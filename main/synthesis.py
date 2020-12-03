import argparse
import logging
import subprocess
from pathlib import Path
from typing import List, Dict, Tuple, Set, Union, Optional, NamedTuple
from enum import Enum, auto
import re
import json
import os
from collections import namedtuple

import pysmt.fnode
from pysmt.solvers.solver import Model
from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import is_sat, is_unsat, get_model, Symbol, BV, Equals, EqualsOrIff, And, Or, TRUE, FALSE, Select, BVConcat, SBV
import pysmt.environment
from pysmt.walkers import DagWalker, IdentityDagWalker
from pysmt.environment import get_env
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter
from pysmt.typing import BOOL, BV32, BV8, ArrayType
import pysmt.operators as op

from funcy import all_fn, any_fn, complement
import multiprocessing as mp
from threading import Lock
from main import values
logger = logging.getLogger(__name__)
Formula = Union[pysmt.fnode.FNode]

pool = mp.Pool(mp.cpu_count())
synthesis_result_list = []
tautology_included = False
contradiction_included = False
found_one = False
patch_list = []

tautology_lock = Lock()
contradiction_lock = Lock()
patch_list_lock = Lock()

def is_tautology_included():
    global tautology_included
    tautology_lock.acquire()
    res = tautology_included
    tautology_lock.release()
    return res


def is_contradiction_included():
    global contradiction_included
    contradiction_lock.acquire()
    res = contradiction_included
    contradiction_lock.release()
    return res


def is_tautology_and_contradiction_included():
    global tautology_included, contradiction_included
    tautology_lock.acquire()
    contradiction_lock.acquire()
    res = tautology_included and contradiction_included
    contradiction_lock.release()
    tautology_lock.release()
    return res


def update_tautology_included():
    global tautology_included
    res = False
    tautology_lock.acquire()
    if not tautology_included:
        tautology_included = True
        res = True
    tautology_lock.release()
    return res


def update_contradiction_included():
    global contradiction_included
    res = False
    contradiction_lock.acquire()
    if not contradiction_included:
        contradiction_included = True
        res = True
    contradiction_lock.release()
    return res


def atomic_patchlist_append(item):
    global patch_list
    patch_list_lock.acquire()
    patch_list.append(item)
    res = len(patch_list) - 1
    patch_list_lock.release()
    return res


def collect_symbols(formula, predicate):

    class SymbolCollector(DagWalker):
        def __init__(self):
            DagWalker.__init__(self, env=get_env(), invalidate_memoization=True)
            self.symbols = set()
            self.functions = {}
            for o in op.all_types():
                if o == op.SYMBOL:
                    self.functions[o] = self.walk_symbol
                else:
                    self.functions[o] = self.walk_none

        def _get_key(self, formula, **kwargs):
            return formula

        def walk_symbol(self, formula, args, **kwargs):
            pred = kwargs['pred']
            if pred(formula):
                self.symbols.add(formula)

    collector = SymbolCollector()
    collector.walk(formula, pred=predicate)
    return collector.symbols


def dump(formula, file):
    with open(file, "w") as f:
        p = SmtPrinter(f)
        p.printer(formula)


# Variables may have the following instances:
class Instance(Enum):
    EXECUTION = auto()  # parameterized by index of execution along given path
    TEST      = auto()  # parameterized by test id
    LOCATION  = auto()  # parameterized by location id
    PATH      = auto()  # parameterized by path id
    COMPONENT = auto()  # parameterized by component id
    NODE      = auto()  # parameterized by encoding node index

    @staticmethod
    def of_symbol(symbol: Formula, parameter: Union[int, str], inst) -> Formula:
        prefix = { Instance.EXECUTION: f"exe:{parameter}!",
                   Instance.TEST:      f"test:{parameter}!",
                   Instance.LOCATION:  f"loc:{parameter}!",
                   Instance.PATH:      f"path:{parameter}!",
                   Instance.COMPONENT: f"comp:{parameter}!",
                   Instance.NODE:      f"node:{parameter}!" }
        return Symbol(prefix[inst] + symbol.symbol_name(), symbol.symbol_type())

    @staticmethod
    def of_formula(formula: Formula, parameter: Union[int, str], inst, predicate) -> Formula:
        return formula.substitute({
            s: Instance.of_symbol(s, parameter, inst) for s in collect_symbols(formula, predicate)
            })

    @staticmethod
    def _regex(s):
        return {
            Instance.EXECUTION: re.compile(r'exe:(\d+)!'),
            Instance.TEST:      re.compile(r'test:(\w+)!'),
            Instance.LOCATION:  re.compile(r'loc:(\w+)!'),
            Instance.PATH:      re.compile(r'path:(\w+)!'),
            Instance.COMPONENT: re.compile(r'comp:(\w+)!'),
            Instance.NODE:      re.compile(r'node:(\d+)!')
        }[s]

    @staticmethod
    def check(symbol: Formula) -> Set['Instance']:
        result = set()
        for i in Instance:
            if Instance._regex(i).search(symbol.symbol_name()):
                result.add(i)
        return result

    @staticmethod
    def parameter(symbol: Formula, inst) -> Union[int, str]:
        par = Instance._regex(inst).search(symbol.symbol_name()).group(0)
        if inst == Instance.EXECUTION or inst == Instance.NODE:
            return int(par)
        else:
            return par


# Component is a pair of component id and component semantics expressed as
# formula over symbols representing program variables, holes, constants and return values
# There are some restriction for components:
#   - all lvalues should be defined in terms of rvalues for all inputs
Component = Tuple[str, Formula]


class TridentType(Enum):
    I32 = auto()   # signed integer
    BOOL = auto()  # boolean

    def __str__(self):
        return {
            TridentType.BOOL: "bool",
            TridentType.I32:  "i32"
        }[self]

    @staticmethod
    def parse(s):
        return {
            "bool": TridentType.BOOL,
            "i32":  TridentType.I32
        }[s]


class SymbolData(NamedTuple):
    lid: Optional[str] = None
    eid: Optional[int] = None
    name: Optional[str] = None
    type: Optional[TridentType] = None


class ComponentSymbol(Enum):
    CONST   = auto()  # constant
    RRETURN = auto()  # rvalue output
    LRETURN = auto()  # lvalue output
    RBRANCH = auto()  # rvalue of branch
    LBRANCH = auto()  # lvalue of branch
    RVALUE  = auto()  # rvalue of variable
    LVALUE  = auto()  # lvalue of variable
    RHOLE   = auto()  # rvalue of subexpression
    LHOLE   = auto()  # lvalue of subexpression

    @staticmethod
    def _regex(s):
        return {
            ComponentSymbol.CONST:   re.compile(r'const_(\w+)$'),
            ComponentSymbol.RRETURN: re.compile(r'(rreturn)$'),
            ComponentSymbol.LRETURN: re.compile(r'(lreturn)$'),
            ComponentSymbol.RBRANCH: re.compile(r'(rbranch)$'),
            ComponentSymbol.LBRANCH: re.compile(r'(lbranch)$'),
            ComponentSymbol.RVALUE:  re.compile(r'rvalue_(\w+)$'),
            ComponentSymbol.LVALUE:  re.compile(r'lvalue_(\w+)$'),
            ComponentSymbol.RHOLE:   re.compile(r'rhole_(\w+)$'),
            ComponentSymbol.LHOLE:   re.compile(r'lhole_(\w+)$')
        }[s]

    @staticmethod
    def check(symbol: Formula) -> Optional['ComponentSymbol']:
        for s in ComponentSymbol:
            if ComponentSymbol._regex(s).search(symbol.symbol_name()):
                return s
        return None

    is_const      = lambda s: ComponentSymbol.check(s) == ComponentSymbol.CONST
    is_rvalue     = lambda s: ComponentSymbol.check(s) == ComponentSymbol.RVALUE
    is_lvalue     = lambda s: ComponentSymbol.check(s) == ComponentSymbol.LVALUE
    is_rhole      = lambda s: ComponentSymbol.check(s) == ComponentSymbol.RHOLE
    is_lhole      = lambda s: ComponentSymbol.check(s) == ComponentSymbol.LHOLE
    is_rreturn    = lambda s: ComponentSymbol.check(s) == ComponentSymbol.RRETURN
    is_lreturn    = lambda s: ComponentSymbol.check(s) == ComponentSymbol.LRETURN
    is_rbranch    = lambda s: ComponentSymbol.check(s) == ComponentSymbol.RBRANCH
    is_lbranch    = lambda s: ComponentSymbol.check(s) == ComponentSymbol.LBRANCH
    is_special    = lambda s: ComponentSymbol.check(s) != None
    is_nonspecial = lambda s: ComponentSymbol.check(s) == None

    @staticmethod
    def parse(symbol: Formula) -> SymbolData:
        s = ComponentSymbol.check(symbol)
        n = ComponentSymbol._regex(s).search(symbol.symbol_name()).group(1)
        if symbol.symbol_type() == BOOL:
            return SymbolData(type=TridentType.BOOL, name=n)
        elif symbol.symbol_type() == BV32:
            return SymbolData(type=TridentType.I32, name=n)
        raise ValueError(f"unsupported symbol type {symbol.symbol_type}")

    @staticmethod
    def const(name) -> Formula:
        #TODO: support bool type?
        return Symbol(f"const_{name}", BV32)

    @staticmethod
    def branch_of(s: Formula) -> Formula:
        return Symbol(re.sub(r'return$', 'branch', s.symbol_name()), s.symbol_type())

class ComponentSemantics:
    @staticmethod
    def get_rreturn(formula):
        rreturns = list(collect_symbols(formula, ComponentSymbol.is_rreturn))
        return rreturns[0] if rreturns else None

    @staticmethod
    def get_lreturn(formula):
        lreturns = list(collect_symbols(formula, ComponentSymbol.is_lreturn))
        return lreturns[0] if lreturns else None

    @staticmethod
    def get_rhole(formula, name):
        rholes = list(collect_symbols(formula, all_fn(ComponentSymbol.is_rhole, lambda x: ComponentSymbol.parse(x).name == name)))
        return rholes[0] if rholes else None

    @staticmethod
    def get_lhole(formula, name):
        lholes = list(collect_symbols(formula, all_fn(ComponentSymbol.is_lhole, lambda x: ComponentSymbol.parse(x).name == name)))
        return lholes[0] if lholes else None


# Program is a pair of
# - a tree of components
# - a valuation of parameters (constants)
# A tree of components is represented as pair of
# - a root component
# - a mapping from hole ids to subprograms
# There are some restrictions on the structure of programs:
# - program cannot assign the same lvalue twice
ComponentTree = Tuple[Component, Dict[str, 'ComponentTree']]
Program = Tuple[ComponentTree, Dict[str, int]]


def program_to_formula(program: Program) -> Formula:
    (tree, constants) = program

    def tree_to_formula(tree, node_counter):
        nid = node_counter[0]
        node_counter[0] += 1
        ((cid, root), children) = tree
        branch_substitution = {}
        rreturn = ComponentSemantics.get_rreturn(root)
        root_rbranch = None
        if rreturn:
            root_rbranch = Instance.of_symbol(ComponentSymbol.branch_of(rreturn), nid, Instance.NODE)
            branch_substitution[rreturn] = root_rbranch
        lreturn = ComponentSemantics.get_lreturn(root)
        root_lbranch = None
        if lreturn:
            root_lbranch = Instance.of_symbol(ComponentSymbol.branch_of(lreturn), nid, Instance.NODE)
            branch_substitution[lreturn] = root_lbranch
        branch_root = root.substitute(branch_substitution)
        is_return = any_fn(ComponentSymbol.is_rreturn, ComponentSymbol.is_lreturn)
        # Keeping constants and variables because they are global; holes because they are replaced with children
        instantiated_root = Instance.of_formula(branch_root, nid, Instance.NODE, is_return)
        hole_substitution = {}
        children_semantics = TRUE()
        for hole_id, subtree in children.items():
            (subtree_semantics, subtree_rbranch, subtree_lbranch) = tree_to_formula(subtree, node_counter)
            if subtree_rbranch:
                rhole = ComponentSemantics.get_rhole(root, hole_id)
                if rhole:
                    hole_substitution[rhole] = subtree_rbranch
            if subtree_lbranch:
                lhole = ComponentSemantics.get_lhole(root, hole_id)
                if lhole:
                    hole_substitution[lhole] = subtree_lbranch
            children_semantics = And(children_semantics, subtree_semantics)
        bound_root = instantiated_root.substitute(hole_substitution)
        result = And(bound_root, children_semantics) if children else bound_root
        return (result, root_rbranch, root_lbranch)

    (semantics, rbranch, _) = tree_to_formula(tree, [0])
    rreturn = ComponentSemantics.get_rreturn(tree[0][1])
    if rreturn:
        semantics = And(semantics, EqualsOrIff(rreturn, rbranch))
    const_substitution = { ComponentSymbol.const(k): SBV(v, 32) for k, v in constants.items() }
    return semantics.substitute(const_substitution)


def program_to_code(program: Program) -> str:
    (tree, constants) = program

    unary_operators = {
        'post-increment': '++',
        'post-decrement': '--',
        'minus': '-',
        'logical-not': '!'
    }
    binary_operators = {
        'assignment': '=',
        'addition': '+',
        'subtraction': '-',
        'multiplication': '*',
        'division': '/',
        'remainder': '%',
        'equal': '==',
        'not-equal': '!=',
        'less-than': '<',
        'less-or-equal': '<=',
        'greater-than': '>',
        'greater-or-equal': '>=',
        'logical-and': '&&',
        'logical-or': '||',
        'sequence': ';'
    }

    def tree_to_code(tree):
        ((cid, semantics), children) = tree
        m = re.search(r'constant_(\w+)', cid)
        if m and m.group(1) in constants:
            return str(constants[m.group(1)])
        elif not children:
            return cid
        else:
            if set(children.keys()) == set(['left', 'right']) and cid in binary_operators.keys():
                return f"({tree_to_code(children['left'])} {binary_operators[cid]} {tree_to_code(children['right'])})"
            elif set(children.keys()) == set(['argument']) and cid in unary_operators.keys():
                if cid in set(['post-increment', 'post-decrement']):
                    return f"{tree_to_code(children['argument'])}{unary_operators[cid]}"
                else:
                    return f"{unary_operators[cid]}{tree_to_code(children['argument'])}"
            elif set(children.keys()) == set(['condition', 'left', 'right']) and cid == 'guarded_assignment':
                return f"if ({tree_to_code(children['condition'])}) {tree_to_code(children['left'])} = {tree_to_code(children['right'])}"
            else:
                return f"{cid}(...)"  #TODO: print arguments

    return tree_to_code(tree)


def program_to_json(program: Program):
    (tree, constants) = program

    def tree_to_json(tree):
        ((cid, semantics), children) = tree
        json_tree = { "node": cid }
        for k, v in children.items():
            symbols = collect_symbols(semantics, lambda s: ComponentSymbol.parse(s).name == k)
            if any(any_fn(ComponentSymbol.is_rhole, ComponentSymbol.is_lhole)(s) for s in symbols):
                if "children" not in tree:
                    json_tree["children"] = {}
                json_tree["children"][k] = tree_to_json(v)
        return json_tree

    json_tree = tree_to_json(tree)
    result = { "tree": json_tree, "constants": constants }
    return result


#TODO: validate
def program_of_json(doc, components) -> Program:

    def tree_of_json(tree, components):
        root = dict(components)[tree["node"]]
        children = {}
        if "children" in tree:
            for hole, subprogram in tree["children"].items():
                children[hole] = tree_of_json(subprogram, components)
        return ((tree["node"], root), children)

    tree = tree_of_json(doc["tree"], components)
    constants = doc["constants"] if "constants" in doc else {}
    return (tree, constants)


# Specification is a map:
#   test id -> (list of paths, test assertion)
# Path is a formula over special trident symbols (angelic, environment, output).
# Test assertion is a formula over trident output symbols.
# The semantics of specification is the satisfiability of
#   for all tests. (V paths) ^ test assertion
Specification = Dict[str, Tuple[List[Formula], Formula]]


class RuntimeSymbol(Enum):
    ANGELIC  = auto()
    RVALUE   = auto()
    LVALUE   = auto()
    SELECTOR = auto()
    OUTPUT   = auto()

    def __str__(self):
        return {
            RuntimeSymbol.ANGELIC:  "angelic",
            RuntimeSymbol.RVALUE:   "rvalue",
            RuntimeSymbol.LVALUE:   "lvalue",
            RuntimeSymbol.SELECTOR: "selector",
            RuntimeSymbol.OUTPUT:   "output",
        }[self]

    is_angelic    = lambda s: RuntimeSymbol.check(s) == RuntimeSymbol.ANGELIC
    is_rvalue     = lambda s: RuntimeSymbol.check(s) == RuntimeSymbol.RVALUE
    is_lvalue     = lambda s: RuntimeSymbol.check(s) == RuntimeSymbol.LVALUE
    is_selector   = lambda s: RuntimeSymbol.check(s) == RuntimeSymbol.SELECTOR
    is_output     = lambda s: RuntimeSymbol.check(s) == RuntimeSymbol.OUTPUT
    is_special    = lambda s: RuntimeSymbol.check(s) != None
    is_nonspecial = lambda s: RuntimeSymbol.check(s) == None

    @staticmethod
    def _regex(s):
        return {
            RuntimeSymbol.ANGELIC:  re.compile(r'^choice!angelic!(\w+)!(\w+)!(\d+)$'),
            RuntimeSymbol.RVALUE:   re.compile(r'^choice!rvalue!(\w+)!(\d+)!(\w+)$'),
            RuntimeSymbol.LVALUE:   re.compile(r'^choice!lvalue!(\w+)!(\d+)!(\w+)$'),
            RuntimeSymbol.SELECTOR: re.compile(r'^choice!lvalue!selector!(\w+)$'),
            RuntimeSymbol.OUTPUT:   re.compile(r'^output!(\w+)!(\w+)!(\d+)$')
        }[s]

    @staticmethod
    def check(symbol: Formula) -> Optional['RuntimeSymbol']:
        for s in RuntimeSymbol:
            if RuntimeSymbol._regex(s).search(symbol.symbol_name()):
                return s
        return None

    @staticmethod
    def parse(symbol: Formula) -> SymbolData:
        kind = RuntimeSymbol.check(symbol)
        if kind == None:
            raise ValueError(f"not a valid trident symbol: {symbol}")
        m = re.search(RuntimeSymbol._regex(kind), symbol.symbol_name())
        if kind == RuntimeSymbol.ANGELIC:
            return SymbolData(type=TridentType.parse(m.group(1)), lid=m.group(2), eid=int(m.group(3)))
        elif kind == RuntimeSymbol.RVALUE or kind == RuntimeSymbol.LVALUE:
            return SymbolData(lid=m.group(1), eid=int(m.group(2)), name=m.group(3))
        elif kind == RuntimeSymbol.SELECTOR:
            return SymbolData(lid=m.group(1))
        elif kind == RuntimeSymbol.OUTPUT:
            return SymbolData(type=TridentType.parse(m.group(1)), name=m.group(2), eid=int(m.group(3)))
        else:
            logger.error(f"unsupported trident symbol kind {kind}")
            exit(1)

    @staticmethod
    def output(d: SymbolData) -> Formula:
        assert d.type == TridentType.I32  #TODO: support boolean?
        array = Symbol(f"output!{d.type}!{d.name}!{d.eid}", Klee.memory_type)
        return Klee.interpret_memory(array, d.type)

    @staticmethod
    def angelic(d: SymbolData) -> Formula:
        array = Symbol(f"choice!angelic!{d.type}!{d.lid}!{d.eid}", Klee.memory_type)
        return Klee.interpret_memory(array, d.type)

    @staticmethod
    def rvalue(d: SymbolData) -> Formula:
        array = Symbol(f"choice!rvalue!{d.lid}!{d.eid}!{d.name}", Klee.memory_type)
        return Klee.interpret_memory(array, d.type)

    @staticmethod
    def lvalue(d: SymbolData) -> Formula:
        array = Symbol(f"choice!lvalue!{d.lid}!{d.eid}!{d.name}", Klee.memory_type)
        return Klee.interpret_memory(array, d.type)


class Klee:
    memory_type = ArrayType(BV32, BV8)

    @staticmethod
    def interpret_memory(array: Formula, type: TridentType) -> Formula:
        concat = BVConcat(Select(array, BV(3, 32)),
                 BVConcat(Select(array, BV(2, 32)),
                 BVConcat(Select(array, BV(1, 32)), Select(array, BV(0, 32)))))
        if type == TridentType.I32:
            return concat
        elif type == TridentType.BOOL:
            return concat.NotEquals(BV(0, 32))
        raise ValueError(f"unsupported type {type}")

    @staticmethod
    def load(tid: str, assertion: Formula, klee_dir: Path) -> Specification:
        """Load specification for test from KLEE output directory.
        Test-instantiate and path-instantiate all non-special symbols.
        TODO: Ignore paths where only a subset of output variables from assertion is defined.
        TODO: Ignore paths where only a subset of environment variables for a reachable location is defined."""
        smt2s = klee_dir.glob('*.smt2')
        path_formulas = []
        for pathfile in smt2s:
            pid = pathfile.stem
            with pathfile.open() as f:
                pysmt.environment.push_env()
                parser = SmtLibParser()
                script = parser.get_script(f)
                path_formula = script.get_last_formula()
                test_instantiated = Instance.of_formula(path_formula, tid, Instance.TEST, RuntimeSymbol.is_nonspecial)
                path_instantiated = Instance.of_formula(test_instantiated, pid, Instance.PATH, RuntimeSymbol.is_nonspecial)
                pysmt.environment.pop_env()
                normalized = pysmt.environment.get_env().formula_manager.normalize(path_instantiated)
                path_formulas.append(normalized)
        return { tid: (path_formulas, assertion) }


def parse_assertion_symbol(symbol: Formula) -> SymbolData:
    # assertion_symbol_regexp = re.compile(r'^(\w+)!(\d+)$')
    # m = re.search(assertion_symbol_regexp, symbol.symbol_name())
    # # TODO: support bool type?
    # return SymbolData(type=TridentType.I32, name=m.group(1), eid=int(m.group(2)))
    symbol_name, symbol_eid = str(symbol).split("!")
    return SymbolData(type=TridentType.I32, name=symbol_name, eid=int(symbol_eid))


# Returns mapping from lids (location IDs) to corresponding type
def extract_lids(path: Formula) -> Dict[str, TridentType]:
    """Extracting lids by checking angelic and lvalue symbols."""
    angelic_symbols = collect_symbols(path, RuntimeSymbol.is_angelic)
    lids = { RuntimeSymbol.parse(s).lid:RuntimeSymbol.parse(s).type for s in angelic_symbols }
    #NB: angelic symbols might be removed by KLEE when they are not used, so check lvalues:
    lvalue_symbols = collect_symbols(path, RuntimeSymbol.is_lvalue)
    lids.update({ RuntimeSymbol.parse(s).lid:TridentType.I32 for s in lvalue_symbols
                  if RuntimeSymbol.parse(s).lid not in lids })
    return lids


def extract_eids(path: Formula, lid: str) -> Set[str]:
    """Extracting exe ids for given lid by checking angelic and lvalue symbols."""
    symbols = collect_symbols(path, any_fn(RuntimeSymbol.is_angelic, RuntimeSymbol.is_lvalue))
    return set(RuntimeSymbol.parse(s).eid for s in symbols if RuntimeSymbol.parse(s).lid == lid)


# assignment of free variables that satisfy specification
VerificationSuccess = namedtuple('VerificationSuccess', ['constants'])


def verify(programs: Union[Dict[str, Program], Dict[str, Formula]],
           specification: Specification) -> Optional[VerificationSuccess]:
    """Check if programs satisfy specification
    """
    vc = TRUE()

    program_semantics = { lid:(program if isinstance(program, Formula) else program_to_formula(program))
                          for (lid, program) in programs.items() }
    free_variables = [v for p in program_semantics.values() for v in collect_symbols(p, ComponentSymbol.is_const)]

    for tid in specification.keys():
        test_vc = FALSE()

        (paths, assertion) = specification[tid]

        for path in paths:
            lids = extract_lids(path).keys()
            if not lids:
                continue
            assert len(lids) == 1
            lid = list(lids)[0]
            eids = extract_eids(path, lid)

            assert eids == set(range(len(eids)))
            path_vc = path

            program = program_semantics[lid]

            for eid in eids:
                program_substitution = {}
                for program_symbol in collect_symbols(program, lambda x: True):
                    kind = ComponentSymbol.check(program_symbol)
                    data = ComponentSymbol.parse(program_symbol)._replace(lid=lid)._replace(eid=eid)
                    if kind == ComponentSymbol.RRETURN:
                        program_substitution[program_symbol] = RuntimeSymbol.angelic(data)
                    elif kind == ComponentSymbol.RVALUE:
                        program_substitution[program_symbol] = RuntimeSymbol.rvalue(data)
                    elif kind == ComponentSymbol.LVALUE:
                        program_substitution[program_symbol] = RuntimeSymbol.lvalue(data)
                    else:
                        pass #FIXME: do I need to handle it somehow?
                bound_program = program.substitute(program_substitution)
                is_branch = any_fn(ComponentSymbol.is_rbranch, ComponentSymbol.is_lbranch)
                exe_inst_program = Instance.of_formula(bound_program, eid, Instance.EXECUTION, is_branch)
                path_vc = And(path_vc, exe_inst_program)

            test_vc = Or(test_vc, path_vc)

        assertion_substitution = {}
        for assertion_symbol in collect_symbols(assertion, lambda x: True):
            symbol_data = parse_assertion_symbol(assertion_symbol)
            assertion_substitution[assertion_symbol] = RuntimeSymbol.output(symbol_data)
        bound_assertion = assertion.substitute(assertion_substitution)
        test_vc = And(test_vc, bound_assertion)
        is_special_nonconst = any_fn(RuntimeSymbol.is_special, all_fn(ComponentSymbol.is_special, complement(ComponentSymbol.is_const)))
        instantiated_test_vc = Instance.of_formula(test_vc, tid, Instance.TEST, is_special_nonconst)

        vc = And(vc, instantiated_test_vc)

        # print(get_model(vc))
        # dump(vc, "vc.smt2")

    model = get_model(vc)
    if model is None:
        return None
    else:
        return VerificationSuccess({v:model[v].bv_signed_value() for v in free_variables})


def verify_parallel(programs: Union[Dict[str, Program], Dict[str, Formula]],
           specification: Specification):
    """Check if programs satisfy specification
    """
    vc = TRUE()

    program_semantics = { lid:(program if isinstance(program, Formula) else program_to_formula(program))
                          for (lid, program) in programs.items() }
    #free_variables = [v for p in program_semantics.values() for v in collect_symbols(p, ComponentSymbol.is_const)]

    for tid in specification.keys():
        test_vc = FALSE()

        (paths, assertion) = specification[tid]

        for path in paths:
            lids = extract_lids(path).keys()
            if not lids:
                continue
            assert len(lids) == 1
            lid = list(lids)[0]
            eids = extract_eids(path, lid)

            assert eids == set(range(len(eids)))
            path_vc = path

            program = program_semantics[lid]

            for eid in eids:
                program_substitution = {}
                for program_symbol in collect_symbols(program, lambda x: True):
                    kind = ComponentSymbol.check(program_symbol)
                    data = ComponentSymbol.parse(program_symbol)._replace(lid=lid)._replace(eid=eid)
                    if kind == ComponentSymbol.RRETURN:
                        program_substitution[program_symbol] = RuntimeSymbol.angelic(data)
                    elif kind == ComponentSymbol.RVALUE:
                        program_substitution[program_symbol] = RuntimeSymbol.rvalue(data)
                    elif kind == ComponentSymbol.LVALUE:
                        program_substitution[program_symbol] = RuntimeSymbol.lvalue(data)
                    else:
                        pass #FIXME: do I need to handle it somehow?
                bound_program = program.substitute(program_substitution)
                is_branch = any_fn(ComponentSymbol.is_rbranch, ComponentSymbol.is_lbranch)
                exe_inst_program = Instance.of_formula(bound_program, eid, Instance.EXECUTION, is_branch)
                path_vc = And(path_vc, exe_inst_program)

            test_vc = Or(test_vc, path_vc)

        assertion_substitution = {}
        for assertion_symbol in collect_symbols(assertion, lambda x: True):
            symbol_data = parse_assertion_symbol(assertion_symbol)
            assertion_substitution[assertion_symbol] = RuntimeSymbol.output(symbol_data)
        bound_assertion = assertion.substitute(assertion_substitution)
        test_vc = And(test_vc, bound_assertion)
        is_special_nonconst = any_fn(RuntimeSymbol.is_special, all_fn(ComponentSymbol.is_special, complement(ComponentSymbol.is_const)))
        instantiated_test_vc = Instance.of_formula(test_vc, tid, Instance.TEST, is_special_nonconst)

        vc = And(vc, instantiated_test_vc)

        # print(get_model(vc))
        # dump(vc, "vc.smt2")
    return vc


# Enumerating components trees
def enumerate_trees(components: List[Component],
                    depth: int,
                    typ: TridentType,
                    need_lreturn: bool,
                    need_rreturn: bool):

    # Contains all components, which match the return types if necessary.                 
    roots = [c for c in components
             if (not need_lreturn \
                   or (ComponentSemantics.get_lreturn(c[1]) \
                     and ComponentSymbol.parse(ComponentSemantics.get_lreturn(c[1])).type == typ)) \
                and (not need_rreturn \
                   or (ComponentSemantics.get_rreturn(c[1]) \
                     and ComponentSymbol.parse(ComponentSemantics.get_rreturn(c[1])).type == typ))]

    def enumerate_mappings(names, mapping_params, drop):
        name, *remaining = names
        depth, typ, commutative, need_lreturn, need_rreturn = mapping_params[name]
        subtrees = enumerate_trees(components, depth, typ, need_lreturn, need_rreturn)
        for _ in range(0, drop):
            next(subtrees)
        for (i, substitution) in enumerate(subtrees):
            if remaining:
                next_drop = drop + i if commutative else drop
                for partial_mapping in enumerate_mappings(remaining, mapping_params, next_drop):
                    if set(partial_mapping.keys()) != set(remaining):
                        yield from ()
                    mapping = {name:substitution}
                    mapping.update(partial_mapping)
                    yield mapping
            else:
                yield {name:substitution}

    for root in roots:
        holes = collect_symbols(root[1], any_fn(ComponentSymbol.is_lhole, ComponentSymbol.is_rhole))
        if not holes:
            yield (root, {})
        if holes and (depth > 1):
            names = list(set(ComponentSymbol.parse(h).name for h in holes))
            commutative = (root[0] in ['addition', 'multiplication',
                                       'equal', 'not-equal',
                                       'logical-and', 'logical-or'])
            mapping_params = {}
            for name in names:
                lhole = ComponentSemantics.get_lhole(root[1], name)
                rhole = ComponentSemantics.get_rhole(root[1], name)
                typ = ComponentSymbol.parse(lhole).type if lhole else ComponentSymbol.parse(rhole).type
                mapping_params[name] = (depth-1, typ, commutative, lhole, rhole)
            for mapping in enumerate_mappings(names, mapping_params, 0):
                yield (root, mapping)


def extract_assigned(tree: ComponentTree) -> List[Component]:
    (root, mapping) = tree
    assigned_names = (name for name in mapping.keys() if ComponentSemantics.get_lhole(root[1], name))
    assigned_trees = list(mapping[name][0] for name in assigned_names)
    for subtree in mapping.values():
        assigned_trees += extract_assigned(subtree)
    return assigned_trees


def collect_synthesis_result(synthesis_result):
    global collected_patch_indeces, pool
    collected_patch_indeces.append(synthesis_result)


def collect_one(synthesis_result):
    global collected_patch_indeces, pool, found_one
    collected_patch_indeces.append(synthesis_result)
    if synthesis_result[0] is True:
        pool.terminate()
        found_one = True



def collect_tautology_result(synthesis_result):
    global collected_patch_indeces
    new_tautology_included = update_tautology_included()
    if new_tautology_included:
        collected_patch_indeces.append(synthesis_result)


def collect_contradiction_result(synthesis_result):
    global collected_patch_indeces
    new_contradiction_included = update_contradiction_included()
    if new_contradiction_included:
        collected_patch_indeces.append(synthesis_result)

def check_sat(vc, index):
    if is_sat(vc):
        return True, index
    else:
        return False, index


# TODO: enforce assigned variables in verification conditon
# TODO: check hole types
def synthesize_one_parallel(components: List[Component],
                        depth: int,
                        specification: Specification,
                        # Optional arguments for concrete patch enumeration
                        concrete_enumeration=False,
                        lower_bound=-10,
                        upper_bound=+10) -> Optional[Dict[str, Program]]:
    lids = {}
    for (tid, (paths, _)) in specification.items():
        for path in paths:
            lids.update(extract_lids(path))
    logger.info(f"locations extracted from klee paths: {list(lids.keys())}")

    assert len(lids) == 1
    (lid, typ) = list(lids.items())[0]

    optimized = True

    ## Variables for parallel execution.
    global tautology_included, contradiction_included, collected_patch_indeces, patch_list, pool, found_one
    tautology_included = not values.IS_TAUTOLOGIES_INCLUDED
    contradiction_included = not values.IS_CONTRADICTIONS_INCLUDED
    patch_list = []
    collected_patch_indeces = []

    ## Open new pool for parallel execution.
    pool = mp.Pool(mp.cpu_count())

    for tree in enumerate_trees(components, depth, typ, False, True):
        assigned = extract_assigned(tree)
        if len(assigned) != len(set(assigned)):
            continue

        if optimized:
            ## Check for tautologies (TRUE) and contradictions (FALSE).
            # 1. Check for x == x, x<=x, x>=x
            component_type = tree[0][0]
            left = None
            if "left" in tree[1]:
                left = tree[1]['left']
            right = None
            if "right" in tree[1]:
                right = tree[1]['right']
            if component_type in ['equal', 'less-or-equal', 'greater-or-equal']:
                if left and right:
                    if left == right:
                        ## Tautology detected. Only use this patch if it is the first tautology in the set.
                        new_tautology_detected = update_tautology_included()
                        if not new_tautology_detected:
                            continue
            # 2. Check for x != x, x < x, x > x
            elif component_type in ['not-equal', 'less-than', 'greater-than']:
                if left and right:
                    if left == right:
                        ## Contradiction detected. Only use this patch if it is the first contradiction in the set.
                        new_contradiction_included = update_contradiction_included()
                        if not new_contradiction_included:
                            continue

        ## Enumerate concrete values for constants if demanded AND if possible (i.e., if there is any constant).
        if concrete_enumeration and (contains_constant(tree[1]) or not optimized):
            names = get_all_constant_names(tree[1])
            if optimized and contains_only_constants(tree[1]):
                if is_tautology_and_contradiction_included():
                    continue
                else:
                    ## Determine whether the patch is always tautology or always contradiction.
                    patch_constraint = extract_constraints_from_patch({lid: (tree, {})})
                    can_be_true = is_sat(patch_constraint)
                    can_be_false = is_unsat(patch_constraint)
                    is_always_tautology = can_be_true and not can_be_false
                    is_always_contradiction = not can_be_true and can_be_false

                    if not is_tautology_included():
                        if is_always_tautology:
                            ## If tautology is new and patch is tautology, then pick any number for constant values.
                            const_dict = {}
                            for const_name in names:
                                const_dict[const_name] = 1
                            patch = {lid: (tree, const_dict)}
                            index = atomic_patchlist_append(patch)
                            vc = verify_parallel(patch, specification)
                            pool.apply_async(check_sat, args=(vc, index), callback=collect_tautology_result)
                            continue
                        else:
                            ## If tautology is new and patch can be true, then pick constant values specifically.
                            # Check with specification for tautology, and hence, get one of the values from the model.
                            model = get_model(patch_constraint)
                            const_dict = {}
                            for const_name in names:
                                sym_def = Symbol("const_" + str(const_name), BV32)
                                if sym_def not in model:
                                    continue
                                value_sym = model[sym_def].simplify()
                                const_dict[const_name] = int(str(value_sym).split("_")[0])
                            patch = {lid: (tree, const_dict)}
                            index = atomic_patchlist_append(patch)
                            vc = verify_parallel(patch, specification)
                            pool.apply_async(check_sat, args=(vc, index), callback=collect_tautology_result)
                            continue

                    if not is_contradiction_included():
                        if is_always_contradiction:
                            ## If contradiction is new and patch is contradiction, then pick any number for constant values.
                            const_dict = {}
                            for const_name in names:
                                const_dict[const_name] = 1
                            patch = {lid: (tree, const_dict)}
                            index = atomic_patchlist_append(patch)
                            vc = verify_parallel(patch, specification)
                            pool.apply_async(check_sat, args=(vc, index), callback=collect_contradiction_result)
                            continue
                        else:
                            ## If contradiction is new and patch can be false, then pick constant values specifically.
                            # Check with specification for contradiction, and hence, get one of the values from the model.
                            model = get_model(patch_constraint)
                            const_dict = {}
                            for const_name in names:
                                sym_def = Symbol("const_" + str(const_name), BV32)
                                if sym_def not in model:
                                    continue
                                value_sym = model[sym_def].simplify()
                                const_dict[const_name] = int(str(value_sym).split("_")[0])
                            patch = {lid: (tree, const_dict)}
                            index = atomic_patchlist_append(patch)
                            vc = verify_parallel(patch, specification)
                            pool.apply_async(check_sat, args=(vc, index), callback=collect_contradiction_result)
                            continue

            # There is at least one variable and one constant, then iterate over possible constant values and verify the concrete patch.
            else:  # TODO explore neighborhood of existing value for constants
                if not optimized and len(names) == 0:  # TODO remove len=0, just for testing
                    for value_a in range(lower_bound, upper_bound):
                        if found_one:
                            break
                        patch = {lid: (tree, {'a': value_a})}
                        index = atomic_patchlist_append(patch)
                        vc = verify_parallel(patch, specification)
                        try:
                            pool.apply_async(check_sat, args=(vc, index), callback=collect_one)
                        except ValueError:
                            break
                elif len(names) == 1:
                    const_a_str = names.pop()
                    for value_a in range(lower_bound, upper_bound):
                        if found_one:
                            break
                        patch = {lid: (tree, {const_a_str: value_a})}
                        index = atomic_patchlist_append(patch)
                        vc = verify_parallel(patch, specification)
                        try:
                            pool.apply_async(check_sat, args=(vc, index), callback=collect_one)
                        except ValueError:
                            break
                elif len(names) == 2:
                    const_a_str = names.pop()
                    const_b_str = names.pop()
                    for value_a in range(lower_bound, upper_bound):
                        if found_one:
                            break
                        for value_b in range(lower_bound, upper_bound):
                            patch = {lid: (tree, {const_a_str: value_a, const_b_str: value_b})}
                            index = atomic_patchlist_append(patch)
                            vc = verify_parallel(patch, specification)
                            try:
                                pool.apply_async(check_sat, args=(vc, index), callback=collect_one)
                            except ValueError:
                                break
                elif len(names) == 3:
                    const_a_str = names.pop()
                    const_b_str = names.pop()
                    const_c_str = names.pop()
                    for value_a in range(lower_bound, upper_bound):
                        if found_one:
                            break
                        for value_b in range(lower_bound, upper_bound):
                            if found_one:
                                break
                            for value_c in range(lower_bound, upper_bound):
                                patch = {
                                    lid: (tree, {const_a_str: value_a, const_b_str: value_b, const_c_str: value_c})}
                                index = atomic_patchlist_append(patch)
                                vc = verify_parallel(patch, specification)
                                try:
                                    pool.apply_async(check_sat, args=(vc, index), callback=collect_one)
                                except ValueError:
                                    break
                elif len(names) == 4:
                    const_a_str = names.pop()
                    const_b_str = names.pop()
                    const_c_str = names.pop()
                    const_d_str = names.pop()
                    for value_a in range(lower_bound, upper_bound):
                        if found_one:
                            break
                        for value_b in range(lower_bound, upper_bound):
                            if found_one:
                                break
                            for value_c in range(lower_bound, upper_bound):
                                if found_one:
                                    break
                                for value_d in range(lower_bound, upper_bound):

                                    patch = {lid: (tree,
                                                   {const_a_str: value_a, const_b_str: value_b, const_c_str: value_c,
                                                    const_d_str: value_d})}
                                    index = atomic_patchlist_append(patch)
                                    vc = verify_parallel(patch, specification)
                                    try:
                                        pool.apply_async(check_sat, args=(vc, index), callback=collect_one)
                                    except ValueError:
                                        break
                else:
                    logger.error("constants=" + str(names))
                    logger.error("More than 4 constants are currently not supported!")
                    exit(1)
        ## Otherwise: verify the patch and report it.
        else:
            patch = {lid: (tree, {})}
            index = atomic_patchlist_append(patch)
            vc = verify_parallel(patch, specification)
            try:
                pool.apply_async(check_sat, args=(vc, index), callback=collect_one)
            except ValueError:
                logger.info("\t\tfound one")

    logger.info("\t\twaiting for thread completion")

    # assert(len(result_list) == len(path_list))

    # print("collected_patch_indeces=" + str(collected_patch_indeces))

    ## Filter feasible patches and return them.
    temp_set = set()
    synthesis_result_list = []
    for result in collected_patch_indeces:
        is_feasible, index = result
        if is_feasible:
            patch = patch_list[index]
            patch_str = str(patch)
            if not patch_str in temp_set:
                temp_set.add(patch_str)
                synthesis_result_list.append(patch)
    return synthesis_result_list



#TODO: enforce assigned variables in verification conditon
#TODO: check hole types
def synthesize_lazy(components: List[Component],
               depth: int,
               specification: Specification,
               # Optional arguments for concrete patch enumeration
               concrete_enumeration = False,
               lower_bound = -10,
               upper_bound = +10) -> Optional[Dict[str, Program]]:
    lids = {}
    for (tid, (paths, _)) in specification.items():
        for path in paths:
            lids.update(extract_lids(path))
    logger.info(f"locations extracted from klee paths: {list(lids.keys())}")

    assert len(lids) == 1
    (lid, typ) = list(lids.items())[0]

    tautology_included = not values.IS_TAUTOLOGIES_INCLUDED
    contradiction_included = not values.IS_CONTRADICTIONS_INCLUDED

    optimized = True

    for tree in enumerate_trees(components, depth, typ, False, True):
        assigned = extract_assigned(tree)
        if len(assigned) != len(set(assigned)):
            continue

        if optimized:
            ## Check for tautologies (TRUE) and contradictions (FALSE).
            # 1. Check for x == x, x<=x, x>=x
            component_type = tree[0][0]
            left = None
            if "left" in tree[1]:
                left = tree[1]['left']

            right = None
            if "right" in tree[1]:
                right = tree[1]['right']

            if component_type in ['equal', 'less-or-equal', 'greater-or-equal']:
                if left and right:
                    if left == right:
                        ## Tautology detected. Only use this patch if it is the first tautology in the set.
                        if tautology_included:
                            continue
                        else:
                            tautology_included = True
            # 2. Check for x != x, x < x, x > x
            elif component_type in ['not-equal', 'less-than', 'greater-than']:
                if left and right:
                    if left == right:
                        ## Contradiction detected. Only use this patch if it is the first contradiction in the set.
                        if contradiction_included:
                            continue
                        else:
                            contradiction_included = True

        ## Enumerate concrete values for constants if demanded AND if possible (i.e., if there is any constant).
        if concrete_enumeration and (contains_constant(tree[1]) or not optimized):
            names = get_all_constant_names(tree[1])
            if optimized and contains_only_constants(tree[1]):
                if tautology_included and contradiction_included:
                    continue
                else:
                    ## Determine whether the patch is always tautology or always contradiction.
                    patch_constraint = extract_constraints_from_patch({lid: (tree, {})})
                    can_be_true = is_sat(patch_constraint)
                    can_be_false = is_unsat(patch_constraint)
                    is_always_tautology = can_be_true and not can_be_false
                    is_always_contradiction = not can_be_true and can_be_false

                    if not tautology_included:
                        if is_always_tautology:
                            ## If tautology is new and patch is tautology, then pick any number for constant values.
                            const_dict = {}
                            for const_name in names:
                                const_dict[const_name] = 1
                            result = verify({lid: (tree, const_dict)}, specification)
                            if result:
                                tautology_included = True
                                yield {lid: (tree, const_dict)}
                        else:
                            ## If tautology is new and patch can be true, then pick constant values specifically.
                            # Check with specification for tautology, and hence, get one of the values from the model.
                            model = get_model(patch_constraint)
                            const_dict = {}
                            for const_name in names:
                                sym_def = Symbol("const_" + str(const_name), BV32)
                                if sym_def not in model:
                                    continue
                                value_sym = model[sym_def].simplify()
                                const_dict[const_name] = int(str(value_sym).split("_")[0])
                            result = verify({lid: (tree, const_dict)}, specification)
                            if result:
                                tautology_included = True
                                yield {lid: (tree, const_dict)}

                    if not contradiction_included:
                        if is_always_contradiction:
                            ## If contradiction is new and patch is contradiction, then pick any number for constant values.
                            const_dict = {}
                            for const_name in names:
                                const_dict[const_name] = 1
                            result = verify({lid: (tree, const_dict)}, specification)
                            if result:
                                contradiction_included = True
                                yield {lid: (tree, const_dict)}
                        else:
                            ## If contradiction is new and patch can be false, then pick constant values specifically.
                            # Check with specification for contradiction, and hence, get one of the values from the model.
                            model = get_model(patch_constraint)
                            const_dict = {}
                            for const_name in names:
                                sym_def = Symbol("const_" + str(const_name), BV32)
                                if sym_def not in model:
                                    continue
                                value_sym = model[sym_def].simplify()
                                const_dict[const_name] = int(str(value_sym).split("_")[0])
                            result = verify({lid: (tree, const_dict)}, specification)
                            if result:
                                tautology_included = True
                                yield {lid: (tree, const_dict)}

            # There is at least one variable and one constant, then iterate over possible constant values and verify the concrete patch.
            else: # TODO explore neighborhood of existing value for constants
                if not optimized and len(names) == 0: # TODO remove len=0, just for testing
                    for value_a in range(lower_bound, upper_bound):
                        result = verify({lid: (tree, {'a': value_a})}, specification)
                        if result:
                            yield {lid: (tree, {'a': value_a})}
                elif len(names) == 1:
                    const_a_str = names.pop()
                    for value_a in range(lower_bound, upper_bound):
                        result = verify({lid: (tree, {const_a_str: value_a})}, specification)
                        if result:
                            yield {lid: (tree, {const_a_str: value_a})}
                elif len(names) == 2:
                    const_a_str = names.pop()
                    const_b_str = names.pop()
                    for value_a in range(lower_bound, upper_bound):
                        for value_b in range(lower_bound, upper_bound):
                            result = verify({lid: (tree, {const_a_str: value_a, const_b_str: value_b})}, specification)
                            if result:
                                yield {lid: (tree, {const_a_str: value_a, const_b_str: value_b})}
                elif len(names) == 3:
                    const_a_str = names.pop()
                    const_b_str = names.pop()
                    const_c_str = names.pop()
                    for value_a in range(lower_bound, upper_bound):
                        for value_b in range(lower_bound, upper_bound):
                            for value_c in range(lower_bound, upper_bound):
                                result = verify({lid: (tree, {const_a_str: value_a, const_b_str: value_b, const_c_str: value_c})}, specification)
                                if result:
                                    yield {lid: (tree, {const_a_str: value_a, const_b_str: value_b, const_c_str: value_c})}
                elif len(names) == 4:
                    const_a_str = names.pop()
                    const_b_str = names.pop()
                    const_c_str = names.pop()
                    const_d_str = names.pop()
                    for value_a in range(lower_bound, upper_bound):
                        for value_b in range(lower_bound, upper_bound):
                            for value_c in range(lower_bound, upper_bound):
                                for value_d in range(lower_bound, upper_bound):
                                    result = verify({lid: (tree, {const_a_str: value_a, const_b_str: value_b, const_c_str: value_c, const_d_str: value_d})}, specification)
                                    if result:
                                        yield {lid: (tree, {const_a_str: value_a, const_b_str: value_b, const_c_str: value_c, const_d_str: value_d})}
                else:
                    logger.error("constants=" + str(names))
                    logger.error("More than 4 constants are currently not supported!")
                    exit(1)
        ## Otherwise: verify the patch and report it.
        else:
            result = verify({lid: (tree, {})}, specification)
            if result:
                yield {lid: (tree, { ComponentSymbol.parse(f).name:v for (f, v) in result.constants.items() })}


#TODO: enforce assigned variables in verification conditon
#TODO: check hole types
def synthesize_parallel(components: List[Component],
               depth: int,
               specification: Specification,
               # Optional arguments for concrete patch enumeration
               concrete_enumeration = False,
               lower_bound = -10,
               upper_bound = +10) -> Optional[Dict[str, Program]]:
    lids = {}
    for (tid, (paths, _)) in specification.items():
        for path in paths:
            lids.update(extract_lids(path))
    logger.info(f"locations extracted from klee paths: {list(lids.keys())}")

    assert len(lids) == 1
    (lid, typ) = list(lids.items())[0]

    optimized = True

    ## Variables for parallel execution.
    global tautology_included, contradiction_included, collected_patch_indeces, patch_list, pool
    tautology_included = not values.IS_TAUTOLOGIES_INCLUDED
    contradiction_included = not values.IS_CONTRADICTIONS_INCLUDED
    patch_list = []
    collected_patch_indeces = []
    
    ## Open new pool for parallel execution.
    pool = mp.Pool(mp.cpu_count())

    for tree in enumerate_trees(components, depth, typ, False, True):
        assigned = extract_assigned(tree)
        if len(assigned) != len(set(assigned)):
            continue

        if optimized:
            ## Check for tautologies (TRUE) and contradictions (FALSE).
            # 1. Check for x == x, x<=x, x>=x
            component_type = tree[0][0]
            left = None
            if "left" in tree[1]:
                left = tree[1]['left']
            right = None
            if "right" in tree[1]:
                right = tree[1]['right']
            if component_type in ['equal', 'less-or-equal', 'greater-or-equal']:
                if left and right:
                    if left == right:
                        ## Tautology detected. Only use this patch if it is the first tautology in the set.  
                        new_tautology_detected = update_tautology_included()
                        if not new_tautology_detected:
                            continue
            # 2. Check for x != x, x < x, x > x
            elif component_type in ['not-equal', 'less-than', 'greater-than']:
                if left and right:
                    if left == right:
                        ## Contradiction detected. Only use this patch if it is the first contradiction in the set.
                        new_contradiction_included = update_contradiction_included()
                        if not new_contradiction_included:
                            continue

        ## Enumerate concrete values for constants if demanded AND if possible (i.e., if there is any constant).
        if concrete_enumeration and (contains_constant(tree[1]) or not optimized):
            names = get_all_constant_names(tree[1])
            if optimized and contains_only_constants(tree[1]):
                if is_tautology_and_contradiction_included():
                    continue
                else:
                    ## Determine whether the patch is always tautology or always contradiction.
                    patch_constraint = extract_constraints_from_patch({lid: (tree, {})})
                    can_be_true = is_sat(patch_constraint)
                    can_be_false = is_unsat(patch_constraint)
                    is_always_tautology = can_be_true and not can_be_false
                    is_always_contradiction = not can_be_true and can_be_false

                    if not is_tautology_included():
                        if is_always_tautology:
                            ## If tautology is new and patch is tautology, then pick any number for constant values.
                            const_dict = {}
                            for const_name in names:
                                const_dict[const_name] = 1
                            patch = {lid: (tree, const_dict)}
                            index = atomic_patchlist_append(patch)
                            vc = verify_parallel(patch, specification)
                            pool.apply_async(check_sat, args=(vc, index), callback=collect_tautology_result)
                            continue
                        else:
                            ## If tautology is new and patch can be true, then pick constant values specifically.
                            # Check with specification for tautology, and hence, get one of the values from the model.
                            model = get_model(patch_constraint)
                            const_dict = {}
                            for const_name in names:
                                sym_def = Symbol("const_" + str(const_name), BV32)
                                if sym_def not in model:
                                    continue
                                value_sym = model[sym_def].simplify()
                                const_dict[const_name] = int(str(value_sym).split("_")[0])
                            patch = {lid: (tree, const_dict)}
                            index = atomic_patchlist_append(patch)
                            vc = verify_parallel(patch, specification)
                            pool.apply_async(check_sat, args=(vc, index), callback=collect_tautology_result)
                            continue

                    if not is_contradiction_included():
                        if is_always_contradiction:
                            ## If contradiction is new and patch is contradiction, then pick any number for constant values.
                            const_dict = {}
                            for const_name in names:
                                const_dict[const_name] = 1
                            patch = {lid: (tree, const_dict)}
                            index = atomic_patchlist_append(patch)
                            vc = verify_parallel(patch, specification)
                            pool.apply_async(check_sat, args=(vc, index), callback=collect_contradiction_result)
                            continue
                        else:
                            ## If contradiction is new and patch can be false, then pick constant values specifically.
                            # Check with specification for contradiction, and hence, get one of the values from the model.
                            model = get_model(patch_constraint)
                            const_dict = {}
                            for const_name in names:
                                sym_def = Symbol("const_" + str(const_name), BV32)
                                if sym_def not in model:
                                    continue
                                value_sym = model[sym_def].simplify()
                                const_dict[const_name] = int(str(value_sym).split("_")[0])
                            patch = {lid: (tree, const_dict)}
                            index = atomic_patchlist_append(patch)
                            vc = verify_parallel(patch, specification)
                            pool.apply_async(check_sat, args=(vc, index), callback=collect_contradiction_result)
                            continue

            # There is at least one variable and one constant, then iterate over possible constant values and verify the concrete patch.
            else: # TODO explore neighborhood of existing value for constants
                if not optimized and len(names) == 0: # TODO remove len=0, just for testing    
                    for value_a in range(lower_bound, upper_bound):
                        patch = {lid: (tree, {'a': value_a})}
                        index = atomic_patchlist_append(patch)
                        vc = verify_parallel(patch, specification)
                        pool.apply_async(check_sat, args=(vc, index), callback=collect_synthesis_result)
                elif len(names) == 1: 
                    const_a_str = names.pop()
                    for value_a in range(lower_bound, upper_bound):
                        patch = {lid: (tree, {const_a_str: value_a})}
                        index = atomic_patchlist_append(patch)
                        vc = verify_parallel(patch, specification)
                        pool.apply_async(check_sat, args=(vc, index), callback=collect_synthesis_result)
                elif len(names) == 2:
                    const_a_str = names.pop()
                    const_b_str = names.pop()
                    for value_a in range(lower_bound, upper_bound):
                        for value_b in range(lower_bound, upper_bound):
                            patch = {lid: (tree, {const_a_str: value_a, const_b_str: value_b})}
                            index = atomic_patchlist_append(patch)
                            vc = verify_parallel(patch, specification)
                            pool.apply_async(check_sat, args=(vc, index), callback=collect_synthesis_result)
                elif len(names) == 3:
                    const_a_str = names.pop()
                    const_b_str = names.pop()
                    const_c_str = names.pop()
                    for value_a in range(lower_bound, upper_bound):
                        for value_b in range(lower_bound, upper_bound):
                            for value_c in range(lower_bound, upper_bound):
                                patch = {lid: (tree, {const_a_str: value_a, const_b_str: value_b, const_c_str: value_c})}
                                index = atomic_patchlist_append(patch)
                                vc = verify_parallel(patch, specification)
                                pool.apply_async(check_sat, args=(vc, index), callback=collect_synthesis_result)
                elif len(names) == 4:
                    const_a_str = names.pop()
                    const_b_str = names.pop()
                    const_c_str = names.pop()
                    const_d_str = names.pop()
                    for value_a in range(lower_bound, upper_bound):
                        for value_b in range(lower_bound, upper_bound):
                            for value_c in range(lower_bound, upper_bound):
                                for value_d in range(lower_bound, upper_bound):
                                    patch = {lid: (tree, {const_a_str: value_a, const_b_str: value_b, const_c_str: value_c, const_d_str: value_d})}
                                    index = atomic_patchlist_append(patch)
                                    vc = verify_parallel(patch, specification)
                                    pool.apply_async(check_sat, args=(vc, index), callback=collect_synthesis_result)
                else:
                    logger.error("constants=" + str(names))
                    logger.error("More than 4 constants are currently not supported!")
                    exit(1)
        ## Otherwise: verify the patch and report it.    
        else:
            patch = {lid: (tree, {})}
            index = atomic_patchlist_append(patch)
            vc = verify_parallel(patch, specification)
            pool.apply_async(check_sat, args=(vc, index), callback=collect_synthesis_result)

    pool.close()
    logger.info("\t\twaiting for thread completion")
    pool.join()

    # assert(len(result_list) == len(path_list))

    #print("collected_patch_indeces=" + str(collected_patch_indeces))

    ## Filter feasible patches and return them.
    temp_set = set()
    synthesis_result_list = []
    for result in collected_patch_indeces:
        is_feasible, index = result
        if is_feasible:
            patch = patch_list[index]
            patch_str = str(patch)
            if not patch_str in temp_set:
                temp_set.add(patch_str)
                synthesis_result_list.append(patch)
    return synthesis_result_list



def contains_constant(tree_content: Dict[str, 'ComponentTree']) -> bool:
    """
    Checks the tree content (incl. sub-trees, ergo it is recursive) for constant values.
    """
    if "left" not in tree_content or "right" not in tree_content:
        return False
    left_name = tree_content['left'][0][0]
    left_dict = tree_content['left'][1] # if there is a non-empty dict, then left is no leaf node
    right_name = tree_content['right'][0][0]
    right_dict = tree_content['right'][1] # if there is a non-empty dict, then right is no leaf node

    # If left side is a leaf node, then check for constant.
    if not left_dict and left_name.startswith('constant_'):
        return True
    # If right side is a leaf node, then check for constant.
    elif not right_dict and right_name.startswith('constant_'):
        return True
    # If left side is an intermediate node, then check the sub-tree for constants.
    elif left_dict and contains_constant(left_dict):
        return True
    # If right side is an intermediate node, then check the sub-tree for constants.
    elif right_dict and contains_constant(right_dict):
        return True
    # Finally, return that there is no constant.
    else:
        return False


def contains_only_constants(tree_content: Dict[str, 'ComponentTree']) -> bool:
    """
    Checks whether there are only constants in the tree content (incl. sub-trees, ergo it is recursive) and no variables.
    """
    left_name = tree_content['left'][0][0]
    left_dict = tree_content['left'][1] # if there is a non-empty dict, then left is no leaf node
    right_name = tree_content['right'][0][0]
    right_dict = tree_content['right'][1] # if there is a non-empty dict, then right is no leaf node

    # If left side is a leaf node, then check for constant.
    if not left_dict and not left_name.startswith('constant_'):
        return False
    # If right side is a leaf node, then check for constant.
    elif not right_dict and not right_name.startswith('constant_'):
        return False
    # If left side is an intermediate node, then check the sub-tree for constants.
    elif left_dict and not contains_only_constants(left_dict):
        return False
    # If right side is an intermediate node, then check the sub-tree for constants.
    elif right_dict and not contains_only_constants(right_dict):
        return False
    # Finally, return that there is no constant.
    else:
        return True


def get_all_constant_names(tree_content: Dict[str, 'ComponentTree']) -> Set[str]:
    """
    Collects all constant names in a tree.
    """
    names = set()

    left_name = tree_content['left'][0][0]
    left_dict = tree_content['left'][1] # if there is a non-empty dict, then left is no leaf node
    right_name = tree_content['right'][0][0]
    right_dict = tree_content['right'][1] # if there is a non-empty dict, then right is no leaf node

    # If left side is a leaf node, then check for constant.
    if not left_dict and left_name.startswith('constant_'):
        names.add(left_name[9:])
    # If left side is an intermediate node, then check the sub-tree for constants.
    elif left_dict:
        names = names.union(get_all_constant_names(left_dict))

    # If right side is a leaf node, then check for constant.
    if not right_dict and right_name.startswith('constant_'):
        names.add(right_name[9:])
    # If right side is an intermediate node, then check the sub-tree for constants.
    elif right_dict:
        names = names.union(get_all_constant_names(right_dict))
    
    # Finally, return the collected constant names (might be empty).
    return names


def load_specification(spec_files: List[Tuple[Path, Path]]) -> Specification:
    logger.info("loading specification")
    specification: Specification = {}
    smt_parser = SmtLibParser()

    for (assertion_file, klee_dir) in spec_files:
        logger.info(f"loading test assertion {assertion_file}")
        tid = assertion_file.stem
        with assertion_file.open() as f:
            script = smt_parser.get_script(f)
            assertion_formula = script.get_last_formula()
        if tid in specification:
            logger.error(f"directory name {tid} is not unique")
            exit(1)
        logger.info(f"loading klee paths {klee_dir}")
        test_spec = Klee.load(tid, assertion_formula, klee_dir)
        if not test_spec[tid][0]:
            raise ValueError(f"no paths loaded for test {tid}")
        specification.update(test_spec)
    return specification


def load_programs(files: Dict[str, Path], components: List[Component]) -> Dict[str, Union[Program, Formula]]:
    """Load programs that are represented either semantically through formulas or syntactically through components
    """
    programs = {}
    smt_parser = SmtLibParser()
    for lid, path in files.items():
        if path.suffix == '.smt2':
            with path.open() as smt_file:
                script = smt_parser.get_script(smt_file)
                programs[lid] = script.get_last_formula()
        elif path.suffix == '.json':
            with path.open() as json_file:
                data = json.load(json_file)
                programs[lid] = program_of_json(data, components)
        else:
            logger.error(f"unsupported file type: {path}")
            exit(1)
    return programs


def load_components(comp_files: List[Path]) -> List[Component]:
    logger.info("loading components")
    components = []

    for component_file in comp_files:
        logger.info(f"loading component {component_file}")
        cid = component_file.stem
        if cid in dict(components):
            logger.error(f"file name {cid} is not unique")
            exit(1)
        with component_file.open() as f:
            pysmt.environment.push_env()
            smt_parser = SmtLibParser()
            script = smt_parser.get_script(f)
            semantics = script.get_last_formula()
            is_var_or_const = any_fn(ComponentSymbol.is_rvalue, ComponentSymbol.is_lvalue, ComponentSymbol.is_const)
            # we assume that variables and constants are global, but everything else is local
            instantiated = Instance.of_formula(semantics, cid, Instance.COMPONENT, complement(is_var_or_const))
            pysmt.environment.pop_env()
            normalized = pysmt.environment.get_env().formula_manager.normalize(instantiated)
        components.append((cid, normalized))

    return components


def main(args):
    parser = argparse.ArgumentParser('Trident synthesizer')
    parser.add_argument('--tests',
                        nargs='+',
                        type=(lambda a: (a.split(':')[0], a.split(':')[1])),
                        required=True,
                        metavar='FILE:DIR',
                        help='pairs of test assertion and klee paths directory')
    parser.add_argument('--components',
                        nargs='+',
                        metavar='FILE',
                        help='synthesis components')
    parser.add_argument('--verify',
                        nargs='+',
                        type=(lambda a: (a.split(':')[0], a.split(':')[1])),
                        metavar='LID:FILE',
                        help='verify given expressions')
    parser.add_argument('--depth',
                        type=int,
                        default=3,
                        help='depth of synthesized expressions')
    parser.add_argument('--all',
                        action='store_true',
                        help='generate all patches')
    parser.add_argument('--all-values',
                        nargs=1,
                        type=(lambda a: (int(a.split(':')[0]), int(a.split(':')[1]))),
                        required=False,
                        metavar='LOWER_BOUND:UPPER_BOUND',
                        help='generate all patches with concrete value enumeration within the given range')
    parser.add_argument('--output',
                        nargs='+',
                        metavar='DIR',
                        help='specify output directory')
    args = parser.parse_args(args)

    rootLogger = logging.getLogger()
    rootLogger.setLevel(logging.INFO)
    consoleHandler = logging.StreamHandler()
    FORMAT = logging.Formatter('%(asctime)s  %(levelname)-7s  %(message)s')
    consoleHandler.setFormatter(FORMAT)
    rootLogger.addHandler(consoleHandler)

    spec_files = [(Path(a[0]), Path(a[1])) for a in args.tests]

    specification = load_specification(spec_files)

    components = []
    if args.components:
        comp_files = [Path(f) for f in args.components]
        components = load_components(comp_files)

    if args.output:
        if not os.path.exists(args.output[0]):
            os.makedirs(args.output[0])
        logger.info(f"patches will be stored in: {args.output[0]}")

    if args.all_values:
        lower_bound = args.all_values[0][0]
        upper_bound = args.all_values[0][1]
        logger.info(f"concrete patch mode with valuation in range: [{lower_bound}, {upper_bound}]")

    if args.verify:
        program_files = { a[0]: Path(a[1]) for a in args.verify }
        programs = load_programs(program_files, components)
        result = verify(programs, specification)
        if result:
            print("SUCCESS")
        else:
            print("FAIL")
    else:
        if not components:
            logger.error("components are not provided")
            exit(1)
        depth = args.depth
        if args.all_values:
            result = synthesize(components, depth, specification, True, lower_bound, upper_bound)
        else:
            result = synthesize(components, depth, specification)

        if args.all or args.all_values:
            for i, v in enumerate(result):
                for (lid, prog) in v.items():
                    print(f"#{i} {lid}:\t{program_to_code(prog)}")
                    if args.output:
                        export_json(f"{args.output[0]}/{i}_{lid}.json", program_to_json(prog))

        else:
            programs = next(result, None)
            if programs:
                for (lid, prog) in programs.items():
                    print(f"{lid}:\t{program_to_code(prog)}")
                    if args.output:
                        export_json(f"{args.output[0]}/{i}_{lid}.json", program_to_json(prog))
            else:
                print("FAIL")

def export_json(output_file, json_content):
    f = open(output_file, "w+")
    f.write(str(json_content))
    f.close()

# TODO just copied from extractor
def extract_constraints_from_patch(patch):
    lid = list(patch.keys())[0]
    eid = 0
    patch_component = patch[lid]
    patch_constraint = program_to_formula(patch_component)
    program_substitution = {}
    for program_symbol in collect_symbols(patch_constraint, lambda x: True):
        kind = ComponentSymbol.check(program_symbol)
        data = ComponentSymbol.parse(program_symbol)._replace(lid=lid)._replace(eid=eid)
        if kind == ComponentSymbol.RRETURN:
            program_substitution[program_symbol] = RuntimeSymbol.angelic(data)
        elif kind == ComponentSymbol.RVALUE:
            program_substitution[program_symbol] = RuntimeSymbol.rvalue(data)
        elif kind == ComponentSymbol.LVALUE:
            program_substitution[program_symbol] = RuntimeSymbol.lvalue(data)
        else:
            pass  # FIXME: do I need to handle it somehow?
    substituted_patch = patch_constraint.substitute(program_substitution)
    return substituted_patch

if __name__ == "__main__":
    import sys
    main(sys.argv[1:])
