#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import pickle
import json
from app import generator, utilities, values, emitter
from app.synthesis import program_to_code


def write_as_json(data, output_file_path):
    content = json.dumps(data)
    with open(output_file_path, 'w') as out_file:
        out_file.writelines(content)


def write_as_pickle(data, output_file_path):
    with open(output_file_path, 'wb') as out_file:
        pickle.dump(data, out_file)


def write_patch_set(patch_list, output_file_path):
    emitter.normal("\twriting patch list to file")
    template_count = 0
    txt_lines = []
    for patch in patch_list:
        template_count = template_count + 1
        txt_lines.append("Patch #" + str(template_count))
        for (lid, prog) in patch.items():
            code = lid + ": " + (program_to_code(prog))
        for comp_var, prog_var in values.MAP_PROG_VAR.items():
            code = code.replace(comp_var, prog_var)
        txt_lines.append(code)
        patch_formula = generator.generate_formula_from_patch(patch)
        patch_formula_str = patch_formula.serialize()
        patch_index = utilities.get_hash(patch_formula_str)
        patch_score = values.LIST_PATCH_SCORE[patch_index]
        concrete_patch_count = 1
        if values.DEFAULT_PATCH_TYPE == values.OPTIONS_PATCH_TYPE[1]:
            patch_space = values.LIST_PATCH_SPACE[patch_index]
            partition_count = 0
            for partition in patch_space:
                partition_count = partition_count + 1
                txt_lines.append("\t\tPartition: " + str(partition_count))
                for constant_name in partition:
                    txt_lines.append("\t\t\tConstant: " + constant_name)
                    constant_info = partition[constant_name]
                    lower_bound = str(constant_info['lower-bound'])
                    upper_bound = str(constant_info['upper-bound'])
                    txt_lines.append("\t\t\tRange: " + lower_bound + " <= " + constant_name + " <= " + upper_bound)
                    dimension = len(range(int(lower_bound), int(upper_bound) + 1))
                    txt_lines.append("\t\t\tDimension: " + str(dimension))
                    concrete_patch_count = utilities.count_concrete_patches_per_template(patch)
        txt_lines.append("\t\tPatch Count: " + str(concrete_patch_count))
        txt_lines.append("\t\tPath Coverage: " + str(patch_score))
        txt_lines.append("\t\tIs Under-approximating: " + str(values.LIST_PATCH_UNDERAPPROX_CHECK[patch_index]))
        txt_lines.append("\t\tIs Over-approximating: " + str(values.LIST_PATCH_OVERAPPROX_CHECK[patch_index]))
    with open(output_file_path, 'w') as out_file:
        out_file.writelines(line + "\n" for line in txt_lines)
