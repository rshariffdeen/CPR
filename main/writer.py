#! /usr/bin/env python3
# -*- coding: utf-8 -*-


import pickle
import json
from main import generator, utilities, values, emitter


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
    with open(output_file_path, 'w') as out_file:
        for patch in patch_list:
            template_count = template_count + 1
            out_file.writelines("Patch #" + str(template_count))
            out_file.writelines(patch, message="\t\t")
            patch_formula = generator.generate_formula_from_patch(patch)
            patch_formula_str = patch_formula.serialize()
            patch_index = utilities.get_hash(patch_formula_str)
            patch_score = values.LIST_PATCH_SCORE[patch_index]
            if values.CONF_PATCH_TYPE == values.OPTIONS_PATCH_TYPE[1]:
                patch_space = values.LIST_PATCH_SPACE[patch_index]
                partition_count = 0
                for partition in patch_space:
                    partition_count = partition_count + 1
                    out_file.writelines("\t\tPartition: " + str(partition_count))
                    for constant_name in partition:
                        out_file.writelines("\t\t\tConstant: " + constant_name)
                        constant_info = partition[constant_name]
                        lower_bound = str(constant_info['lower-bound'])
                        upper_bound = str(constant_info['upper-bound'])
                        out_file.writelines("\t\t\tRange: " + lower_bound + " <= " + constant_name + " <= " + upper_bound)
                        dimension = len(range(int(lower_bound), int(upper_bound) + 1))
                        out_file.writelines("\t\t\tDimension: " + str(dimension))
                        concrete_patch_count = utilities.count_concrete_patches_per_template(patch)
            out_file.writelines("\t\tPatch Count: " + str(concrete_patch_count))
            out_file.writelines("\t\tPath Coverage: " + str(patch_score))
            out_file.writelines("\t\tIs Under-approximating: " + str(values.LIST_PATCH_UNDERAPPROX_CHECK[patch_index]))
            out_file.writelines("\t\tIs Over-approximating: " + str(values.LIST_PATCH_OVERAPPROX_CHECK[patch_index]))