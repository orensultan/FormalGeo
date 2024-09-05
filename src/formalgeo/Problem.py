import json
import re
from formalgeo.data import DatasetLoader
from formalgeo.solver import Interactor
from formalgeo.tools import show_solution

dl = DatasetLoader(dataset_name="formalgeo7k_v1", datasets_path="formalgeo7k_v1")
solver = Interactor(dl.predicate_GDL, dl.theorem_GDL)


# def activate_theory_with_arguments(theory_with_templates, theory_with_args):
#     # Extract the theory name and templates
#     theory_name, templates = eval(theory_with_templates)
#     premise_template = templates['premise']
#     conclusion_template = templates['conclusion'][0]
#
#     # Extract the new theory name and its arguments
#     theory_name_with_args, *args = re.findall(r'\w+', theory_with_args)
#
#     # Create a dictionary mapping from original variables to new arguments
#     original_vars = re.findall(r'\w+', theory_name)
#     substitutions = dict(zip(original_vars, args))
#
#     # Substitute the arguments in the premise and conclusion
#     premise = premise_template
#     for var, value in substitutions.items():
#         premise = premise.replace(var, value)
#
#     conclusion = conclusion_template
#     for var, value in substitutions.items():
#         conclusion = conclusion.replace(var, value)
#
#     # Format the final theory
#     activated_theory = f"('{theory_name_with_args}({', '.join(args[1:])})', " \
#                        f"{{'premise': '{premise}', 'conclusion': ['{conclusion}']}})"
#
#     return activated_theory


# def extract_arguments_from_theory(theory):
#     _, args_str = theory.split('(')
#     args_str = args_str.rstrip(')')
#     arguments = args_str.split(',')[1:]  # Skip the first element if it's not part of the arguments
#     return arguments

# def get_theory_arguments(original_json, theory_call):
#     theorem_data = json.loads(original_json)
#     original_arguments = extract_arguments_from_theory(theorem_data['theorem'])
#     new_arguments = extract_arguments_from_theory(theory_call)
#     assert len(original_arguments) == len(new_arguments), "Argument lists have different lengths."
#     for orig_arg, new_arg in zip(original_arguments, new_arguments):
#         assert len(orig_arg) == len(new_arg), f"Argument '{orig_arg}' and '{new_arg}' have different lengths."
#     return original_arguments, new_arguments


# def replace_symbols(expression, mapping):
#     substrings = re.findall(r'\(([A-Z]+)\)', expression)
#     for substring in substrings:
#         new_substring = ''.join(mapping.get(char, char) for char in substring)
#         expression = expression.replace(substring, new_substring)
#     return expression

# def find_all_indices(concat_str, substring, start_index=0, current_indices=None):
#     if current_indices is None:
#         current_indices = []
#     if len(current_indices) == len(substring):
#         return [current_indices]
#     result = []
#     for i in range(start_index, len(concat_str)):
#         if concat_str[i] == substring[len(current_indices)]:
#             new_indices = current_indices + [i]
#             result.extend(find_all_indices(concat_str, substring, i + 1, new_indices))
#     return result

# def get_substring_from_indices(concat_str, indices):
#     return ''.join([concat_str[i] for i in indices])


# def find_all_indices(original_args_concat, target_sequence):
#     indices = []
#     for char in target_sequence:
#         index = original_args_concat.index(char)
#         indices.append(index)
#     return indices


# def replace_in_expression(expression, original_args_concat, new_args_concat):
#     substrings = re.findall(r'\(([A-Z]+)\)', expression)
#     for target_sequence in substrings:
#         print(f"\nProcessing target sequence '{target_sequence}':")
#         result = find_all_indices(original_args_concat, target_sequence)
#         print("All possible indices:", result)
#
#         if len(result) == 0:
#             print(1)
#         # Since we just want the indices where the letters appear
#         selected_indices = result
#         print("Selected Indices:", selected_indices)
#
#         substring_from_new_args = get_substring_from_indices(new_args_concat, selected_indices)
#         print(
#             f"Extracted Substring from New Args for '{target_sequence}': '{substring_from_new_args}' using indices {selected_indices}")
#
#         expression = expression.replace(f"({target_sequence})", f"({substring_from_new_args})")
#
#     return expression

# def replace_in_premise_and_conclusion(premise, conclusion, original_args_concat, new_args_concat):
#     updated_premise = replace_in_expression(premise, original_args_concat, new_args_concat)
#
#     updated_conclusion = []
#     for concl in conclusion:
#         updated_conclusion.append(replace_in_expression(concl, original_args_concat, new_args_concat))
#
#     return updated_premise, updated_conclusion

# def get_theorem_seqs_expl(theorem_seqs):
#     theorems_seqs_expl = []
#     for theorem_call in theorem_seqs:
#         theory_json = get_theory(theorem_call)
#         original_args, new_args = get_theory_arguments(theory_json, theorem_call)
#         original_args_concat,  new_args_concat= "".join(original_args), "".join(new_args)
#         premise, conclusion = json.loads(theory_json)['premise'], json.loads(theory_json)['conclusion']
#         updated_premise, updated_conclusion = replace_in_premise_and_conclusion(premise, conclusion,
#                                                                                 original_args_concat, new_args_concat)
#         updated_json = {
#             "theorem": theorem_call,
#             "premise": updated_premise,
#             "conclusion": updated_conclusion
#         }
#         updated_json_str = json.dumps(updated_json, indent=4)
#         theorems_seqs_expl.append(updated_json_str)
#     return theorems_seqs_expl


# def get_theorem_seqs_dag_expl(theorem_seqs_dag):
#     theorems_seqs_dag_expl = []
#     for key, val in theorem_seqs_dag.items():
#         for v in val:
#             theory_str = str(get_theory(v))
#             input_string1 = v
#             input_string2 = theory_str
#             result1 = extract_substring_first_exp(input_string1)
#             result2 = extract_substring_second_exp(input_string2)
#             if len(result1.replace(",", "")) != len(result2.replace(",", "")):
#                 raise ValueError("The extracted substrings must have the same length for character-level mapping.")
#
#             mapping_dict = {result2[i]: result1[i] for i in range(len(result2)) if result2[i].isupper()}
#             theorems_seqs_dag_expl.append(replace_symbols(input_string2, mapping_dict))
#     return theorems_seqs_dag_expl

def modify_string(input_string):
    modified_string = re.sub(r'(\w+)-(\d+)', r'\1=\2', input_string)
    return modified_string

def convert_equations(equations_string):
    equations_list = equations_string.split("\n")
    res = []
    for row in equations_list:
        values = row.split(";")
        if len(values) > 1:
            res.append(modify_string(values[1]))
    return res

def convert_relations(relations_string):
    relations_list = relations_string.split("\n")
    res = []
    type = ""
    for row in relations_list:
        if not row.startswith("("):
            type = row[:-1]
        else:
            values = row.split(";")
            res.append((type + "(" + values[1] + ")", values[-1][:-1]))
    extended_res = []
    for tup in res:
        if tup[-1] == "prerequisite":
            continue
        extended_res.append(tup[0])
    return extended_res

class Problem:



    def __init__(self, id, problem_level, description, solution, construction_cdl, abstract_construction_cdl, text_cdl,
                 abstract_text_cdl, goal_cdl, abstract_goal_cdl, theorem_seqs, abstract_theorem_seqs,
                 theorem_seqs_dag, abstract_theorem_seqs_dag):
        self.id = id
        self.level = problem_level
        self.description = description
        self.solution = solution
        self.construction = []
        self.construction_cdl = construction_cdl
        self.abstract_construction_cdl = abstract_construction_cdl
        self.text_cdl = text_cdl
        self.abstract_text_cdl = abstract_text_cdl
        self.goal_cdl = goal_cdl
        self.abstract_goal_cdl = abstract_goal_cdl

        self.theorem_seqs = theorem_seqs
        self.abstract_theorem_seqs = abstract_theorem_seqs
        self.theorem_seqs_dag = theorem_seqs_dag
        self.abstract_theorem_seqs_dag = abstract_theorem_seqs_dag

    def enrich_problem(self):
        problem_CDL = dl.get_problem(self.id)
        solver.load_problem(problem_CDL)
        result_dict = show_solution(solver.problem)

        # prompt_input_description = problem_CDL['problem_text_en'].split('As shown in the diagram,')[1].strip()
        # prompt_input_construction_cdl = "\n".join(problem_CDL['construction_cdl'])
        # prompt_input_text_cdl = "\n".join(problem_CDL['text_cdl'])
        # prompt_input_goal_cdl = problem_CDL['goal_cdl']
        # prompt_input_relations = remove_trailing_empty_lines(result_dict['relations'])
        construction_cdl_extended = convert_relations(result_dict['relations'])
        prompt_input_symbols_and_values = result_dict['symbols_and_values']
        prompt_output_equations = convert_equations(result_dict['equations'])
        prompt_output_goal_symbol = result_dict['goal_value']
        prompt_output_answer = result_dict['answer']

        self.construction_cdl_extended = construction_cdl_extended
        self.symbols_and_values = prompt_input_symbols_and_values
        self.equations = prompt_output_equations
        self.goal_symbol = prompt_output_goal_symbol.split("goal:")[1].strip()
        self.answer = prompt_output_answer.split("answer:")[1].strip()

    def print_problem(self):
        print('---')
        print("problem:")
        print(self.id)
        print("level:")
        print(self.level)

        print("description:")
        print(self.description)
        print("construction_cdl:")
        print(self.construction_cdl)
        for i in range(len(self.construction_cdl)):
            self.construction.append(convert_shape_to_polygon(self.construction_cdl[i]))
        print("construction:")
        print(self.construction)
        print("text_cdl:")
        print(self.text_cdl)
        print("goal_cdl:")
        print(self.goal_cdl)
        print("solution: " + str(self.solution))
        print("theorem_seqs_dag:")
        print(self.theorem_seqs_dag)



def get_theory(theorem):
    with open('formalgeo7k_v1/gdl/theorem_GDL.json', 'r') as file:
        theorems = json.load(file)
        matching_keys = [key for key, value in theorems.items() if theorem.split("(")[0] in key]
        key = matching_keys[0]
        num = theorem.split("(")[1][0]
        premise_and_conclusion = theorems[key][num]
        final_json = {
            "theorem": f"{key.split('(')[0]}({num},{key.split('(')[1]}",
            "premise": premise_and_conclusion['premise'],
            "conclusion": premise_and_conclusion['conclusion']
        }
        final_json_str = json.dumps(final_json, indent=4)
        return final_json_str


def convert_shape_to_polygon(shape_str):
    if not shape_str.startswith('Shape'):
        return shape_str

    inside_parentheses = shape_str[shape_str.index('(') + 1: shape_str.index(')')]
    segments = inside_parentheses.split(',')

    points = []
    for segment in segments:
        for point in segment:
            if point not in points:
                points.append(point)

    points_str = ''.join(points)
    polygon_names = {3: 'Triangle', 4: 'Quadrilateral', 5: 'Pentagon', 6: 'Hexagon'}
    polygon_name = polygon_names.get(len(points), 'Polygon')

    polygon_str = f'{polygon_name}({points_str})'

    return polygon_str


def replace_symbols(input_string, mapping_dict):
    # Function to replace symbols in a given text based on the dictionary
    def replace_inside_parentheses(match):
        content = match.group(1)
        # Replace all capital letters in the content
        new_content = ''.join(mapping_dict.get(char, char) for char in content)
        return f'({new_content})'

    # Pattern to find content inside parentheses
    pattern = r'\(([A-Z,]+)\)'

    # Replace the content inside parentheses
    new_string = re.sub(pattern, replace_inside_parentheses, input_string)
    return new_string

