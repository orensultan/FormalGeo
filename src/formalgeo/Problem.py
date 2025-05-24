import json
import re
import os
from formalgeo.data import DatasetLoader
from formalgeo.solver import Interactor
from formalgeo.tools import show_solution

# Get the path to the project root (two directories up from this script)
PROJECT_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))

# Load GDL files directly
with open(os.path.join(PROJECT_ROOT, 'formalgeo7k_v1/gdl/predicate_GDL.json'), 'r') as f:
    predicate_GDL = json.load(f)
with open(os.path.join(PROJECT_ROOT, 'formalgeo7k_v1/gdl/theorem_GDL.json'), 'r') as f:
    theorem_GDL = json.load(f)

# Create a solver instance with the loaded GDL files
solver = Interactor(predicate_GDL, theorem_GDL)

dl = DatasetLoader(dataset_name="formalgeo7k_v1", datasets_path=os.path.join(PROJECT_ROOT, "formalgeo7k_v1"))





def modify_string(input_string):
    modified_string = re.sub(r'(\w+)-(\d+)', r'\1=\2', input_string)
    return modified_string

def convert_equations(equations_string):
    equations_list = equations_string.split("\n")
    res = []
    for row in equations_list:
        values = row.split(";")
        if len(values) > 1:
            res.append(values[1])
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



def get_theorem(theorem):
    with open(os.path.join(PROJECT_ROOT, 'formalgeo7k_v1/gdl/theorem_GDL.json'), 'r') as file:
        theorems = json.load(file)
        matching_keys = [key for key, value in theorems.items() if theorem.split("(")[0] in key]
        key = matching_keys[0]
        num = theorem.split("(")[1][0]
        if key in theorems and num in theorems[key]:
            premise_and_conclusion = theorems[key][num]
            final_json = {
                "theorem": f"{key.split('(')[0]}({num},{key.split('(')[1]}",
                "premise": premise_and_conclusion['premise'],
                "conclusion": premise_and_conclusion['conclusion'],
            }
        else:
            final_json = {
                "theorem": f"{key.split('(')[0]}({num},{key.split('(')[1]}",
                "premise": "theorem not found",
                "conclusion": "theorem not found",
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

