import json
import re
class Problem:
    def __init__(self, id, problem_level, description, solution, construction_cdl, abstract_construction_cdl, text_cdl,
                 abstract_text_cdl, goal_cdl, abstract_goal_cdl, theorem_seqs, abstract_theorem_seqs,
                 theorem_seqs_dag, abstract_theorem_seqs_dag):
        self.id = id
        self.level = problem_level
        self.description = description
        self.solution = solution
        self.construction_cdl = construction_cdl
        self.construction = []
        self.abstract_construction_cdl = abstract_construction_cdl
        self.text_cdl = text_cdl
        self.abstract_text_cdl = abstract_text_cdl
        self.goal_cdl = goal_cdl
        self.abstract_goal_cdl = abstract_goal_cdl

        self.theorem_seqs = theorem_seqs
        self.abstract_theorem_seqs = abstract_theorem_seqs
        self.theorem_seqs_dag = theorem_seqs_dag
        self.abstract_theorem_seqs_dag = abstract_theorem_seqs_dag


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

        theories_set = set()
        theorems_expl = []
        for key, val in self.theorem_seqs_dag.items():
            for v in val:
                theory_str = str(get_theory(v))
                theories_set.add(theory_str)
                input_string1 = v
                input_string2 = theory_str
                result1 = extract_substring_first_exp(input_string1)
                result2 = extract_substring_second_exp(input_string2)
                if len(result1.replace(",", "")) != len(result2.replace(",", "")):
                    raise ValueError("The extracted substrings must have the same length for character-level mapping.")

                mapping_dict = {result2[i]: result1[i] for i in range(len(result2)) if result2[i].isupper()}
                theorems_expl.append(replace_symbols(input_string2, mapping_dict))

        for key, val in self.theorem_seqs_dag.items():
            l = []
            for v in val:
                l.append(remove_id_first_arg(v))
            self.theorem_seqs_dag[key] = l

        print("theorem_seqs_dag:")
        print(self.theorem_seqs_dag)
        print("theorem_explanation:")
        for t in theorems_expl:
            print(t)

        print("solution: " + str(self.solution))


def get_theory(theory):
    with open('formalgeo7k_v1/gdl/theorem_GDL.json', 'r') as file:
        theories = json.load(file)
        matching_keys = [key for key, value in theories.items() if theory.split("(")[0] in key]
        key = matching_keys[0]
        num = theory.split("(")[1][0]
        premise_and_conclusion = theories[key][num]
        return key, premise_and_conclusion


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

def remove_id_first_arg(input_string):
    pattern = r'([a-zA-Z_]+)\(\d+,?(.*)\)'
    converted_string = re.sub(pattern, r'\1(\2)', input_string)
    return converted_string



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

def extract_substring_first_exp(input_string):
    pattern = r'\((?:[^,]+,)?([^,]+(?:,[^)]+)?)\)'
    match = re.search(pattern, input_string)
    return match.group(1) if match else None


def extract_substring_second_exp(input_string):
    pattern = r"\('([^']+)\(([^)]+)\)'\s*,"
    match = re.search(pattern, input_string)
    return match.group(2) if match else None
