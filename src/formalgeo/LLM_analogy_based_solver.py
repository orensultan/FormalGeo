import re
import json
from formalgeo.data import download_dataset, DatasetLoader
from formalgeo.solver import Interactor
from formalgeo.parse import parse_one_theorem

from formalgeo.tools import show_solution

from Problem import get_theory, replace_symbols
from create_problems_proofs_similarity_dataset import save_problems
import time
import openai

openai.api_key = "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"
openai.api_key = "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"
openai.api_key = "sk-ds-openapi-key-0sfNvLjYF3wMuFQcp7oST3BlbkFJWeqSW76sV6Gy48mjIJVK"
openai.api_key = "sk-ds-openapi-key-0sfNvLjYF3wMuFQcp7oST3BlbkFJWeqSW76sV6Gy48mjIJVK"
openai.api_key = "sk-svcacct-kVTUGOlCTL2vge6gtHi--la5vr8g-lqT3ieuWGdHQBrYChItgkm2k1WPS9mA-MXe7ebaPHCMk8YrCft1OT3BlbkFJLNl-eYBXpQiokB5m3Nw0oiO9ZOe_Paf1WH0Kh4If52-rQ92DiSodgoopxiDoQDKlAGYDPRpiWamueq8vQA"
from utils import display_image
from similar_proofs_retrieval import retrieve_similar_proofs
import ast
import re

dl = DatasetLoader(dataset_name="formalgeo7k_v1", datasets_path="formalgeo7k_v1")
solver = Interactor(dl.predicate_GDL, dl.theorem_GDL)
with open('formalgeo7k_v1/gdl/theorem_GDL.json', 'r') as f:
    theorems = json.load(f)



def get_theorem_seqs_expl(theorem_seqs):
    theorems_seqs_expl = []
    for theorem in theorem_seqs:
        t_name, t_branch, t_para = parse_one_theorem(theorem)
        letters = get_letters(t_name, t_para)
        theory_json = get_theory(theorem)
        premise, conclusions = json.loads(theory_json)['premise'], json.loads(theory_json)['conclusion']
        premise = replace_symbols(premise, letters)
        for i in range(len(conclusions)):
            conclusions[i] = replace_symbols(conclusions[i], letters)

        updated_json = {
            "theorem": theorem,
            "premise": premise,
            "conclusion": conclusions
        }
        updated_json_str = json.dumps(updated_json, indent=4)
        theorems_seqs_expl.append(updated_json_str)
    return theorems_seqs_expl



def get_letters(t_name, t_para):
    letters = {}
    for i in range(len(solver.parsed_theorem_GDL[t_name]["vars"])):
        key = solver.parsed_theorem_GDL[t_name]["vars"][i].upper()
        letters[key] = t_para[i]
    return letters

def remove_trailing_empty_lines(text):
    return '\n'.join(line for line in text.splitlines() if line.strip())


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
    return "\n".join(extended_res)


def validate_premise(premise, relations_string):
    # Parse the relations string
    parsed_data = parse_relations(relations_string)

    # Split the premise string by '&'
    validations = premise.split("&")

    # Dictionary to store validation results
    validation_results = {}

    # Function to validate a single item
    def validate_item(item, parsed_data):
        match = re.match(r"(\w+)\(([\w,]+)\)", item)
        if match:
            section = match.group(1)
            entities = match.group(2).split(',')

            # Check only in the relevant section
            if section in parsed_data:
                for relation in parsed_data[section]:
                    if set(entities).issubset(set(relation['entities'])):
                        return True
            else:
                return False  # Section not found
        return False

    # Validate each item in the premise
    for item in validations:
        item = item.strip()
        validation_results[item] = validate_item(item, parsed_data)

    # Return the validation results
    return validation_results


#         updated_json = {
#             "theorem": theorem_call,
#             "premise": updated_premise,
#             "conclusion": updated_conclusion
#         }
#         updated_json_str = json.dumps(updated_json, indent=4)
#         theorems_seqs_expl.append(updated_json_str)


def theorem_verifier(solver, theorem_seqs):
    res = "Correct"

    for theorem in theorem_seqs:
        t_name, t_branch, t_para = parse_one_theorem(theorem)
        # try:
        letters = get_letters(t_name, t_para)
        theory_json = get_theory(theorem)
        premise = json.loads(theory_json)['premise']
        premise = replace_symbols(premise, letters)
        update, reason = solver.apply_theorem(t_name, t_branch, t_para)
        if not update and reason != 'No updates were made.':
            return "A mistake in theorem sequence step: " + theorem + ". Premise: " + premise + ". " + reason

            # expl = get_theorem_seqs_expl([theorem])[0]
            # parsed_tuple = ast.literal_eval(expl)
            # premise = parsed_tuple[1]['premise']
            # if not update:
            #     results = validate_premise(premise, res2['prompt_input_relations'])
            #     for item, is_valid in results.items():
            #         print(f"{item}: {'Valid' if is_valid else 'Invalid'}")
            #
            #     invalid_premises = " | ".join(
            #         [f"please rewrite the theory step, you have an invalid premise: {key} which is not part of the given RELATIONS of the problem" for key, value in results.items() if not value])
            #     if len(invalid_premises) > 0:
            #         return "Theorem sequence step: " + theorem + ". premise: " + premise + ". " + invalid_premises

        # except Exception as e:
        #     print(e)
        #     res = str(e) + " Theorem sequence step: " + theorem
        #     break

    return res





def def_call_gpt_o1_preview(model, messages):
    response = openai.ChatCompletion.create(
        model=model,
        messages=messages
    )
    return response.choices[0].message['content']


def call_gpt(model, messages, temperature=0, wait_time=1, retry_wait_time=6, max_retries=10):
    retries = 0
    while retries <= max_retries:
        try:
            response = openai.ChatCompletion.create(
                model=model,
                messages=messages,
                max_tokens=4096,
                temperature=temperature,
                top_p=1,
                frequency_penalty=0,
                presence_penalty=0,
            )

            if response and response.choices and response.choices[0]:
                res = response.choices[0].message['content'].strip()
                time.sleep(wait_time)
                return res

        except openai.error.OpenAIError as e:
            print(f"OpenAIError: {e}. Retrying in {retry_wait_time} seconds...")
            time.sleep(retry_wait_time)
            retries += 1
            if retries > max_retries:
                print("Failed after maximum retries.")
                raise Exception(f"Failed after {max_retries} attempts due to OpenAI errors.")
        except Exception as e:
            print(f"Unexpected error: {e}. Not retrying.")
            raise Exception(f"Unexpected error: {e}")

def gpt_response(messages, model_name):
    resp = def_call_gpt_o1_preview(model=model_name, messages=messages) if model_name != 'o1-preview' else def_call_gpt_o1_preview(model=model_name, messages=messages)
    print(resp)
    return resp

def find_relevant_theorems(theorems, problems_set):
    relevant_theorems = {}
    for key in theorems.keys():
        for problem in problems_set:
            if problem in key:
                relevant_theorems[key] = theorems[key]
    return relevant_theorems

def get_problem_fields(problem):
    construction_cdl = "\n".join(problem.construction_cdl)
    text_cdl = "\n".join(problem.text_cdl)
    construction_cdl_extended = "\n".join(problem.construction_cdl_extended)
    theorem_seqs = "\n".join(f"{i + 1};{problem.theorem_seqs[i]}" for i in range(len(problem.theorem_seqs)))
    equations = "\n".join(problem.equations)
    return {'construction_cdl': construction_cdl, 'text_cdl': text_cdl,
            'construction_cdl_extended': construction_cdl_extended, 'theorem_seqs': theorem_seqs, 'equations': equations}


def convert_json_list_to_custom_format(json_list):
    result = []

    for index, item in enumerate(json_list, start=1):
        # Parse the JSON string into a dictionary
        theorem_dict = json.loads(item)

        # Extract the fields
        theorem = theorem_dict.get("theorem", "")
        premise = theorem_dict.get("premise", "")
        conclusion = theorem_dict.get("conclusion", [])

        # Format the conclusion as a string
        conclusion_str = json.dumps(conclusion)

        # Create the custom formatted string
        formatted_string = f"step_id: {index}; theorem: {theorem}; premise: {premise}; conclusion: {conclusion_str}"

        # Append to the result list
        result.append(formatted_string)

    # Join all the formatted strings into a single string with line breaks
    return "\n".join(result)


def convert_theorem_seqs_format_string(input_str):
    # Remove the leading and trailing single quotes
    input_str = input_str.strip("'")

    # Split the input string by lines
    lines = input_str.strip().splitlines()

    converted_list = []

    for line in lines:
        line = line.strip()
        if not line.startswith("step_id "):
            continue  # Continue to the next line if this one doesn't start with 'step_id '

        # Split the line by ';'
        parts = line.split(';')

        # Initialize variables with empty strings in case any part is missing
        step_id = ""
        theorem = ""
        premise = ""
        conclusion = ""

        # Extract the parts
        if len(parts) > 0:
            step_id_part = parts[0].strip()
            # Extract just the number from 'step_id N'
            if step_id_part.startswith('step_id '):
                step_id = step_id_part[len('step_id '):]

        if len(parts) > 1:
            theorem = parts[1].strip()

        if len(parts) > 2:
            premise = parts[2].strip()

        if len(parts) > 3:
            conclusion = parts[3].strip()

        # Combine them in the desired format and add to the list
        converted_list.append(f"{step_id};{theorem};{premise};{conclusion}")

    return "\n".join(converted_list)






def create_messages(content):
    # Constructing the initial message with the user role
    initial_message = {"role": "user", "content": content}

    # Only include the user message
    messages = [initial_message]

    return messages


def generate_and_verify(prompt_path, model_name, similar_problems, problem2, max_retries=5):
    relevant_theorems = set()
    for problem in similar_problems:
        for theorem in problem.abstract_theorem_seqs:
            relevant_theorems.add(theorem)
    for theorem in problem2.abstract_theorem_seqs:
        relevant_theorems.add(theorem)
    gdl_relevant_theorems = find_relevant_theorems(theorems, relevant_theorems)
    with open(prompt_path, 'r') as file:
        initial_prompt = file.read()

    gdl_relevant_theorems_str = json.dumps(gdl_relevant_theorems, indent=4)
    initial_prompt = initial_prompt.replace('{GDL}', gdl_relevant_theorems_str)

    content = initial_prompt
    for i in range(len(similar_problems)):
        problem = similar_problems[i]
        problem_dict = get_problem_fields(problem)

        theorems_seqs_expl = convert_json_list_to_custom_format(get_theorem_seqs_expl(problem.theorem_seqs))
        content += f"\nInputs for Problem A{i+1}:\nDESCRIPTION:\n{problem.description}\nCONSTRUCTION_CDL:\n{problem_dict['construction_cdl']}\n"
        content += f"TEXT_CDL:\n{problem_dict['text_cdl']}\nGOAL_CDL:\n{problem.goal_cdl}\nCONSTRUCTION_CDL_EXTENDED:\n{problem_dict['construction_cdl_extended']}\nSYMBOLS_AND_VALUES:\n{problem.symbols_and_values}\n"
        content += f"Outputs:\nOutputs for Problem A{i+1}:\nEQUATIONS:\n{problem_dict['equations']}\nGOAL_SYMBOL:\n{problem.goal_symbol}\nANSWER:\n{problem.answer}\nTHEOREM_SEQUENCE:\n{theorems_seqs_expl}\n"

    problem_dict = get_problem_fields(problem2)
    content += f"Inputs for Problem B:\nDESCRIPTION:\n{problem2.description}\n"
    content += f"CONSTRUCTION_CDL:\n{problem_dict['construction_cdl']}\nTEXT_CDL:\n{problem_dict['text_cdl']}\nGOAL_CDL:\n{problem2.goal_cdl}\n"
    content += f"CONSTRUCTION_CDL_EXTENDED:\n{problem_dict['construction_cdl_extended']}\nSYMBOLS_AND_VALUES:\n{problem.symbols_and_values}\nOutputs:\nOutputs for Problem B:\n"

    # initial_message = {"role": "user", "content": content}
    # messages = [
    #     {"role": "system", "content": "You are a helpful assistant."},
    #     initial_message
    # ]

    messages = create_messages(content)


    attempts = 0
    theorem_verifier_result = ""
    resp = ""
    while attempts < max_retries:
        resp = gpt_response(messages, model_name)
        generated_theorem_sequence = resp.split("THEOREM_SEQUENCE:\n")[1]
        generated_theorem_sequence = convert_theorem_seqs_format_string(generated_theorem_sequence)
        generated_theorem_sequence_list = re.findall(r'\d+;([^\(\)]+\([^\)]+\))', generated_theorem_sequence)
        # generated_theorem_list = [line.split(';')[1] for line in generated_theorem_sequence.split('\n')]
        theorem_verifier_result = theorem_verifier(solver, generated_theorem_sequence_list)

        if theorem_verifier_result == "Correct":
            print("Theorem sequence verified correctly")
            break

        messages.append({"role": "assistant", "content": resp})
        messages.append({"role": "user", "content": f"Verifier result: {theorem_verifier_result}. Please retry generating the correct theorem sequence proof, using the verifier hints."})
        print(f"Verifier result: {theorem_verifier_result}")
        print(f"Retry attempt: {attempts + 1}")
        attempts += 1

    return messages, resp, theorem_verifier_result



def get_level_to_problems(problems):
    level_to_problems = {}
    for problem_id, problem_obj in problems.items():
        level = problem_obj.level
        if level not in level_to_problems:
            level_to_problems[level] = [problem_id]
        else:
            level_to_problems[level].append(problem_id)
    return level_to_problems



def main(problems):
    level_to_problems = get_level_to_problems(problems)

    # level 1: 2833, level 2: 6523, level 3: 2999, level 4: 2425, level 5: 4908, level 6: 729, level 7: 683, level 8: 912, level 9: 5749
    problem2_id = 5749
    similar_problem_ids = retrieve_similar_proofs(problem2_id, n=5)
    similar_problems = []
    for problem_id in similar_problem_ids:
        problem = problems[problem_id]
        problem.print_problem()
        problem.enrich_problem()
        problem_CDL = dl.get_problem(problem_id)
        solver.load_problem(problem_CDL)
        display_image(problem_id)
        similar_problems.append(problem)


    problem2 = problems[problem2_id]
    problem2.print_problem()
    problem2.enrich_problem()
    problem_CDL = dl.get_problem(problem2_id)
    solver.load_problem(problem_CDL)
    display_image(problem2_id)

    prompt_path = "src/formalgeo/prompt/geometry_similar_problems_prompt.txt"
    model_name = "gpt-4o"
    model_name = "o1-preview"
    messages, resp, verifier_result = generate_and_verify(prompt_path, model_name, similar_problems, problem2)
    print(resp)
    print(1)

if __name__ == "__main__":
    problems = save_problems()
    print(1)
    main(problems)
