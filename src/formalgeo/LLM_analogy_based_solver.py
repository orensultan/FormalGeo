import re
from formalgeo.data import download_dataset, DatasetLoader
from formalgeo.solver import Interactor
from formalgeo.parse import parse_one_theorem
from formalgeo.tools import show_solution

from Problem import get_theorem_seqs_expl
from create_problems_proofs_similarity_dataset import save_problems
import time
import openai

openai.api_key = "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"
openai.api_key = "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"
openai.api_key = "sk-ds-openapi-key-0sfNvLjYF3wMuFQcp7oST3BlbkFJWeqSW76sV6Gy48mjIJVK"
openai.api_key = "sk-ds-openapi-key-0sfNvLjYF3wMuFQcp7oST3BlbkFJWeqSW76sV6Gy48mjIJVK"

from utils import display_image
from similar_proofs_retrieval import retrieve_similar_proof
import ast
import re

dl = DatasetLoader(dataset_name="formalgeo7k_v1", datasets_path="formalgeo7k_v1")
solver = Interactor(dl.predicate_GDL, dl.theorem_GDL)




def remove_trailing_empty_lines(text):
    return '\n'.join(line for line in text.splitlines() if line.strip())


def parse_relations(relations_string):
    # Split by sections (e.g., Shape, Collinear, Point, etc.)
    sections = re.split(r'(?<=\n)(?=\w+:\n)', relations_string)

    # Dictionary to hold all sections
    parsed_data = {}

    # Process each section
    for section in sections:
        if section.strip():  # If the section is not empty
            # Get the section name by finding the first line ending with ':'
            section_name = section.split(':')[0].strip()
            # Split the section into individual relations by newline, starting from the second line
            relations = section.split('\n')[1:]  # Skip the section header line

            # Parse each relation
            parsed_relations = []
            for relation in relations:
                relation = relation.strip()
                if relation:  # Ensure it's not an empty line
                    parts = relation.strip('()').split(';')
                    parsed_relations.append({
                        'id': int(parts[0]),
                        'entities': parts[1].split(','),
                        'dependencies': parts[2].strip('()').split(',') if parts[2] != '(-1)' else [],
                        'type': parts[3]
                    })

            # Store the parsed relations in the dictionary
            parsed_data[section_name] = parsed_relations

    return parsed_data


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
def theorem_verifier(solver, theorem_seqs):
    res = "Correct"

    for theorem in theorem_seqs:
        t_name, t_branch, t_para = parse_one_theorem(theorem)
        try:
            update, reason = solver.apply_theorem(t_name, t_branch, t_para)
            expl = get_theorem_seqs_expl([theorem])[0]
            parsed_tuple = ast.literal_eval(expl)
            premise = parsed_tuple[1]['premise']
            if not update:
                return "Theorem sequence step: " + theorem + ". premise: " + premise + ". " + reason

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

        except Exception as e:
            res = str(e) + " Theorem sequence step: " + theorem
            break

    return res


def parse_problem(pid):
    problem_CDL = dl.get_problem(pid)
    solver.load_problem(problem_CDL)

    result_dict = show_solution(solver.problem)

    prompt_input_relations = remove_trailing_empty_lines(result_dict['relations'])
    prompt_input_symbols_and_values = result_dict['symbols_and_values']
    prompt_input_description = problem_CDL['problem_text_en'].split('As shown in the diagram,')[1].strip()
    prompt_input_construction_cdl = "\n".join(problem_CDL['construction_cdl'])
    prompt_input_text_cdl = "\n".join(problem_CDL['text_cdl'])
    prompt_input_goal_cdl = problem_CDL['goal_cdl']
    theorem_seqs = problem_CDL['theorem_seqs']
    prompt_output_theorem_seqs = "\n".join(f"({i + 1};{theorem_seqs[i]})" for i in range(len(theorem_seqs)))
    prompt_output_equations = result_dict['equations']
    prompt_output_goal_symbol = result_dict['goal_value']
    prompt_output_answer = result_dict['answer']
    return {
        'prompt_input_description': prompt_input_description,
        'prompt_input_construction_cdl': prompt_input_construction_cdl,
        'prompt_input_text_cdl': prompt_input_text_cdl,
        'prompt_input_goal_cdl': prompt_input_goal_cdl,
        'prompt_input_relations': prompt_input_relations,
        'prompt_input_symbols_and_values': prompt_input_symbols_and_values,
        'prompt_output_equations': prompt_output_equations,
        'prompt_output_goal_symbol': prompt_output_goal_symbol,
        'prompt_output_answer': prompt_output_answer,
        'prompt_output_theorem_seqs': prompt_output_theorem_seqs
    }




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
    resp = call_gpt(model=model_name, messages=messages)
    print(resp)
    return resp


def generate_and_verify(prompt_path, model_name, res1, res2, max_retries=5):
    with open(prompt_path, 'r') as file:
        initial_prompt = file.read()

    initial_message = {
        "role": "user",
        "content": initial_prompt + (
            f"\nInputs for Problem A (Analogous Problem):\nDESCRIPTION:\n{res1['prompt_input_description']}\nCONSTRUCTION_CDL:\n{res1['prompt_input_construction_cdl']}\n"
            f"TEXT_CDL:\n{res1['prompt_input_text_cdl']}\nGOAL_CDL:\n{res1['prompt_input_goal_cdl']}\nRELATIONS:\n{res1['prompt_input_relations']}\nSYMBOLS_AND_VALUES:\n{res1['prompt_input_symbols_and_values']}\n"
            f"Outputs:\nOutputs for Problem A (Analogous Problem):EQUATIONS:\n{res1['prompt_output_equations']}\nGOAL_SYMBOL:\n{res1['prompt_output_goal_symbol']}\nANSWER:\n{res1['prompt_output_answer']}\nTHEOREM_SEQUENCE:\n{res1['prompt_output_theorem_seqs']}\nInputs for Problem B (To Be Solved):\nDESCRIPTION:\n{res2['prompt_input_description']}\n"
            f"CONSTRUCTION_CDL:\n{res2['prompt_input_construction_cdl']}\nTEXT_CDL:\n{res2['prompt_input_text_cdl']}\nGOAL_CDL:\n{res2['prompt_input_goal_cdl']}\n"
            f"RELATIONS:\n{res2['prompt_input_relations']}\nSYMBOLS_AND_VALUES:\n{res2['prompt_input_symbols_and_values']}\nOutputs for Problem B (Final Goal):\nEQUATIONS:\n"
        )
    }

    messages = [
        {"role": "system", "content": "You are a helpful assistant."},
        initial_message
    ]

    attempts = 0
    verifier_result = None

    while attempts < max_retries:
        resp = gpt_response(messages, model_name)
        generated_theorem_sequence = resp.split("THEOREM_SEQUENCE:\n")[1]
        generated_theorem_sequence_list = re.findall(r'\d+;([^\(\)]+\([^\)]+\))', generated_theorem_sequence)
        verifier_result = theorem_verifier(solver, generated_theorem_sequence_list)

        print("Theorem explanation")
        for t in get_theorem_seqs_expl(generated_theorem_sequence_list):
            print(t)

        if verifier_result == "Correct":
            print("Theorem sequence verified correctly")
            break

        messages.append({"role": "user", "content": f"Verifier result: {verifier_result}"})
        messages.append({"role": "user", "content": f"Generated theorem sequence: {generated_theorem_sequence}"})
        messages.append({"role": "assistant", "content": resp})

        print(f"Verifier result: {verifier_result}")
        print(f"Retry attempt: {attempts + 1}")
        attempts += 1

    return messages, resp, verifier_result



def main():

    problem2_id = 1643
    problem1_id = retrieve_similar_proof(problem2_id)

    problems = save_problems()
    problem = problems[problem1_id]
    problem.print_problem()
    display_image(problem1_id)

    problem = problems[problem2_id]
    problem.print_problem()
    display_image(problem2_id)

    res1 = parse_problem(problem1_id)
    res2 = parse_problem(problem2_id)

    prompt_path = "src/formalgeo/prompt/geometry_problem_prompt.txt"
    messages, resp, verifier_result = generate_and_verify(prompt_path, 'gpt-4o', res1, res2)
    print(resp)
    print(1)

if __name__ == "__main__":
    main()
