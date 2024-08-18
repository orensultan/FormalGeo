import re
from formalgeo.data import download_dataset, DatasetLoader
from formalgeo.solver import Interactor
from formalgeo.parse import parse_one_theorem
from formalgeo.tools import show_solution

from create_problems_proofs_similarity_dataset import save_problems
import time
import openai

openai.api_key = "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"
openai.api_key = "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"
openai.api_key = "sk-ds-openapi-key-0sfNvLjYF3wMuFQcp7oST3BlbkFJWeqSW76sV6Gy48mjIJVK"
openai.api_key = "sk-ds-openapi-key-0sfNvLjYF3wMuFQcp7oST3BlbkFJWeqSW76sV6Gy48mjIJVK"

from utils import display_image

dl = DatasetLoader(dataset_name="formalgeo7k_v1", datasets_path="formalgeo7k_v1")
solver = Interactor(dl.predicate_GDL, dl.theorem_GDL)




def remove_trailing_empty_lines(text):
    return '\n'.join(line for line in text.splitlines() if line.strip())

def theorem_verifier(solver, theorem_seqs):
    res = "Correct"

    for theorem in theorem_seqs:
        t_name, t_branch, t_para = parse_one_theorem(theorem)
        try:
            solver.apply_theorem(t_name, t_branch, t_para)
        except Exception as e:
            res = str(e) + " Theorem sequence step: " + theorem
    return res


def parse_problem(pid):
    problem_CDL = dl.get_problem(pid)
    solver.load_problem(problem_CDL)

    prompt_input_relations = remove_trailing_empty_lines(show_solution(solver.problem))
    prompt_input_description = problem_CDL['problem_text_en'].split('As shown in the diagram,')[1].strip()
    prompt_input_construction_cdl = "\n".join(problem_CDL['construction_cdl'])
    prompt_input_text_cdl = "\n".join(problem_CDL['text_cdl'])
    prompt_input_goal_cdl = problem_CDL['goal_cdl']
    theorem_seqs = problem_CDL['theorem_seqs']
    prompt_output_theorem_seqs = "\n".join(f"({i + 1};{theorem_seqs[i]})" for i in range(len(theorem_seqs)))

    return {
        'prompt_input_description': prompt_input_description,
        'prompt_input_construction_cdl': prompt_input_construction_cdl,
        'prompt_input_text_cdl': prompt_input_text_cdl,
        'prompt_input_goal_cdl': prompt_input_goal_cdl,
        'prompt_input_relations': prompt_input_relations,
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


def generate_and_verify(prompt_path, model_name, max_retries=5):
    with open(prompt_path, 'r') as file:
        initial_prompt = file.read()

    initial_message = {
        "role": "user",
        "content": initial_prompt + (
            f"\nDESCRIPTION:\n{problem1_description}\nCONSTRUCTION_CDL:\n{problem1_construction_cdl}\n"
            f"TEXT_CDL:\n{problem1_text_cdl}\nGOAL_CDL:\n{problem1_goal_cdl}\nRELATIONS:\n{problem1_relations}\n"
            f"Outputs:\nTHEOREM_SEQUENCE:\n{problem1_theorem_seqs}\nInputs:\nDESCRIPTION:\n{problem2_construction_cdl}\n"
            f"CONSTRUCTION_CDL:\n{problem2_construction_cdl}\nTEXT_CDL:\n{problem2_text_cdl}\nGOAL_CDL:\n{problem2_goal_cdl}\n"
            f"RELATIONS:\n{problem2_relations}\nOutputs:\nTHEOREM_SEQUENCE:\n"
        )
    }

    messages = [
        {"role": "system", "content": "You are a helpful assistant."},
        initial_message
    ]

    attempts = 0
    verifier_result = None

    while attempts <= max_retries:
        resp = gpt_response(messages, model_name)
        generated_theorem_sequence = resp.split("THEOREM_SEQUENCE:\n")[1]
        generated_theorem_sequence_list = re.findall(r'\d+;([^\(\)]+\([^\)]+\))', generated_theorem_sequence)
        verifier_result = theorem_verifier(solver, generated_theorem_sequence_list)

        if verifier_result == "Correct":
            print("Theorem sequence verified correctly")
            break

        messages.append({"role": "user", "content": f"Generated theorem sequence: {generated_theorem_sequence}"})
        messages.append({"role": "user", "content": f"Verifier result: {verifier_result}"})
        messages.append({"role": "user", "content": resp})

        print(f"Verifier result: {verifier_result}")
        print(f"Retry attempt: {attempts + 1}")
        attempts += 1

    return messages, resp, verifier_result



def main():
    problem1_id = 1570
    problem2_id = 5536

    problems = save_problems()
    problem = problems[problem1_id]
    problem.print_problem()
    display_image(problem1_id)

    problem = problems[problem2_id]
    problem.print_problem()
    display_image(problem2_id)

    res = parse_problem(problem1_id)
    problem1_description, problem1_construction_cdl, problem1_text_cdl, problem1_goal_cdl, problem1_relations, problem1_theorem_seqs = \
    res['prompt_input_description'], res['prompt_input_construction_cdl'], res['prompt_input_text_cdl'], res[
        'prompt_input_goal_cdl'], res['prompt_input_relations'], res['prompt_output_theorem_seqs']
    res = parse_problem(problem2_id)
    problem2_description, problem2_construction_cdl, problem2_text_cdl, problem2_goal_cdl, problem2_relations, problem2_theorem_seqs = \
    res['prompt_input_description'], res['prompt_input_construction_cdl'], res['prompt_input_text_cdl'], res[
        'prompt_input_goal_cdl'], res['prompt_input_relations'], res['prompt_output_theorem_seqs']

    print(1)

if __name__ == "__main__":
    main()
