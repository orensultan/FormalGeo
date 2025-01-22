from formalgeo.data import download_dataset, DatasetLoader
from formalgeo.solver import Interactor
from formalgeo.parse import parse_theorem_seqs
from formalgeo.tools import show_solution


import time
import openai

openai.api_key = "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"
openai.api_key = "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"
openai.api_key = "sk-ds-openapi-key-0sfNvLjYF3wMuFQcp7oST3BlbkFJWeqSW76sV6Gy48mjIJVK"
openai.api_key = "sk-ds-openapi-key-0sfNvLjYF3wMuFQcp7oST3BlbkFJWeqSW76sV6Gy48mjIJVK"



# download_dataset(dataset_name="formalgeo7k_v1", datasets_path=".")
dl = DatasetLoader(dataset_name="formalgeo7k_v1", datasets_path="formalgeo7k_v1")
solver = Interactor(dl.predicate_GDL, dl.theorem_GDL)
problem_CDL = dl.get_problem(pid=5232)
solver.load_problem(problem_CDL)
for t_name, t_branch, t_para in parse_theorem_seqs(problem_CDL["theorem_seqs"]):
    solver.apply_theorem(t_name, t_branch, t_para)
solver.problem.check_goal()
show_solution(solver.problem)
print(1)


def call_gpt(model, prompt, temperature=0, wait_time=1, retry_wait_time=6, max_retries=10):
    retries = 0
    while retries <= max_retries:
        try:
            response = openai.ChatCompletion.create(
                model=model,
                messages=[
                    {"role": "system", "content": "You are a helpful assistant."},
                    {"role": "user", "content": prompt},
                ],
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


def print_gpt_response(prompt_path, model_name):
    with open(prompt_path, 'r') as file:
        prompt = file.read()
    resp = call_gpt(model=model_name, prompt=prompt)
    print(resp)

prompt_path = 'src/formalgeo/prompt/geometry_problem_prompt.txt'
model_name = 'gpt-4o-mini'
# print_gpt_response(prompt_path, model_name)