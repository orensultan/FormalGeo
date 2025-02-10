import json
import os
from formalgeo.data import download_dataset, DatasetLoader

from LLM_analogy_based_solver import get_processed_model_resp, process_problem

from Problem import get_theorem, replace_symbols
from create_problems_proofs_similarity_dataset import save_problems
from formalgeo.solver import Interactor

from src.formalgeo.verifier.verifier import Verifier

dl = DatasetLoader(dataset_name="formalgeo7k_v1", datasets_path="formalgeo7k_v1")
solver = Interactor(dl.predicate_GDL, dl.theorem_GDL)





def read_llm_resp(file_path):
    with open(file_path, 'r', encoding='utf-8') as file:
        lines = file.readlines()

    start_marker = "EQUATIONS:"
    end_marker = "GT_EQUATIONS:"
    extracting = False
    extracted_text = []

    for line in lines:
        if line.strip() == start_marker:
            extracting = True
        if extracting and line.strip():  # Omit empty lines
            extracted_text.append(line.strip())
        if line.strip() == end_marker:
            break

    return "\n".join(extracted_text[:-1])  # Exclude the last line of GT_EQUATIONS

def read_gt(file_path):
    with open(file_path, 'r', encoding='utf-8') as file:
        lines = file.readlines()

    start_marker = "GT_EQUATIONS:"
    extracting = False
    extracted_text = []

    for line in lines:
        if line.strip() == start_marker:
            extracting = True
        if extracting:  # Keep extracting until the end
            extracted_text.append(line.strip())

    return "\n".join(extracted_text)






problems = [2833, 6523, 2999, 2425, 4908, 729, 683, 912, 5749,
            1975, 1490, 1726, 178, 2669, 2614, 51, 2323, 192, 2624,
            2141, 69, 2916, 358, 4473, 4483, 5645, 127, 2410, 4523,
            4187, 5244, 5062, 844, 1945,
            2114, 464, 5510, 3272, 5230,
            5440, 6485, 696, 847, 5563,
            4923, 3298, 759, 4910, 5805,
            4898, 6802, 6247, 449,
            3983, 2761, 2875, 3434, 6806,
            4892, 5092, 5522, 4796, 3418]



verifier_results_path = os.path.join("verifier_results", "verification_results.txt")

for problem_id in problems:
    variant = "analogy_based"
    model = "o1"
    file_path = "results/variant_" + variant + "_model_" + model + "_problem_" + str(problem_id) + ".txt"
    resp = read_llm_resp(file_path)
    # resp = read_gt(file_path)
    generated_theorem_sequence_list = get_processed_model_resp(resp)
    verifier = Verifier(problem_id, generated_theorem_sequence_list)
    theorem_verifier_result = verifier.verify()
    with open(verifier_results_path, "a") as f:  # Use "a" to append results
        f.write(f"problem_id: {problem_id}: {theorem_verifier_result}\n")




