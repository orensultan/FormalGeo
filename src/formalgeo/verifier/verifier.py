from formalgeo.data import DatasetLoader
from formalgeo.parse import parse_one_theorem
from formalgeo.solver import Interactor
from Problem import get_theorem, replace_symbols
import json
import ast
dl = DatasetLoader(dataset_name="formalgeo7k_v1", datasets_path="formalgeo7k_v1")

def convert_theorem_seqs_format_string(input_str):
    # Remove leading and trailing single quotes if present
    input_str = input_str.strip("'")

    # Split the input string by lines
    lines = input_str.strip().splitlines()

    converted_list = []

    for line in lines:
        line = line.strip()
        if line.startswith("step_id:"):
            # Split the line by ';' and extract labeled parts
            parts = [part.split(":", 1)[1].strip() for part in line.split(";") if ":" in part]
        else:
            # Assume the line is unlabeled and split by ';'
            parts = [part.strip() for part in line.split(";")]

        step_id = parts[0] if len(parts) > 0 else ""
        theorem = parts[1] if len(parts) > 1 else ""
        premise = parts[2] if len(parts) > 2 else ""
        conclusion = parts[3] if len(parts) > 3 else ""

        converted_list.append(f"{step_id};{theorem};{premise};{conclusion}")

    return "\n".join(converted_list)


def get_processed_model_resp(resp):
    """Process model response and return list of (theorem, premises, conclusions) triplets."""
    generated_theorem_sequence = resp.split("THEOREM_SEQUENCE:\n")[1] if len(resp.split("THEOREM_SEQUENCE:\n")) > 1 else ""
    generated_theorem_sequence = convert_theorem_seqs_format_string(generated_theorem_sequence) if generated_theorem_sequence != "" else ""
    
    if generated_theorem_sequence == "":
        return []
    
    # Process each line into a triplet
    triplets = []
    for line in generated_theorem_sequence.strip().split("\n"):
        parts = line.split(";")
        if len(parts) >= 3:
            theorem = parts[1].strip()
            premises = parts[2].strip()
            conclusions = parts[3].strip() if len(parts) > 3 else "[]"
            triplets.append((theorem, premises, conclusions))
    
    return triplets


class Verifier:
    def __init__(self, problem_id, resp):
        self.resp = resp
        self.solver = Interactor(dl.predicate_GDL, dl.theorem_GDL)
        self.solver.load_problem(dl.get_problem(problem_id))
        self.theorem_seqs = get_processed_model_resp(resp)
        self.gdl_dict = dl.theorem_GDL

    def get_letters(self, t_name, t_para):
        letters = {}
        for i in range(len(self.solver.parsed_theorem_GDL[t_name]["vars"])):
            key = self.solver.parsed_theorem_GDL[t_name]["vars"][i].upper()
            letters[key] = t_para[i]
        return letters


    def verify_symbols_syntax(self):
        if len(self.theorem_seqs) == 0:
            return "Verification failed. The THEOREM_SEQUENCE you provided is empty. Please generate a proof again, using the similar problems I provided (A1, A2, A3, A4, A5), along with the GDL_DICTIONARY of theorems."
        for theorem, model_premises, model_conclusions in self.theorem_seqs:
            t_name, t_branch, t_para = parse_one_theorem(theorem)
            tier1_verification_result = self.solver.verify_tier1(t_name, t_branch, t_para)
            if tier1_verification_result != "Success":
                return "Verification failed. " + tier1_verification_result
            letters = self.get_letters(t_name, t_para)
            theory_json = get_theorem(theorem)
            premises, conclusions = json.loads(theory_json)['premise'], json.loads(theory_json)['conclusion']
            premises = replace_symbols(premises, letters)
            if model_premises != premises:
                return f"Verification failed. Premises mismatch:\nModel premises: {model_premises}\nExpected premises: {premises}"
            for i in range(len(conclusions)):
                conclusions[i] = replace_symbols(conclusions[i], letters)
                if ast.literal_eval(model_conclusions)[i] != conclusions[i]:
                    return f"Verification failed. Conclusions mismatch:\nModel conclusions: {ast.literal_eval(model_conclusions)[i]}\nExpected conclusions: {conclusions[i]}"

        return "Success"