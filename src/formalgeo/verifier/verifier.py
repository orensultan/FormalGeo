from formalgeo.data import DatasetLoader
from formalgeo.parse import parse_one_theorem
from formalgeo.solver import Interactor
dl = DatasetLoader(dataset_name="formalgeo7k_v1", datasets_path="formalgeo7k_v1")


class Verifier:
    def __init__(self, problem_id, theorem_seqs):
        self.theorem_seqs = theorem_seqs
        self.solver = Interactor(dl.predicate_GDL, dl.theorem_GDL)
        self.solver.load_problem(dl.get_problem(problem_id))

    def verify(self):
        if len(self.theorem_seqs) == 0:
            return "Verification failed. The THEOREM_SEQUENCE you provided is empty. Please generate a proof again, using the similar problems I provided (A1, A2, A3, A4, A5), along with the GDL_DICTIONARY of theorems."
        for theorem in self.theorem_seqs:
            t_name, t_branch, t_para = parse_one_theorem(theorem)
            tier1_verification_result = self.solver.verify_tier1(t_name, t_branch, t_para)
            if tier1_verification_result != "Success":
                return "Tier1 error. " + tier1_verification_result
            # update, tier2_verification_result = self.solver.verify_tier2(t_name, t_branch, t_para)
            # if tier2_verification_result != "Success":
            #     return "Tier2 error. " + tier2_verification_result
        return "Success"