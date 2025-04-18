    def verify_tier1(self, t_name, t_branch=None, t_para=None):
        if self.problem is None:
            e_msg = "Problem not loaded. Please run <load_problem> before run <apply_theorem>."
            raise Exception(e_msg)
        if t_name not in self.parsed_theorem_GDL:
            e_msg = "Theorem '{}' not defined in current GDL. Please rewrite the proof sequence, you are allowed to use only theorems from the GDL.".format(t_name)
            return e_msg
        if t_para is not None and len(t_para) != len(self.parsed_theorem_GDL[t_name]["vars"]):
            e_msg = "Theorem <{}> para length error. Expected {} but got {}.".format(
                t_name, len(self.parsed_theorem_GDL[t_name]["vars"]), t_para)
            return e_msg
        if t_branch is None or t_branch not in self.parsed_theorem_GDL[t_name]["body"]:
            e_msg = "Theorem <{}> branch error. Expected {} but got {}. Please rewrite your response, you should change only the call to theorem <{}> by adding the branch number from the dict_keys as the first argument".format(
                t_name, self.parsed_theorem_GDL[t_name]["body"].keys(), t_branch, t_name)
            return e_msg
        return "Success" 