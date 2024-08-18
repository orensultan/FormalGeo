from similar_proofs_model import load_model_and_predict
from similar_proofs_model import model_save_path
import numpy as np
import pandas as pd
from create_problems_proofs_similarity_dataset import save_problems
from utils import display_image





def main():
    data = pd.read_csv('results.csv')
    problem1_id = 6800
    filtered_data = data[data["problem1_id"] == problem1_id]
    filtered_data["predicted_similarity"] = filtered_data.apply(
        lambda row: load_model_and_predict(
            model_save_path,
            np.array([[row["abstract_construction_cdl_jaccard_similarity"],
                       row["abstract_text_cdl_jaccard_similarity"],
                       row["abstract_goal_similarity"]]])
        ),
        axis=1
    )
    top_row = filtered_data.sort_values(by="predicted_similarity", ascending=False).head(1)
    print("predicted similarity")
    print(top_row['predicted_similarity'])
    print("ground truth similarity")
    print(top_row['abstract_theorem_seqs_jaccard_similarity'])

    problem1_id = top_row["problem1_id"].values[0]
    problem2_id = top_row["problem2_id"].values[0]

    problems = save_problems()

    problem = problems[problem1_id]
    problem.print_problem()
    display_image(problem1_id)

    problem = problems[problem2_id]
    problem.print_problem()
    display_image(problem2_id)

if __name__ == "__main__":
    main()

