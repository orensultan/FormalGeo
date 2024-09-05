from similar_proofs_model import load_model_and_predict
from similar_proofs_model import model_save_path
import numpy as np
import pandas as pd
from create_problems_proofs_similarity_dataset import save_problems
from utils import display_image



def retrieve_similar_proofs(problem_id, n=1):
    data = pd.read_csv('results.csv')
    filtered_data = data[data["problem1_id"] == problem_id]
    filtered_data["predicted_similarity"] = filtered_data.apply(
        lambda row: load_model_and_predict(
            model_save_path,
            np.array([[row["abstract_construction_cdl_jaccard_similarity"],
                       row["abstract_text_cdl_jaccard_similarity"],
                       row["abstract_goal_similarity"]]])
        ),
        axis=1
    )
    top_rows = filtered_data.sort_values(by="predicted_similarity", ascending=False).head(n)
    print("predicted similarities")
    print(top_rows['predicted_similarity'])
    print("ground truth similarities")
    print(top_rows['abstract_theorem_seqs_jaccard_similarity'])

    return top_rows["problem2_id"].values.tolist()


def main():
    retrieve_similar_proof(6800)


if __name__ == "__main__":
    main()

