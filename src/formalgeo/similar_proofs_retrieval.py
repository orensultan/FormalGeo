from similar_proofs_model import load_model_and_predict
from similar_proofs_model import model_save_path
import numpy as np
import pandas as pd
from create_problems_proofs_similarity_dataset import save_problems
from utils import display_image



def retrieve_similar_proof(problem_id):
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
    top_row = filtered_data.sort_values(by="predicted_similarity", ascending=False).head(1)
    print("predicted similarity")
    print(top_row['predicted_similarity'])
    print("ground truth similarity")
    print(top_row['abstract_theorem_seqs_jaccard_similarity'])

    return top_row["problem2_id"].values[0]


def main():
    retrieve_similar_proof(6800)


if __name__ == "__main__":
    main()

