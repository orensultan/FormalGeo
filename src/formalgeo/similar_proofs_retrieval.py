from similar_proofs_model import load_model_and_predict
from similar_proofs_model import model_save_path
import numpy as np
import pandas as pd

problems_similarity_csv = 'problems_similarity_results.csv'

def retrieve_random_proofs(problem_id, n=1):
    data = pd.read_csv(problems_similarity_csv)

    # Filter rows where the given problem_id appears in either problem1_id or problem2_id
    filtered_data = data[(data["problem1_id"] == problem_id) | (data["problem2_id"] == problem_id)]

    # Compute predicted similarity
    filtered_data["predicted_similarity"] = filtered_data.apply(
        lambda row: load_model_and_predict(
            model_save_path,
            np.array([[row["abstract_construction_cdl_jaccard_similarity"],
                       row["abstract_text_cdl_jaccard_similarity"],
                       row["abstract_goal_similarity"]]])
        ),
        axis=1
    )

    print(f"Filtered data size: {len(filtered_data)}")

    # Sample randomly from the filtered data
    top_rows = filtered_data.sample(n=min(n, len(filtered_data)), random_state=42)

    print("predicted similarities")
    print(top_rows['predicted_similarity'])
    print("ground truth similarities")
    print(top_rows['abstract_theorem_seqs_jaccard_similarity'])

    # Return the other problem id from each row, cast to int
    random_problem_ids = [
        int(row["problem2_id"]) if row["problem1_id"] == problem_id else int(row["problem1_id"])
        for _, row in top_rows.iterrows()
    ]

    return random_problem_ids



def retrieve_similar_proofs(problem_id, n=1):
    data = pd.read_csv(problems_similarity_csv)

    # Filter rows where the given problem_id appears in either problem1_id or problem2_id
    filtered_data = data[(data["problem1_id"] == problem_id) | (data["problem2_id"] == problem_id)]

    # Compute predicted similarity
    filtered_data["predicted_similarity"] = filtered_data.apply(
        lambda row: load_model_and_predict(
            model_save_path,
            np.array([[row["abstract_construction_cdl_jaccard_similarity"],
                       row["abstract_text_cdl_jaccard_similarity"],
                       row["abstract_goal_similarity"]]])
        ),
        axis=1
    )

    # Sort by predicted similarity and take top n
    top_rows = filtered_data.sort_values(by="predicted_similarity", ascending=False).head(n)

    print("predicted similarities")
    print(top_rows['predicted_similarity'])
    print("ground truth similarities")
    print(top_rows['abstract_theorem_seqs_jaccard_similarity'])

    # Return the other problem id from each row, cast to int
    similar_problem_ids = [
        int(row["problem2_id"]) if row["problem1_id"] == problem_id else int(row["problem1_id"])
        for _, row in top_rows.iterrows()
    ]

    return similar_problem_ids




def main():
    data = pd.read_csv(problems_similarity_csv)
    print(1)

if __name__ == "__main__":
    main()

