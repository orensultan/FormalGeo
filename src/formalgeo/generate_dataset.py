import os
import json
import re
from collections import Counter
import csv
import matplotlib.pyplot as plt
import seaborn as sns
from PIL import Image


import pandas as pd
import numpy as np
import torch
import torch.nn as nn
import torch.optim as optim
from torch.utils.data import DataLoader, TensorDataset
from sklearn.model_selection import train_test_split
from sklearn.preprocessing import StandardScaler
from sklearn.utils import resample
from sklearn.metrics import accuracy_score, confusion_matrix, precision_score, recall_score, f1_score, precision_recall_fscore_support

import re
from formalgeo.data import download_dataset, DatasetLoader
from formalgeo.solver import Interactor
from formalgeo.parse import parse_one_theorem
from formalgeo.tools import show_solution

import time
import openai

openai.api_key = "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"
openai.api_key = "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"
openai.api_key = "sk-ds-openapi-key-0sfNvLjYF3wMuFQcp7oST3BlbkFJWeqSW76sV6Gy48mjIJVK"
openai.api_key = "sk-ds-openapi-key-0sfNvLjYF3wMuFQcp7oST3BlbkFJWeqSW76sV6Gy48mjIJVK"





def replace_symbols(input_string, mapping_dict):
    # Function to replace symbols in a given text based on the dictionary
    def replace_inside_parentheses(match):
        content = match.group(1)
        # Replace all capital letters in the content
        new_content = ''.join(mapping_dict.get(char, char) for char in content)
        return f'({new_content})'

    # Pattern to find content inside parentheses
    pattern = r'\(([A-Z,]+)\)'

    # Replace the content inside parentheses
    new_string = re.sub(pattern, replace_inside_parentheses, input_string)
    return new_string

def extract_prefix(input_string):
    match = re.match(r"'?([a-zA-Z_]+)\(", input_string)
    return match.group(1) if match else None

def extract_complex_prefix(input_string):
    # This regex matches the pattern for the complex input string
    match = re.search(r"\('([a-zA-Z_]+)\(", input_string)
    return match.group(1) if match else None

def compare_prefixes(input_string1, input_string2):
    prefix1 = extract_prefix(input_string1)
    prefix2 = extract_complex_prefix(input_string2)
    return prefix1, prefix2, prefix1 == prefix2

def remove_id_first_arg(input_string):
    pattern = r'([a-zA-Z_]+)\(\d+,?(.*)\)'
    converted_string = re.sub(pattern, r'\1(\2)', input_string)
    return converted_string


def convert_shape_to_polygon(shape_str):
    if not shape_str.startswith('Shape'):
        return shape_str

    inside_parentheses = shape_str[shape_str.index('(') + 1: shape_str.index(')')]
    segments = inside_parentheses.split(',')

    points = []
    for segment in segments:
        for point in segment:
            if point not in points:
                points.append(point)

    points_str = ''.join(points)
    polygon_names = {3: 'Triangle', 4: 'Quadrilateral', 5: 'Pentagon', 6: 'Hexagon'}
    polygon_name = polygon_names.get(len(points), 'Polygon')

    polygon_str = f'{polygon_name}({points_str})'

    return polygon_str

class Problem:
    def __init__(self, id, problem_level, description, solution, construction_cdl, abstract_construction_cdl, text_cdl,
                 abstract_text_cdl, goal_cdl, abstract_goal_cdl, theorem_seqs, abstract_theorem_seqs,
                 theorem_seqs_dag, abstract_theorem_seqs_dag):
        self.id = id
        self.level = problem_level
        self.description = description
        self.solution = solution
        self.construction_cdl = construction_cdl
        self.construction = []
        self.abstract_construction_cdl = abstract_construction_cdl
        self.text_cdl = text_cdl
        self.abstract_text_cdl = abstract_text_cdl
        self.goal_cdl = goal_cdl
        self.abstract_goal_cdl = abstract_goal_cdl

        self.theorem_seqs = theorem_seqs
        self.abstract_theorem_seqs = abstract_theorem_seqs
        self.theorem_seqs_dag = theorem_seqs_dag
        self.abstract_theorem_seqs_dag = abstract_theorem_seqs_dag


    def print_problem(self):
        print('---')
        print("problem:")
        print(self.id)
        print("level:")
        print(self.level)

        print("description:")
        print(self.description)
        print("construction_cdl:")
        print(self.construction_cdl)
        for i in range(len(self.construction_cdl)):
            self.construction.append(convert_shape_to_polygon(self.construction_cdl[i]))
        print("construction:")
        print(self.construction)
        print("text_cdl:")
        print(self.text_cdl)
        print("goal_cdl:")
        print(self.goal_cdl)

        theories_set = set()
        # theorems_expl = []
        # for key, val in self.theorem_seqs_dag.items():
        #     for v in val:
        #         theory_str = str(get_theory(v))
        #         theories_set.add(theory_str)
        #         input_string1 = v
        #         input_string2 = theory_str
        #         result1 = extract_substring_first_exp(input_string1)
        #         result2 = extract_substring_second_exp(input_string2)
        #         if len(result1.replace(",", "")) != len(result2.replace(",", "")):
        #             raise ValueError("The extracted substrings must have the same length for character-level mapping.")
        #
        #         mapping_dict = {result2[i]: result1[i] for i in range(len(result2)) if result2[i].isupper()}
        #         theorems_expl.append(replace_symbols(input_string2, mapping_dict))

        for key, val in self.theorem_seqs_dag.items():
            l = []
            for v in val:
                l.append(remove_id_first_arg(v))
            self.theorem_seqs_dag[key] = l

        print("theorem_seqs_dag:")
        print(self.theorem_seqs_dag)
        print("solution: " + str(self.solution))





def display_image(problem_id):
    # Define the path to the image
    path = '../../formalgeo7k_v1/diagrams/' + str(problem_id) + '.png'

    # Check if the file exists
    if not os.path.exists(path):
        print(f"File not found: {path}")
        return

    # Open the image file
    image = Image.open(path)

    # Display the image
    plt.imshow(image)
    plt.axis('off')  # Hide the axis
    plt.show()

def remove_duplicates(theorem_seqs):
    seen = set()
    unique_res = []
    for seq in theorem_seqs:
        if seq not in seen:
            unique_res.append(seq)
            seen.add(seq)
    return unique_res

def get_abstract_theorem_seqs(theorem_seqs):
    res = []
    for seq in theorem_seqs:
        res.append(seq.split("(")[0])
    return remove_duplicates(res)

def get_abstract_theorem_seq_dag(theorem_seqs_dag):
    new_data = {}
    for key, value_list in theorem_seqs_dag.items():
        new_key = key.split('(')[0].strip()
        new_value_list = [value.split('(')[0].strip() for value in value_list]
        new_data[new_key] = new_value_list
    return new_data

def read_results_csv(file_path):
    df = pd.read_csv(file_path)
    return df

def calc_Jaccard_sim_between_multisets(l1, l2):
    # Count elements in each list
    multiset1 = Counter(l1)
    multiset2 = Counter(l2)

    # Calculate intersection: minimum of corresponding counts
    intersection = sum((multiset1 & multiset2).values())

    # Calculate union: maximum of corresponding counts
    union = sum((multiset1 | multiset2).values())

    if union == 0:
        return 0
    return intersection / union

def replace_letters_and_numbers(text):
    text = re.sub(r'\d+', '<num>', text)
    def replace_letters(match):
        return re.sub(r'\b[A-Z]+\b', '<word>', match.group(0))

    return re.sub(r'\([^\(\)]+\)', replace_letters, text)

def print_problem(json, verbose=False):
    text_cdl = json['text_cdl']
    construction_cdl = json['construction_cdl']
    goal_cdl = json['goal_cdl']

    abstract_text_cdl = [replace_letters_and_numbers(s) for s in text_cdl]
    abstract_construction_cdl = [replace_letters_and_numbers(s) for s in construction_cdl]
    abstract_goal_cdl = replace_letters_and_numbers(goal_cdl)

    abstract_theorem_seqs = get_abstract_theorem_seqs(json['theorem_seqs'])
    abstract_theorem_seq_dag = get_abstract_theorem_seq_dag(json['theorem_seqs_dag'])

    if verbose:
        print("problem id: {}".format(json['problem_id']))
        print("problem level: {}".format(json['problem_level']))
        print("problem description: {}".format(json['problem_text_en']))
        print("construction_cdl")
        print(construction_cdl)
        print("abstract_construction_cdl")
        print(abstract_construction_cdl)
        print("text_cdl")
        print(text_cdl)
        print("abstract text_cdl")
        print(abstract_text_cdl)
        print("problem goal: {}".format(goal_cdl))
        print("abstract problem goal: {}".format(abstract_goal_cdl))
        print("problem answer: {}".format(json['problem_answer']))
        print("problem theorem seqs: {}".format(json['theorem_seqs']))
        print("problem abstract theorem seqs: {}".format(abstract_theorem_seqs))
        print("problem abstract theorem seqs dag: {}".format(json['theorem_seqs_dag']))
        print("problem abstract theorem seqs dag: {}".format(abstract_theorem_seq_dag))

    return Problem(json['problem_id'], json['problem_level'], json['problem_text_en'], json['problem_answer'], construction_cdl,
                   abstract_construction_cdl, text_cdl, abstract_text_cdl, goal_cdl, abstract_goal_cdl,
                   json['theorem_seqs'], abstract_theorem_seqs, json['theorem_seqs_dag'], abstract_theorem_seq_dag)






def save_problems():
    count = 0
    problems = {}
    directory_path = '../../formalgeo7k_v1/formalgeo7k_v1/problems'
    for filename in os.listdir(directory_path):
        count += 1
        if filename.endswith('.json'):
            file_path = os.path.join(directory_path, filename)
            with open(file_path, 'r') as file:
                json_data = json.load(file)
                problem = print_problem(json_data)
                problems[problem.id] = problem
    return problems


def write_problems_proofs_similarity_dataset():
    keys = list(problems.keys())
    count = 0
    results = []
    column_names = ["problem1_id", "problem1_level", "problem2_id", "problem2_level", "abstract_construction_cdl_jaccard_similarity",
                    "abstract_text_cdl_jaccard_similarity", "abstract_goal_similarity", "abstract_theorem_seqs_jaccard_similarity"]
    for i in range(len(keys)):
        for j in range(i + 1, len(keys)):
            count += 1
            print(count)
            problem1_id, problem2_id = keys[i], keys[j]
            problem1_level, problem2_level = problems[problem1_id].level, problems[problem2_id].level
            problem1_abstract_construction_cdl, problem2_abstract_construction_cdl = problems[
                problem1_id].abstract_construction_cdl, problems[problem2_id].abstract_construction_cdl
            problem1_abstract_text_cdl, problem2_abstract_text_cdl = problems[problem1_id].abstract_text_cdl, problems[
                problem2_id].abstract_text_cdl
            problem1_abstract_goal_cdl, problem2_abstract_goal_cdl = problems[problem1_id].abstract_goal_cdl, problems[
                problem2_id].abstract_goal_cdl
            problem1_abstract_theorem_seqs, problem2_abstract_theorem_seqs = (
                problems[problem1_id].abstract_theorem_seqs, problems[problem2_id].abstract_theorem_seqs)


            abstract_construction_cdl_jaccard_similarity = calc_Jaccard_sim_between_multisets(
                problem1_abstract_construction_cdl, problem2_abstract_construction_cdl)
            print("problems construction jaccard similarity: " + str(abstract_construction_cdl_jaccard_similarity))

            abstract_text_cdl_jaccard_similarity = calc_Jaccard_sim_between_multisets(problem1_abstract_text_cdl,
                                                                                      problem2_abstract_text_cdl)
            print("problems text jaccard similarity: " + str(abstract_text_cdl_jaccard_similarity))

            abstract_goal_similarity = 1.0 if problem1_abstract_goal_cdl == problem2_abstract_goal_cdl else 0.0
            print("problems goal similarity: " + str(abstract_goal_similarity))

            abstract_theorem_seqs_jaccard_similarity = calc_Jaccard_sim_between_multisets(problem1_abstract_theorem_seqs, problem2_abstract_theorem_seqs)
            print("problems abstract theorem seqs jaccard similarity: " + str(abstract_theorem_seqs_jaccard_similarity))

            results.append([problem1_id, problem1_level, problem2_id, problem2_level, abstract_construction_cdl_jaccard_similarity,
                            abstract_text_cdl_jaccard_similarity, abstract_goal_similarity,
                            abstract_theorem_seqs_jaccard_similarity])

            print(1)
    with open('results.csv', mode='w', newline='') as file:
        writer = csv.writer(file)
        writer.writerow(column_names)
        writer.writerows(results)
    print("Data has been saved to results.csv")



class SimpleNN_old(nn.Module):
    def __init__(self, input_size, num_classes):
        super(SimpleNN, self).__init__()
        self.fc1 = nn.Linear(input_size, 128)
        self.fc2 = nn.Linear(128, 256)
        self.fc3 = nn.Linear(256, 128)
        self.fc4 = nn.Linear(128, 64)
        self.fc5 = nn.Linear(64, num_classes)

    def forward(self, x):
        x = torch.relu(self.fc1(x))
        x = torch.relu(self.fc2(x))
        x = torch.relu(self.fc3(x))
        x = torch.relu(self.fc4(x))
        x = self.fc5(x)
        return x


class SimpleNN(nn.Module):
    def __init__(self, input_size):
        super(SimpleNN, self).__init__()
        self.fc1 = nn.Linear(input_size, 64)
        self.fc2 = nn.Linear(64, 32)
        self.fc3 = nn.Linear(32, 1)

    def forward(self, x):
        x = torch.relu(self.fc1(x))
        x = torch.relu(self.fc2(x))
        x = self.fc3(x)
        return x

def make_plots(y_pred_np, y_test_np):
    plt.figure(figsize=(14, 6))

    plt.subplot(1, 2, 1)
    sns.histplot(y_pred_np, kde=True, color='blue', label='Predictions', bins=20)
    plt.title('Distribution of Predictions')
    plt.xlabel('Predicted Values')
    plt.ylabel('Frequency')
    plt.legend()

    plt.subplot(1, 2, 2)
    sns.histplot(y_test_np, kde=True, color='red', label='True Values', bins=20)
    plt.title('Distribution of True Values')
    plt.xlabel('True Values')
    plt.ylabel('Frequency')
    plt.legend()

    plt.tight_layout()
    plt.show()

    plt.figure(figsize=(14, 6))

    plt.subplot(1, 2, 1)
    sns.kdeplot(y_pred_np, color='blue', label='Predictions')
    plt.title('Density Plot of Predictions')
    plt.xlabel('Predicted Values')
    plt.ylabel('Density')
    plt.legend()

    plt.subplot(1, 2, 2)
    sns.kdeplot(y_test_np, color='red', label='True Values')
    plt.title('Density Plot of True Values')
    plt.xlabel('True Values')
    plt.ylabel('Density')
    plt.legend()

    plt.tight_layout()
    plt.show()



def print_eval_results(y_pred_bins, y_test_bins):
    accuracy = accuracy_score(y_test_bins, y_pred_bins)
    print(f'Accuracy: {accuracy:.4f}')

    conf_matrix = confusion_matrix(y_test_bins, y_pred_bins, labels=labels)
    print("Confusion Matrix:")
    print(conf_matrix)

    plt.figure(figsize=(10, 8))
    sns.heatmap(conf_matrix, annot=True, fmt='d', cmap='Blues', xticklabels=labels, yticklabels=labels)
    plt.xlabel('Predicted')
    plt.ylabel('True')
    plt.title('Confusion Matrix')
    plt.show()

    precision, recall, f1, _ = precision_recall_fscore_support(y_test_bins, y_pred_bins, labels=labels, average=None,
                                                               zero_division=0)

    for i, label in enumerate(labels):
        print(f'Precision for Class {label}: {precision[i]:.4f}')
        print(f'Recall for Class {label}: {recall[i]:.4f}')
        print(f'F1 Score for Class {label}: {f1[i]:.4f}')

    overall_precision = precision_score(y_test_bins, y_pred_bins, average='weighted', zero_division=0)
    overall_recall = recall_score(y_test_bins, y_pred_bins, average='weighted', zero_division=0)
    overall_f1 = f1_score(y_test_bins, y_pred_bins, average='weighted', zero_division=0)

    print(f'Overall Precision: {overall_precision:.4f}')
    print(f'Overall Recall: {overall_recall:.4f}')
    print(f'Overall F1 Score: {overall_f1:.4f}')


def print_mistakes(y_pred_bins, y_test_bins):
    mistakes_df = pd.DataFrame({'Predictions': y_pred_bins, 'Ground Truth': y_test_bins})
    mistakes = mistakes_df[mistakes_df['Predictions'] != mistakes_df['Ground Truth']]
    print("Num of Mistakes: " + str(len(mistakes)))
    print("Total predictions: " + str(len(mistakes_df)))
    print("Mistakes:")
    print(mistakes)


def balance_data(X, y):
    bins = [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]
    bin_labels = range(len(bins) - 1)
    y_binned = pd.cut(y, bins=bins, labels=bin_labels, include_lowest=True)

    min_bin_count = y_binned.value_counts().min()

    balanced_indices = y_binned.groupby(y_binned).apply(lambda x: x.sample(min_bin_count)).index.get_level_values(1)

    X_balanced = X.loc[balanced_indices]
    y_balanced = y.loc[balanced_indices]

    # Print distribution of the balanced data
    print("Distribution of the balanced data in bins:")
    print(pd.cut(y_balanced, bins=bins).value_counts().sort_index())

    return X_balanced, y_balanced


def data_pre_processing(X_train, y_train, X_test, y_test):
    scaler = StandardScaler()
    X_train = scaler.fit_transform(X_train)
    X_test = scaler.transform(X_test)

    X_train_tensor = torch.tensor(X_train, dtype=torch.float32)
    y_train_tensor = torch.tensor(y_train.values, dtype=torch.float32).view(-1, 1)
    X_test_tensor = torch.tensor(X_test, dtype=torch.float32)
    y_test_tensor = torch.tensor(y_test.values, dtype=torch.float32).view(-1, 1)

    train_dataset = TensorDataset(X_train_tensor, y_train_tensor)
    test_dataset = TensorDataset(X_test_tensor, y_test_tensor)

    train_loader = DataLoader(train_dataset, batch_size=32, shuffle=True)
    test_loader = DataLoader(test_dataset, batch_size=32, shuffle=False)

    return train_loader, test_loader, X_train_tensor, y_train_tensor, X_test_tensor, y_test_tensor





# def run_model_predictions_old():
#     data = pd.read_csv('results.csv')
#     X, y = data.iloc[:, -4:-1], data.iloc[:, -1]
#     data_combined = pd.concat([X, y], axis=1)
#     data_combined['bin'] = pd.cut(data_combined.iloc[:, -1], bins=bins, labels=labels, include_lowest=True, right=True)
#     print("Number of samples per bin:")
#     print(data_combined['bin'].value_counts().sort_index())
#     print("NaN values in 'bin' column:")
#     print(data_combined['bin'].isna().sum())
#     data_combined.dropna(subset=['bin'], inplace=True)
#     print("Unique values in the target variable:")
#     print(data_combined.iloc[:, -1].unique())
#
#     X_train, X_test, y_train, y_test = train_test_split(data_combined.iloc[:, :-1], data_combined['bin'], test_size=0.2,
#                                                         random_state=42)
#     print("Training set class distribution:")
#     print(y_train.value_counts().sort_index())
#     print("Test set class distribution:")
#     print(y_test.value_counts().sort_index())
#
#     X_train_downsampled, y_train_downsampled = balance_train_data(X_train, y_train)
#     train_loader, test_loader, X_train_tensor, y_train_tensor, X_test_tensor, y_test_tensor = data_pre_processing(
#         X_train_downsampled, y_train_downsampled, X_test, y_test)
#     num_classes = len(labels)
#     input_size = X_train_tensor.shape[1]
#     model = SimpleNN(input_size, num_classes)
#     criterion = nn.CrossEntropyLoss()
#     optimizer = optim.Adam(model.parameters(), lr=0.001)
#
#     model_train(train_loader, optimizer, model, criterion, num_epochs=3)
#     outputs, y_pred = model_eval(model, test_loader, criterion, X_test_tensor)
#
#     print("Predictions: ", y_pred[:100].numpy())
#     print("True values: ", y_test_tensor[:100].numpy())
#
#     y_pred_bins = pd.Categorical.from_codes(y_pred.numpy(), categories=labels)
#     y_test_bins = pd.Categorical.from_codes(y_test_tensor.numpy(), categories=labels)
#
#     print_mistakes(y_pred_bins, y_test_bins)
#
#     y_pred_bins = y_pred_bins.astype(str)
#     y_test_bins = y_test_bins.astype(str)
#     print_eval_results(y_pred_bins, y_test_bins)
#
#     y_pred_np = y_pred.numpy()
#     y_test_np = y_test_tensor.numpy()
#     make_plots(y_pred_np, y_test_np)



bins = [0.0, 0.4, 1.0]
labels = [f'{bins[i]}-{bins[i + 1]}' for i in range(len(bins) - 1)]

# def predict():
#     data = pd.read_csv('results.csv')
#     X, y = data.iloc[:, -4:-1], data.iloc[:, -1]  # Assuming the last 4 columns are features and the last column is the target
#     data_combined = pd.concat([X, y], axis=1)
#     data_combined['bin'] = pd.cut(data_combined.iloc[:, -1], bins=bins, labels=labels, include_lowest=True, right=True)
#
#     print("Number of samples per bin:")
#     print(data_combined['bin'].value_counts().sort_index())
#     print("NaN values in 'bin' column:")
#     print(data_combined['bin'].isna().sum())
#
#     data_combined.dropna(subset=['bin'], inplace=True)
#     print("Unique values in the target variable:")
#     print(data_combined.iloc[:, -1].unique())
#
#     X_train, X_test, y_train, y_test = train_test_split(data_combined.iloc[:, :-2], data_combined['bin'], test_size=0.2,
#                                                         random_state=42)
#     print("Training set class distribution:")
#     print(y_train.value_counts().sort_index())
#     print("Test set class distribution:")
#     print(y_test.value_counts().sort_index())
#
#     X_train_downsampled, y_train_downsampled = balance_train_data(X_train, y_train)
#     train_loader, test_loader, X_train_tensor, y_train_tensor, X_test_tensor, y_test_tensor = data_pre_processing(
#         X_train_downsampled, y_train_downsampled, X_test, y_test)
#     num_classes = len(labels)
#     input_size = X_train_tensor.shape[1]
#     model = SimpleNN(input_size, num_classes)
#     criterion = nn.CrossEntropyLoss()
#     optimizer = optim.Adam(model.parameters(), lr=0.001)
#
#     model_train(train_loader, optimizer, model, criterion, num_epochs=3)
#     outputs, y_pred = model_eval(model, test_loader, criterion, X_test_tensor)
#
#     print("Predictions: ", y_pred[:100].numpy())
#     print("True values: ", y_test_tensor[:100].numpy())
#
#     y_pred_bins = pd.Categorical.from_codes(y_pred.numpy(), categories=labels)
#     y_test_bins = pd.Categorical.from_codes(y_test_tensor.numpy(), categories=labels)
#
#     print_mistakes(y_pred_bins, y_test_bins)
#
#     y_pred_bins = y_pred_bins.astype(str)
#     y_test_bins = y_test_bins.astype(str)
#     print_eval_results(y_pred_bins, y_test_bins)
#
#     y_pred_np = y_pred.numpy()
#     y_test_np = y_test_tensor.numpy()
#     make_plots(y_pred_np, y_test_np)
#
#     # Save the trained model
#     torch.save(model.state_dict(), 'trained_model.pth')
#     print("Model saved to 'trained_model.pth'.")

from sklearn.metrics import mean_squared_error, r2_score





def data_pre_processing(X_train, y_train, X_test, y_test):
    scaler = StandardScaler()
    X_train = scaler.fit_transform(X_train)
    X_test = scaler.transform(X_test)

    X_train_tensor = torch.tensor(X_train, dtype=torch.float32)
    y_train_tensor = torch.tensor(y_train.values, dtype=torch.float32).view(-1, 1)
    X_test_tensor = torch.tensor(X_test, dtype=torch.float32)
    y_test_tensor = torch.tensor(y_test.values, dtype=torch.float32).view(-1, 1)

    train_dataset = TensorDataset(X_train_tensor, y_train_tensor)
    test_dataset = TensorDataset(X_test_tensor, y_test_tensor)

    train_loader = DataLoader(train_dataset, batch_size=32, shuffle=True)
    test_loader = DataLoader(test_dataset, batch_size=32, shuffle=False)

    return train_loader, test_loader, X_train_tensor, y_train_tensor, X_test_tensor, y_test_tensor


def model_train(train_loader, optimizer, model, criterion, num_epochs):
    model.train()
    for epoch in range(num_epochs):
        for X_batch, y_batch in train_loader:
            optimizer.zero_grad()
            outputs = model(X_batch)
            loss = criterion(outputs, y_batch)
            loss.backward()
            optimizer.step()
        print(f"Epoch {epoch + 1}/{num_epochs}, Loss: {loss.item()}")


def model_eval(model, test_loader, criterion, X_test_tensor, y_test_tensor):
    model.eval()
    with torch.no_grad():
        outputs = model(X_test_tensor)
        test_loss = criterion(outputs, y_test_tensor)
        y_pred = outputs.squeeze()
    return outputs, y_pred





def map_symbols(expression1, expression2):
    # Remove the number in the first expression and extract angles
    expr1_parts = expression1.split('(', 1)
    expr1_main = expr1_parts[0]
    expr1_angles = expr1_parts[1].split(',', 1)[1].rstrip(')').split(',')

    # Extract the part inside the parentheses for the second expression
    expr2_parts = expression2.split('(', 1)
    expr2_main = expr2_parts[0]
    expr2_angles = expr2_parts[1].rstrip(')').split(',')

    # Ensure the two expressions have the same number of parts to map
    if len(expr1_angles) != len(expr2_angles):
        raise ValueError("The expressions must have the same number of parts to map.")

    # Create the mapping dictionary in reverse
    reverse_mappings = {}
    for angle1, angle2 in zip(expr1_angles, expr2_angles):
        for char1, char2 in zip(angle2, angle1):
            reverse_mappings[char1] = char2

    # Create the new angle strings based on reverse mappings
    new_angle1 = ''.join([reverse_mappings[char] for char in expr2_angles[0]])
    new_angle2 = ''.join([reverse_mappings[char] for char in expr2_angles[1]])

    # Map the premise and conclusion
    premise = "Collinear(AOC)&Angle(AOB)&Angle(BOC)"
    mapped_premise = ''.join([reverse_mappings.get(char, char) for char in premise])
    conclusion = "Equal(Add(MeasureOfAngle(AOB),MeasureOfAngle(BOC)),180)"
    mapped_conclusion = ''.join([reverse_mappings.get(char, char) for char in conclusion])

    # Format the new function call
    new_function_call = f"{expr1_main}({expr1_parts[1].split(',')[0]},{new_angle1},{new_angle2})"

    # Format the final output
    result = (new_function_call, {'premise': mapped_premise, 'conclusion': [mapped_conclusion]})

    return result




run_generate_dataset = False
run_model_predictions = True
problems = save_problems()

if run_generate_dataset:
    write_problems_proofs_similarity_dataset()
if run_model_predictions:
    predict()

data = pd.read_csv('results.csv')
problem1_level = 3
problem2_level = 6
abstract_theorem_seqs_jaccard_similarity = 1.0
data = data[(data['problem1_level'] == problem1_level) & (data['problem2_level'] == problem2_level) & (data['abstract_theorem_seqs_jaccard_similarity'] == abstract_theorem_seqs_jaccard_similarity)]
print(1)
# levels = set()
# for problem_id, problem in problems.items():
#     levels.add(problems[problem_id].level)
#     # if problems[problem_id].level == 12:
#     #     print(problem_id)
#     if problem_id == 3865 or problem_id == 6105:
#         print(problem_id, problems[problem_id].level)
#
#
# 6207
# 6933

# 6722, 6634

problem1_id = 1570
problem2_id = 5536

problem = problems[problem1_id]
problem.print_problem()
display_image(problem1_id)

problem = problems[problem2_id]
problem.print_problem()
display_image(problem2_id)


def remove_trailing_empty_lines(text):
    return '\n'.join(line for line in text.splitlines() if line.strip())



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




# download_dataset(dataset_name="formalgeo7k_v1", datasets_path="../../formalgeo7k_v1")
dl = DatasetLoader(dataset_name="formalgeo7k_v1", datasets_path="../../formalgeo7k_v1/formalgeo7k_v1")
solver = Interactor(dl.predicate_GDL, dl.theorem_GDL)


res = parse_problem(problem1_id)
problem1_description, problem1_construction_cdl, problem1_text_cdl, problem1_goal_cdl, problem1_relations, problem1_theorem_seqs = res['prompt_input_description'], res['prompt_input_construction_cdl'], res['prompt_input_text_cdl'], res['prompt_input_goal_cdl'], res['prompt_input_relations'], res['prompt_output_theorem_seqs']
res = parse_problem(problem2_id)
problem2_description, problem2_construction_cdl, problem2_text_cdl, problem2_goal_cdl, problem2_relations, problem2_theorem_seqs = res['prompt_input_description'], res['prompt_input_construction_cdl'], res['prompt_input_text_cdl'], res['prompt_input_goal_cdl'], res['prompt_input_relations'],  res['prompt_output_theorem_seqs']





