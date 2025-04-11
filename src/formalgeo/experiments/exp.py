import matplotlib.pyplot as plt
import numpy as np
import os
import re
from collections import defaultdict
import json
from src.formalgeo.config.config import MAX_RUNS, MAX_RETRIES_IN_RUN
import math


def evaluate_expression(expr):
    """Evaluate a mathematical expression string."""
    try:
        # Handle special cases
        if expr.lower() == 'none' or expr.lower() == 'null':
            return None

        # Replace sqrt with math.sqrt
        expr = expr.replace('sqrt', 'math.sqrt')

        # Handle implicit multiplication
        expr = re.sub(r'(\d+)([a-zA-Z(])', r'\1*\2', expr)

        # Evaluate the expression with math module
        result = eval(expr, {"math": math})
        return round(result, 6)  # Round to 6 decimal places for comparison
    except:
        return None


def convert_to_float(number_str):
    """Convert a number string to float, handling fractions and expressions."""
    try:
        # First try to evaluate as an expression
        expr_result = evaluate_expression(number_str)
        if expr_result is not None:
            return expr_result

        # If not an expression, try fraction
        if '/' in number_str:
            numerator, denominator = number_str.split('/')
            return round(float(numerator) / float(denominator), 6)

        # If not a fraction, try direct float conversion
        return round(float(number_str), 6)
    except (ValueError, ZeroDivisionError):
        return None


def calculate_success_rates(base_path):
    results = defaultdict(lambda: defaultdict(dict))
    for level in range(1, 3):
        level_dir = os.path.join(base_path, f"level_{level}")
        if not os.path.exists(level_dir):
            continue

        # Initialize counters for each variant
        variant_stats = {
            "variant_analogy_based_model_o1": {
                "total_problems": 0,
                "successful_answers_first_try": 0,
                "successful_answers_with_retries": 0,
                "successful_theorems_first_try": 0,
                "successful_theorems_with_retries": 0
            },
            "variant_random_all_theorems_model_o1": {
                "total_problems": 0,
                "successful_answers_first_try": 0,
                "successful_answers_with_retries": 0,
                "successful_theorems_first_try": 0,
                "successful_theorems_with_retries": 0
            }
        }

        # Group files by variant and problem_id
        problem_groups = defaultdict(lambda: defaultdict(list))
        for result_file in os.listdir(level_dir):
            if not result_file.endswith('.txt'):
                continue

            # Extract variant and problem_id
            variant = None
            for v in variant_stats.keys():
                if result_file.startswith(v):
                    variant = v
                    break

            if variant is None:
                continue

            # Extract problem_id from filename
            problem_match = re.search(r'problem_(\d+)_run_', result_file)
            if not problem_match:
                continue

            problem_id = problem_match.group(1)
            problem_groups[variant][problem_id].append(result_file)

        # Process each problem group
        for variant, problems in problem_groups.items():
            for problem_id, files in problems.items():
                variant_stats[variant]["total_problems"] += 1

                # Track if any run succeeded for this problem
                any_answer_correct = False
                any_first_try_success = False
                any_theorem_success = False

                print(f"\nProcessing problem {problem_id} for {variant}")

                # Get GT_ANSWER from any file (they should all have the same GT_ANSWER)
                gt_answer = None
                gt_answer_float = None
                for result_file in files:
                    file_path = os.path.join(level_dir, result_file)
                    with open(file_path, 'r') as f:
                        lines = f.readlines()
                        for i, line in enumerate(lines):
                            if line.strip() == "GT_ANSWER:":
                                if i + 1 < len(lines):
                                    gt_answer = lines[i + 1].strip()
                                    gt_answer_float = convert_to_float(gt_answer)
                                    print(f"Found GT_ANSWER in {result_file}: {gt_answer} -> {gt_answer_float}")
                                    break

                if gt_answer_float is None:
                    print(f"Warning: No GT_ANSWER found for problem {problem_id}")
                    continue

                # Find run_0 file for first try check
                run_0_file = None
                for result_file in files:
                    if 'run_0' in result_file:
                        run_0_file = result_file
                        break

                if run_0_file:
                    file_path = os.path.join(level_dir, run_0_file)
                    with open(file_path, 'r') as f:
                        lines = f.readlines()

                        # Check for RETRY_ANSWER in the entire file
                        retry_answer = None
                        retry_answer_float = None
                        print(f"Looking for RETRY_ANSWER in {run_0_file}...")
                        for i, line in enumerate(lines):
                            if line.strip() == "RETRY_ANSWER:":
                                if i + 1 < len(lines):
                                    retry_answer = lines[i + 1].strip()
                                    retry_answer_float = convert_to_float(retry_answer)
                                    print(f"Found RETRY_ANSWER in {run_0_file}: {retry_answer} -> {retry_answer_float}")
                                    print(f"GT_ANSWER: {gt_answer} -> {gt_answer_float}")
                                    if retry_answer_float is not None and retry_answer_float == gt_answer_float:
                                        print(
                                            f"Setting first try success for {run_0_file} due to matching RETRY_ANSWER")
                                        any_first_try_success = True
                                        any_answer_correct = True
                                    break

                        # Only check ANSWER in model response section if no RETRY_ANSWER was found
                        if retry_answer_float is None:
                            print(
                                f"No RETRY_ANSWER found in {run_0_file}, checking for ANSWER in model response section...")

                            # Find model response section
                            model_response_start = -1
                            model_response_end = -1
                            for i, line in enumerate(lines):
                                if line.strip() == "***MODEL_RESPONSE_BEGIN***":
                                    model_response_start = i
                                elif line.strip() == "***MODEL_RESPONSE_END***":
                                    model_response_end = i
                                    break

                            if model_response_start != -1 and model_response_end != -1:
                                model_response = lines[model_response_start:model_response_end + 1]

                                answer = None
                                answer_float = None
                                for i, line in enumerate(model_response):
                                    if line.strip() == "ANSWER:":
                                        if i + 1 < len(model_response):
                                            answer = model_response[i + 1].strip()
                                            answer_float = convert_to_float(answer)
                                            print(
                                                f"Found ANSWER in model response section of {run_0_file}: {answer} -> {answer_float}")
                                            break

                                if answer_float is not None and answer_float == gt_answer_float:
                                    print(f"Setting first try success for {run_0_file} due to matching ANSWER")
                                    any_first_try_success = True
                                    any_answer_correct = True

                        # Check for theorem sequence success (first try) in run_0
                        retries = None
                        runs = None
                        print(f"\nChecking theorem sequence success for {run_0_file}:")

                        # Find RETRIES_MESSAGES section
                        retries_messages_start = -1
                        for i, line in enumerate(lines):
                            if line.strip() == "RETRIES_MESSAGES:":
                                retries_messages_start = i
                                break

                        if retries_messages_start != -1:
                            # Look for RETRIES and RUNS in RETRIES_MESSAGES section
                            for i, line in enumerate(lines[retries_messages_start:]):
                                if line.strip() == "#RETRIES:":
                                    try:
                                        # Get the next line for the value
                                        if i + 1 < len(lines[retries_messages_start:]):
                                            retries_str = lines[retries_messages_start + i + 1].strip()
                                            retries = int(retries_str)
                                            print(f"  Found RETRIES line: {line.strip()}")
                                            print(f"  Parsed RETRIES value: {retries}")
                                    except (ValueError, IndexError):
                                        print(f"  Error parsing RETRIES from line: {line.strip()}")
                                        continue
                                elif line.strip() == "#RUNS:":
                                    try:
                                        # Get the next line for the value
                                        if i + 1 < len(lines[retries_messages_start:]):
                                            runs_str = lines[retries_messages_start + i + 1].strip()
                                            runs = int(runs_str)
                                            print(f"  Found RUNS line: {line.strip()}")
                                            print(f"  Parsed RUNS value: {runs}")
                                    except (ValueError, IndexError):
                                        print(f"  Error parsing RUNS from line: {line.strip()}")
                                        continue

                        print(f"  Final values - RETRIES: {retries}, RUNS: {runs}")

                        # Only count as success if both RETRIES and RUNS are 0
                        if retries is not None and runs is not None:
                            if retries == 0 and runs == 0:
                                print(
                                    f"  Setting theorem sequence first try success for {run_0_file} due to RETRIES=0 and RUNS=0")
                                any_theorem_success = True
                            else:
                                print(
                                    f"  No theorem sequence first try success for {run_0_file} - RETRIES={retries}, RUNS={runs}")
                        else:
                            print(f"  Missing RETRIES or RUNS in {run_0_file}")

                print(f"Problem {problem_id} final flags:")
                print(f"any_first_try_success: {any_first_try_success}")
                print(f"any_answer_correct: {any_answer_correct}")
                print(f"any_theorem_success: {any_theorem_success}")

                # Update counters based on problem-level success
                if any_first_try_success:
                    variant_stats[variant]["successful_answers_first_try"] += 1
                    print(f"Incrementing first try success counter for {variant}")

                if any_theorem_success:
                    variant_stats[variant]["successful_theorems_first_try"] += 1
                    print(f"Incrementing theorem sequence first try success counter for {variant}")

                # Check for theorem sequence success with verifier feedback
                theorem_with_retries_success = True

                # Check if last run exists and has max retries
                last_run = f"run_{MAX_RUNS - 1}"
                for result_file in files:
                    if last_run in result_file:
                        file_path = os.path.join(level_dir, result_file)
                        with open(file_path, 'r') as f:
                            lines = f.readlines()
                            for i, line in enumerate(lines):
                                if line.strip() == "#RETRIES:":
                                    if i + 1 < len(lines):
                                        retries_str = lines[i + 1].strip()
                                        if retries_str:
                                            retries = int(retries_str)
                                            if retries == MAX_RETRIES_IN_RUN:
                                                print(f"Found max retries in {result_file}, setting failure")
                                                theorem_with_retries_success = False
                                                break

                if theorem_with_retries_success:
                    variant_stats[variant]["successful_theorems_with_retries"] += 1
                    print(f"Incrementing theorem sequence with retries success counter for {variant}")

                # Process all runs for answer success with retries
                for result_file in files:
                    file_path = os.path.join(level_dir, result_file)
                    with open(file_path, 'r') as f:
                        lines = f.readlines()

                        # Check for RETRY_ANSWER in the entire file
                        retry_answer = None
                        retry_answer_float = None
                        print(f"Looking for RETRY_ANSWER in {result_file}...")
                        for i, line in enumerate(lines):
                            if line.strip() == "RETRY_ANSWER:":
                                if i + 1 < len(lines):
                                    retry_answer = lines[i + 1].strip()
                                    retry_answer_float = convert_to_float(retry_answer)
                                    print(
                                        f"Found RETRY_ANSWER in {result_file}: {retry_answer} -> {retry_answer_float}")
                                    print(f"GT_ANSWER: {gt_answer} -> {gt_answer_float}")
                                    if retry_answer_float is not None and retry_answer_float == gt_answer_float:
                                        print(
                                            f"Setting with retries success for {result_file} due to matching RETRY_ANSWER")
                                        any_answer_correct = True
                                        break

                        # If no RETRY_ANSWER found, check for ANSWER in model response section
                        if not any_answer_correct:
                            print(
                                f"No matching RETRY_ANSWER found in {result_file}, checking for ANSWER in model response section...")

                            # Find model response section
                            model_response_start = -1
                            model_response_end = -1
                            for i, line in enumerate(lines):
                                if line.strip() == "***MODEL_RESPONSE_BEGIN***":
                                    model_response_start = i
                                elif line.strip() == "***MODEL_RESPONSE_END***":
                                    model_response_end = i
                                    break

                            if model_response_start != -1 and model_response_end != -1:
                                model_response = lines[model_response_start:model_response_end + 1]

                                answer = None
                                answer_float = None
                                for i, line in enumerate(model_response):
                                    if line.strip() == "ANSWER:":
                                        if i + 1 < len(model_response):
                                            answer = model_response[i + 1].strip()
                                            answer_float = convert_to_float(answer)
                                            print(
                                                f"Found ANSWER in model response section of {result_file}: {answer} -> {answer_float}")
                                            break

                                if answer_float is not None and answer_float == gt_answer_float:
                                    print(f"Setting with retries success for {result_file} due to matching ANSWER")
                                    any_answer_correct = True

                        # If we found a matching answer, no need to check other files
                        if any_answer_correct:
                            break

                # Update counter for answer success with retries
                if any_answer_correct:
                    variant_stats[variant]["successful_answers_with_retries"] += 1
                    print(f"Incrementing with retries success counter for {variant}")

        # Calculate and store success rates for each variant
        for variant, stats in variant_stats.items():
            total_problems = stats["total_problems"]

            # Answer success rates
            answer_success_rate_first_try = stats[
                                                "successful_answers_first_try"] / total_problems if total_problems > 0 else 0
            answer_success_rate_with_retries = stats[
                                                   "successful_answers_with_retries"] / total_problems if total_problems > 0 else 0

            # Theorem sequence success rates
            theorem_success_rate_first_try = stats[
                                                 "successful_theorems_first_try"] / total_problems if total_problems > 0 else 0
            theorem_success_rate_with_retries = stats[
                                                    "successful_theorems_with_retries"] / total_problems if total_problems > 0 else 0

            results[f"level{level}"][variant] = {
                "success_rate_answer_first_try": answer_success_rate_first_try,
                "success_rate_answer_with_retries": answer_success_rate_with_retries,
                "success_rate_theorem_sequence_first_try": theorem_success_rate_first_try,
                "success_rate_theorem_sequence_with_retries": theorem_success_rate_with_retries
            }

    return results


def plot_success_rates(results):
    """Create two plots: one for answer success rates and one for theorem sequence success rates."""
    levels = [1, 2]
    variants = ["variant_analogy_based_model_o1", "variant_random_all_theorems_model_o1"]

    # Prepare data for plotting
    data = {
        'analogy_based': {
            'answer_first_try': [],
            'answer_with_retries': [],
            'theorem_first_try': [],
            'theorem_with_retries': []
        },
        'random': {
            'answer_first_try': [],
            'answer_with_retries': [],
            'theorem_first_try': [],
            'theorem_with_retries': []
        }
    }

    for level in levels:
        level_key = f"level{level}"
        if level_key in results:
            for variant in variants:
                if variant in results[level_key]:
                    if variant == "variant_analogy_based_model_o1":
                        data['analogy_based']['answer_first_try'].append(
                            results[level_key][variant]["success_rate_answer_first_try"])
                        data['analogy_based']['answer_with_retries'].append(
                            results[level_key][variant]["success_rate_answer_with_retries"])
                        data['analogy_based']['theorem_first_try'].append(
                            results[level_key][variant]["success_rate_theorem_sequence_first_try"])
                        data['analogy_based']['theorem_with_retries'].append(
                            results[level_key][variant]["success_rate_theorem_sequence_with_retries"])
                    else:
                        data['random']['answer_first_try'].append(
                            results[level_key][variant]["success_rate_answer_first_try"])
                        data['random']['answer_with_retries'].append(
                            results[level_key][variant]["success_rate_answer_with_retries"])
                        data['random']['theorem_first_try'].append(
                            results[level_key][variant]["success_rate_theorem_sequence_first_try"])
                        data['random']['theorem_with_retries'].append(
                            results[level_key][variant]["success_rate_theorem_sequence_with_retries"])

    # Set style parameters
    plt.rcParams['font.size'] = 12
    plt.rcParams['axes.labelsize'] = 12
    plt.rcParams['axes.titlesize'] = 14
    plt.rcParams['xtick.labelsize'] = 11
    plt.rcParams['ytick.labelsize'] = 11
    plt.rcParams['legend.fontsize'] = 11
    plt.rcParams['figure.facecolor'] = 'white'
    plt.rcParams['axes.facecolor'] = 'white'
    plt.rcParams['grid.color'] = '#d3d3d3'
    plt.rcParams['grid.linestyle'] = '--'
    plt.rcParams['grid.alpha'] = 0.7

    # Create answer success rate plot
    plt.figure(figsize=(10, 6))
    # Random examples - both lines in blue
    plt.plot(levels, data['random']['answer_first_try'], 'o-', color='#1f77b4', label='Random examples (first try)',
             linewidth=2, markersize=8, markeredgewidth=1.5)
    plt.plot(levels, data['random']['answer_with_retries'], 's--', color='#1f77b4',
             label='Random examples (with verifier feedback)', linewidth=2, markersize=8, markeredgewidth=1.5)
    # Analogous examples - both lines in orange
    plt.plot(levels, data['analogy_based']['answer_first_try'], 'o-', color='#ff7f0e',
             label='Analogous examples (first try)', linewidth=2, markersize=8, markeredgewidth=1.5)
    plt.plot(levels, data['analogy_based']['answer_with_retries'], 's--', color='#ff7f0e',
             label='Analogous examples (with verifier feedback)', linewidth=2, markersize=8, markeredgewidth=1.5)

    plt.xlabel('Level', fontsize=12)
    plt.ylabel('Success Rate', fontsize=12)
    plt.title('o1 Model Answer Success Rate Comparison Across Levels', fontsize=14)
    plt.grid(True)
    plt.legend(fontsize=10)
    plt.gca().yaxis.set_major_formatter(plt.FuncFormatter(lambda y, _: '{:.0%}'.format(y)))
    plt.ylim(0, 1.05)  # Slightly above 100% to show markers
    plt.xticks(levels)
    plt.axhline(y=0, color='k', linestyle='-', alpha=0.3)
    plt.tight_layout()
    plt.savefig('answer_success_rate.png', dpi=300, bbox_inches='tight')
    plt.close()

    # Create theorem sequence success rate plot
    plt.figure(figsize=(10, 6))
    # Random examples - both lines in blue
    plt.plot(levels, data['random']['theorem_first_try'], 'o-', color='#1f77b4', label='Random examples (first try)',
             linewidth=2, markersize=8, markeredgewidth=1.5)
    plt.plot(levels, data['random']['theorem_with_retries'], 's--', color='#1f77b4',
             label='Random examples (with verifier feedback)', linewidth=2, markersize=8, markeredgewidth=1.5)
    # Analogous examples - both lines in orange
    plt.plot(levels, data['analogy_based']['theorem_first_try'], 'o-', color='#ff7f0e',
             label='Analogous examples (first try)', linewidth=2, markersize=8, markeredgewidth=1.5)
    plt.plot(levels, data['analogy_based']['theorem_with_retries'], 's--', color='#ff7f0e',
             label='Analogous examples (with verifier feedback)', linewidth=2, markersize=8, markeredgewidth=1.5)

    plt.xlabel('Level', fontsize=12)
    plt.ylabel('Success Rate', fontsize=12)
    plt.title('o1 Model Theorem Sequence Success Rate Comparison Across Levels', fontsize=14)
    plt.grid(True)
    plt.legend(fontsize=10)
    plt.gca().yaxis.set_major_formatter(plt.FuncFormatter(lambda y, _: '{:.0%}'.format(y)))
    plt.ylim(0, 1.05)  # Slightly above 100% to show markers
    plt.xticks(levels)
    plt.axhline(y=0, color='k', linestyle='-', alpha=0.3)
    plt.tight_layout()
    plt.savefig('theorem_success_rate.png', dpi=300, bbox_inches='tight')
    plt.close()


if __name__ == "__main__":
    base_path = "../../../results"
    results = calculate_success_rates(base_path)

    print("\nSuccess Rates:")
    for level, variants in results.items():
        print(f"\n{level}:")
        for variant, rates in variants.items():
            print(f"  {variant}:")
            print(f"    Answer success rate (first try): {rates['success_rate_answer_first_try']:.2%}")
            print(f"    Answer success rate (with verifier feedback): {rates['success_rate_answer_with_retries']:.2%}")
            print(
                f"    Theorem sequence success rate (first try): {rates['success_rate_theorem_sequence_first_try']:.2%}")
            print(
                f"    Theorem sequence success rate (with verifier feedback): {rates['success_rate_theorem_sequence_with_retries']:.2%}")

    # Create plots
    plot_success_rates(results)
    print("\nPlots have been saved as 'answer_success_rate.png' and 'theorem_success_rate.png'")