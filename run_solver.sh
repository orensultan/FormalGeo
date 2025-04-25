#!/bin/bash

# File: run_llm_solver.sh

# Description: Keeps Mac awake and runs the LLM analogy-based solver script with helpful logging.

# Exit immediately if a command exits with a non-zero status
set -e

# Log the start time
echo "======================================="
echo "Starting LLM_analogy_based_solver..."
echo "Start time: $(date)"
echo "======================================="

# Keep Mac awake during script execution
echo "Using caffeinate to prevent sleep..."

# Export PYTHONPATH so your src/ directory is included
export PYTHONPATH="$(pwd)"
echo "PYTHONPATH set to $PYTHONPATH"

# Run the Python script with caffeinate
caffeinate -i python src/formalgeo/LLM_analogy_based_solver.py

# Log the end time
echo "======================================="
echo "Finished script."
echo "End time: $(date)"
echo "======================================="
