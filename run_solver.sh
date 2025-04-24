#!/bin/bash

# Keep Mac awake during script execution
echo "Running LLM_analogy_based_solver with caffeinate..."

# Export PYTHONPATH so it's available to the python process
export PYTHONPATH="$(pwd)"

# Run the script with caffeinate
caffeinate -i python src/formalgeo/LLM_analogy_based_solver.py
