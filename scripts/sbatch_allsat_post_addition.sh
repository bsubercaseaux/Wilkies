#!/usr/bin/env bash
#SBATCH --job-name=wilkies-allsat
#SBATCH --output=logs/slurm/%x-%A_%a.out
#SBATCH --error=logs/slurm/%x-%A_%a.err
#SBATCH --time=24:00:00
#SBATCH --mem=8G
#SBATCH --cpus-per-task=1

set -euo pipefail

if [[ -z "${SLURM_ARRAY_TASK_ID:-}" ]]; then
  echo "This script expects to run as a Slurm array job." >&2
  exit 2
fi

REPO_DIR="${REPO_DIR:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
N="${N:-12}"
CNF_DIR="${CNF_DIR:-formulas/post-add}"
RESULT_DIR="${RESULT_DIR:-results/post-add}"
DATAVARS="${DATAVARS:-3600}"
ALLSAT="${ALLSAT:-allsat}"
ALLSAT_EXTRA_ARGS="${ALLSAT_EXTRA_ARGS:-}"

cd "$REPO_DIR"
mkdir -p "$RESULT_DIR"

index="$SLURM_ARRAY_TASK_ID"
cnf="${CNF_DIR}/wilkies_${N}_${index}.cnf"
stdout_file="${RESULT_DIR}/wilkies_${N}_${index}.allsat.out"
stderr_file="${RESULT_DIR}/wilkies_${N}_${index}.allsat.err"

if [[ ! -s "$cnf" ]]; then
  echo "Missing CNF: $cnf" >&2
  exit 3
fi

extra_args=()
if [[ -n "$ALLSAT_EXTRA_ARGS" ]]; then
  read -r -a extra_args <<< "$ALLSAT_EXTRA_ARGS"
fi

echo "Running allsat on $cnf with datavars=${DATAVARS}"
"$ALLSAT" "$cnf" --allsat "--datavars=${DATAVARS}" "${extra_args[@]}" \
  > "$stdout_file" \
  2> "$stderr_file"

num_solutions="$(grep -c '^v ' "$stdout_file" || true)"
echo "Finished model ${index}; wrote ${stdout_file}; counted ${num_solutions} model lines."
