#!/usr/bin/env bash
#SBATCH --job-name=wilkies-gen-add
#SBATCH --output=logs/slurm/%x-%A_%a.out
#SBATCH --error=logs/slurm/%x-%A_%a.err
#SBATCH --time=02:00:00
#SBATCH --mem=6G
#SBATCH --cpus-per-task=1

set -euo pipefail

if [[ -z "${SLURM_ARRAY_TASK_ID:-}" ]]; then
  echo "This script expects to run as a Slurm array job." >&2
  exit 2
fi

REPO_DIR="${REPO_DIR:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
N="${N:-12}"
MODELS="${MODELS:-solutions_addition.txt}"
OUT_DIR="${OUT_DIR:-formulas/post-add}"
PYTHON="${PYTHON:-python3}"

cd "$REPO_DIR"
mkdir -p "$OUT_DIR"

echo "Generating post-addition CNF for n=${N}, model=${SLURM_ARRAY_TASK_ID}"
"$PYTHON" encoder.py \
  -n "$N" \
  --gen-post-addition "$MODELS" \
  --post-addition-index "$SLURM_ARRAY_TASK_ID" \
  --post-addition-output-dir "$OUT_DIR"
