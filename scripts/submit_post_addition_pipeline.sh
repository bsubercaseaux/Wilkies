#!/usr/bin/env bash
set -euo pipefail

REPO_DIR="${REPO_DIR:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
cd "$REPO_DIR"

N="${N:-12}"
MODELS="${MODELS:-solutions_addition.txt}"
OUT_DIR="${OUT_DIR:-formulas/post-add}"
RESULT_DIR="${RESULT_DIR:-results/post-add}"
DATAVARS="${DATAVARS:-3600}"
PYTHON="${PYTHON:-python3}"
ALLSAT="${ALLSAT:-allsat}"
ALLSAT_EXTRA_ARGS="${ALLSAT_EXTRA_ARGS:-}"

# Set ARRAY_LIMIT, GEN_ARRAY_LIMIT, or ALLSAT_ARRAY_LIMIT to cap concurrency,
# e.g. ARRAY_LIMIT=64 scripts/submit_post_addition_pipeline.sh.
GEN_ARRAY_LIMIT="${GEN_ARRAY_LIMIT:-${ARRAY_LIMIT:-}}"
ALLSAT_ARRAY_LIMIT="${ALLSAT_ARRAY_LIMIT:-${ARRAY_LIMIT:-}}"

mkdir -p logs/slurm "$OUT_DIR" "$RESULT_DIR"

num_models="$("$PYTHON" - "$MODELS" <<'PY'
import sys

count = 0
has_open_model = False
with open(sys.argv[1], "r") as f:
    for line in f:
        if not line.startswith("v "):
            continue
        for token in line.split()[1:]:
            lit = int(token)
            if lit == 0:
                count += 1
                has_open_model = False
            else:
                has_open_model = True
if has_open_model:
    count += 1
print(count)
PY
)"

if [[ "$num_models" -le 0 ]]; then
  echo "No models found in $MODELS" >&2
  exit 4
fi

last_model=$((num_models - 1))
gen_array="0-${last_model}"
allsat_array="0-${last_model}"
if [[ -n "$GEN_ARRAY_LIMIT" ]]; then
  gen_array="${gen_array}%${GEN_ARRAY_LIMIT}"
fi
if [[ -n "$ALLSAT_ARRAY_LIMIT" ]]; then
  allsat_array="${allsat_array}%${ALLSAT_ARRAY_LIMIT}"
fi

export REPO_DIR N MODELS OUT_DIR RESULT_DIR DATAVARS PYTHON ALLSAT ALLSAT_EXTRA_ARGS

if [[ "${DRY_RUN:-0}" == "1" ]]; then
  echo "Found ${num_models} models in ${MODELS}."
  echo "Would submit generation array:"
  echo "  sbatch --parsable --array=${gen_array} scripts/sbatch_gen_post_addition.sh"
  echo "Would submit allsat array after generation succeeds:"
  echo "  sbatch --parsable --dependency=afterok:<gen_job> --array=${allsat_array} scripts/sbatch_allsat_post_addition.sh"
  exit 0
fi

gen_job="$(
  sbatch \
    --parsable \
    --array="$gen_array" \
    scripts/sbatch_gen_post_addition.sh
)"

allsat_job="$(
  sbatch \
    --parsable \
    --dependency="afterok:${gen_job}" \
    --array="$allsat_array" \
    scripts/sbatch_allsat_post_addition.sh
)"

echo "Submitted ${num_models} CNF-generation tasks as job ${gen_job}."
echo "Submitted ${num_models} allsat tasks as job ${allsat_job}, dependent on ${gen_job}."
echo "CNFs: ${OUT_DIR}/wilkies_${N}_<index>.cnf"
echo "allsat output: ${RESULT_DIR}/wilkies_${N}_<index>.allsat.out"
