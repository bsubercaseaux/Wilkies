#!/usr/bin/env bash
set -euo pipefail

REPO_DIR="${REPO_DIR:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
PYTHON="${PYTHON:-python3}"
TMP_DIR="${TMP_DIR:-/private/tmp/wilkies-sbatch-smoke.$$}"

cleanup() {
  if [[ "${KEEP_SMOKE:-0}" != "1" ]]; then
    rm -rf "$TMP_DIR"
  fi
}
trap cleanup EXIT

mkdir -p "$TMP_DIR"

fixture_models="${TMP_DIR}/solutions_addition_n5.txt"
fake_allsat="${TMP_DIR}/fake_allsat.sh"
out_dir="${TMP_DIR}/formulas/post-add"
result_dir="${TMP_DIR}/results/post-add"

"$PYTHON" - "$fixture_models" <<'PY'
import sys

n = 5
num_addition_vars = (n * (n + 1) // 2) * n
lits = []
for block_start in range(1, num_addition_vars + 1, n):
    for offset in range(n):
        lit = block_start + offset
        lits.append(lit if offset == 0 else -lit)

with open(sys.argv[1], "w") as f:
    f.write("s SATISFIABLE\n")
    f.write("v " + " ".join(map(str, lits)) + " 0\n")
PY

cat > "$fake_allsat" <<'SH'
#!/usr/bin/env bash
set -euo pipefail

echo "fake allsat received: $*" >&2
echo "s SATISFIABLE"
echo "v 1 -2 0"
echo "v -1 2 0"
SH
chmod +x "$fake_allsat"

cd "$REPO_DIR"

echo "Smoke temp dir: $TMP_DIR"
echo "1. Checking submitter dry-run..."
DRY_RUN=1 \
  N=5 \
  MODELS="$fixture_models" \
  OUT_DIR="$out_dir" \
  RESULT_DIR="$result_dir" \
  DATAVARS=10 \
  PYTHON="$PYTHON" \
  ALLSAT="$fake_allsat" \
  scripts/submit_post_addition_pipeline.sh

echo "2. Running generation worker with SLURM_ARRAY_TASK_ID=0..."
(
  cd "$TMP_DIR"
  SLURM_ARRAY_TASK_ID=0 \
    SLURM_SUBMIT_DIR="$REPO_DIR" \
    N=5 \
    MODELS="$fixture_models" \
    OUT_DIR="$out_dir" \
    PYTHON="$PYTHON" \
    "$REPO_DIR/scripts/sbatch_gen_post_addition.sh"
)

cnf="${out_dir}/wilkies_5_0.cnf"
if [[ ! -s "$cnf" ]]; then
  echo "Expected generated CNF at $cnf" >&2
  exit 10
fi
if grep -q '^0 0$' "$cnf"; then
  echo "Generated CNF contains an empty clause from a DIMACS terminator." >&2
  exit 11
fi

echo "3. Running allsat worker with fake allsat..."
(
  cd "$TMP_DIR"
  SLURM_ARRAY_TASK_ID=0 \
    SLURM_SUBMIT_DIR="$REPO_DIR" \
    N=5 \
    CNF_DIR="$out_dir" \
    RESULT_DIR="$result_dir" \
    DATAVARS=10 \
    ALLSAT="$fake_allsat" \
    "$REPO_DIR/scripts/sbatch_allsat_post_addition.sh"
)

allsat_out="${result_dir}/wilkies_5_0.allsat.out"
if [[ "$(grep -c '^v ' "$allsat_out")" != "2" ]]; then
  echo "Expected fake allsat output to contain two model lines." >&2
  exit 12
fi

echo "Local sbatch smoke test passed."
if [[ "${KEEP_SMOKE:-0}" == "1" ]]; then
  echo "Kept smoke artifacts in $TMP_DIR"
fi
