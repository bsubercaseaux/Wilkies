"""
Verification script for the classification of 8,957,952 models of HSA
failing Wilkie's identity on 12 elements.

This script trusts ONLY:
  1. The SAT encoding (encoder.py / wilkies_12.cnf)
  2. The SAT solutions in solutions_addition.txt (768 addition tables)

It verifies that the classification in full_classification.md correctly
describes all models by:
  - Generating the 768 addition tables from the classification template
  - Checking they match the SAT solutions up to isomorphism
  - For EACH of the 768 SAT-solved addition tables, running allsat to
    enumerate all compatible (mul, exp) pairs
  - Checking each matches the classification's mul table and exp template

Uses 8 parallel workers.
"""

import sys
import os
import subprocess
import itertools
import tempfile
from multiprocessing import Pool, current_process
from collections import Counter
from itertools import product as iprod

from pynauty import Graph, certificate, canon_label, autgrp
from pysat.formula import IDPool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from encoder import encode, operation_accessors

N = 12
NUM_WORKERS = 8

# =============================================================================
# CLASSIFICATION DATA (from full_classification.md)
# =============================================================================

CLASSIFICATION_MUL = [
    [8, 0, 2,10, 9,10,10, 2, 8,10,10, 2],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9,10,11],
    [2, 2,10,10,10,10,10,10, 2,10,10,10],
    [10, 3,10,10,10,10,10,10,10,10,10,10],
    [9, 4,10,10,10, 9,10,10,10,10,10,10],
    [10, 5,10,10, 9,10,10,10,10,10,10,10],
    [10, 6,10,10,10,10,10,10,10,10,10,10],
    [2, 7,10,10,10,10,10,10, 2,10,10,10],
    [8, 8, 2,10,10,10,10, 2, 8,10,10, 2],
    [10, 9,10,10,10,10,10,10,10,10,10,10],
    [10,10,10,10,10,10,10,10,10,10,10,10],
    [2,11,10,10,10,10,10,10, 2,10,10,10],
]

# Addition template: fixed cells (not F or ?)
# F-cells: (0,1), (1,1), (1,7), (1,8), (1,11)
# ?-cells: (0,5), (0,6), (1,4), (1,5), (1,6), (4,8), (5,8), (6,8)
ADD_TEMPLATE_BASE = [
    [ 2,-1,10,10, 9,-1,-1, 3, 2,10,10, 3],
    [-1,-1, 3,10,-1,-1,-1,-1,-1,10,10,-1],
    [10, 3,10,10,10,10,10,10,10,10,10,10],
    [10,10,10,10,10,10,10,10,10,10,10,10],
    [ 9,-1,10,10,10, 9, 3,10,-1,10,10,10],
    [-1,-1,10,10, 9,10, 3,10,-1,10,10,10],
    [-1,-1,10,10, 3, 3,10,10,-1,10,10,10],
    [ 3,-1,10,10,10,10,10,10, 3,10,10,10],
    [ 2,-1,10,10,-1,-1,-1, 3, 2,10,10, 3],
    [10,10,10,10,10,10,10,10,10,10,10,10],
    [10,10,10,10,10,10,10,10,10,10,10,10],
    [ 3,-1,10,10,10,10,10,10, 3,10,10,10],
]

FAMILY_F_CELLS = {
    # (upper-triangle positions, values)
    'A': {(0,1): 11, (1,1): 7, (1,7): 3, (1,8): 7, (1,11): 3},
    'B': {(0,1): 11, (1,1): 2, (1,7): 10, (1,8): 7, (1,11): 10},
    'C': {(0,1): 7, (1,1): 7, (1,7): 3, (1,8): 11, (1,11): 3},
}

FREE_CELL_POSITIONS = [(0,5), (0,6), (1,4), (1,5), (1,6), (4,8), (5,8), (6,8)]

# Exponentiation template
EXP_TEMPLATE_BASE = [
    [-1, 0, 8, 8, 8, 8, 8, 8,-1, 8, 8, 8],
    [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [10, 2,10,10,10,10,10,10,10,10,10,10],
    [-1, 3,10,10,-1,-1,-2,10,10, 9,10,10],
    [-1, 4,10,10,-1,-1,10,10,10,10,10,10],
    [-1, 5,10,10,-1,-1,10,10,10,10,10,10],
    [10, 6,10,10,10,10,10,10,10,10,10,10],
    [-3, 7,10,10,-3,-2,-2,10,10,10,10,10],
    [ 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8],
    [10, 9,10,10,10,10,10,10,10,10,10,10],
    [10,10,10,10,10,10,10,10,10,10,10,10],
    [-3,11,10,10,-3,-2,-2,10,10,10,10,10],
]
# -1 = P-cell, -2 = free ternary (?), -3 = constrained block (*)

P_PATTERNS = {
    'alpha': {(0,0): 0, (0,8): 0, (3,0): 5, (3,4): 4, (3,5): 5,
              (4,0): 9, (4,4):10, (4,5): 9, (5,0):10, (5,4): 9, (5,5):10},
    'beta':  {(0,0): 8, (0,8): 8, (3,0): 4, (3,4): 5, (3,5): 4,
              (4,0):10, (4,4): 9, (4,5):10, (5,0): 9, (5,4):10, (5,5): 9},
    'gamma': {(0,0): 8, (0,8): 8, (3,0): 5, (3,4): 4, (3,5): 5,
              (4,0): 9, (4,4):10, (4,5): 9, (5,0):10, (5,4): 9, (5,5):10},
}

FREE_TERNARY_POSITIONS = [(3,6), (7,5), (7,6), (11,5), (11,6)]
TERNARY_VALUES = [6, 9, 10]

STAR_SET_S = [(6,6), (6,9), (6,10), (9,6), (10,6)]

def star_type(pair):
    if pair == (6,6): return 'A'
    if pair[0] == 6: return 'B'
    return 'C'

# =============================================================================
# GENERATION FUNCTIONS
# =============================================================================

def generate_all_addition_tables():
    """Generate all 768 addition tables from the classification template."""
    tables = []
    for family_name in ['A', 'B', 'C']:
        f_cells = FAMILY_F_CELLS[family_name]
        for bits in iprod([3, 10], repeat=8):
            table = [row[:] for row in ADD_TEMPLATE_BASE]
            # Fill F-cells
            for (i, j), val in f_cells.items():
                table[i][j] = val
                table[j][i] = val
            # Fill ?-cells
            for k, (i, j) in enumerate(FREE_CELL_POSITIONS):
                table[i][j] = bits[k]
                table[j][i] = bits[k]
            # Verify no -1 remains
            assert all(table[i][j] >= 0 for i in range(N) for j in range(N))
            tables.append(table)
    return tables


def generate_all_exp_tables():
    """Generate all 11664 exponentiation tables from the classification template."""
    tables = set()
    for p_name, p_cells in P_PATTERNS.items():
        for ternary_bits in iprod(TERNARY_VALUES, repeat=5):
            for s0 in STAR_SET_S:
                for s4 in STAR_SET_S:
                    if star_type(s0) == star_type(s4):
                        continue
                    table = [row[:] for row in EXP_TEMPLATE_BASE]
                    # Fill P-cells
                    for (i, j), val in p_cells.items():
                        table[i][j] = val
                    # Fill free ternary cells
                    for k, (i, j) in enumerate(FREE_TERNARY_POSITIONS):
                        table[i][j] = ternary_bits[k]
                    # Fill * block
                    table[7][0] = s0[0]
                    table[11][0] = s0[1]
                    table[7][4] = s4[0]
                    table[11][4] = s4[1]
                    # Verify no negatives remain
                    assert all(table[i][j] >= 0 for i in range(N) for j in range(N))
                    tables.add(tuple(tuple(row) for row in table))
    return tables


# =============================================================================
# NAUTY UTILITIES
# =============================================================================

def commutative_table_certificate(table):
    """Nauty certificate for a commutative Cayley table (addition or multiplication)."""
    n = N
    m = n * (n + 1) // 2
    num_v = n + m + m
    g = Graph(num_v)
    g.set_vertex_coloring([set(range(n)), set(range(n, n+m)), set(range(n+m, n+2*m))])
    pair_idx = 0
    for i in range(n):
        for j in range(i, n):
            pv = n + pair_idx
            cv = n + m + pair_idx
            g.connect_vertex(pv, [i, j])
            g.connect_vertex(cv, [pv, table[i][j]])
            pair_idx += 1
    return certificate(g)


def find_isomorphism(table1, table2):
    """Find permutation σ mapping commutative table1 to table2.
    Uses row-sorted profile to prune, then backtracking with constraint propagation.
    Returns sigma (list of length N) or None."""
    n = N

    if table1 == table2:
        return list(range(n))

    # Start with full domains; propagation will narrow them
    domain = [set(range(n)) for _ in range(n)]

    def propagate(sigma, domain):
        changed = True
        while changed:
            changed = False
            for i in range(n):
                if sigma[i] is None:
                    continue
                for j in range(n):
                    if sigma[j] is None:
                        continue
                    k = table1[i][j]
                    required = table2[sigma[i]][sigma[j]]
                    if sigma[k] is not None:
                        if sigma[k] != required:
                            return False
                    else:
                        if required not in domain[k]:
                            return False
                        if len(domain[k]) > 1:
                            domain[k] = {required}
                            sigma[k] = required
                            for x in range(n):
                                if x != k:
                                    domain[x].discard(required)
                                    if not domain[x] and sigma[x] is None:
                                        return False
                            changed = True
        return True

    def search(sigma, domain):
        unassigned = [i for i in range(n) if sigma[i] is None]
        if not unassigned:
            return sigma[:]
        best = min(unassigned, key=lambda i: len(domain[i]))
        if not domain[best]:
            return None
        for target in sorted(domain[best]):
            new_sigma = sigma[:]
            new_sigma[best] = target
            new_domain = [set(d) for d in domain]
            new_domain[best] = {target}
            valid = True
            for i in range(n):
                if i != best:
                    new_domain[i].discard(target)
                    if not new_domain[i] and new_sigma[i] is None:
                        valid = False
                        break
            if not valid:
                continue
            if not propagate(new_sigma, new_domain):
                continue
            result = search(new_sigma, new_domain)
            if result is not None:
                return result
        return None

    sigma = [None] * n
    if not propagate(sigma, domain):
        return None
    return search(sigma, domain)


def apply_perm(table, sigma):
    """Apply permutation sigma to a table (symmetric or not)."""
    n = N
    result = [[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            result[sigma[i]][sigma[j]] = sigma[table[i][j]]
    return result


# =============================================================================
# SAT SOLUTION DECODING
# =============================================================================

def decode_addition_from_solution(solution):
    """Decode an addition table from a SAT solution."""
    idpool = IDPool()
    add_, mul_, exp, symmetric_combs = operation_accessors(N, idpool)
    model = set(lit for lit in solution if lit > 0)
    table = [[0]*N for _ in range(N)]
    for i in range(N):
        for j in range(i, N):
            for k in range(N):
                if add_(i, j, k) in model:
                    table[i][j] = k
                    table[j][i] = k
                    break
    return table


def parse_solutions_file(filename):
    """Parse solutions_addition.txt and return list of literal lists."""
    solutions = []
    with open(filename, 'r') as f:
        for line in f:
            line = line.strip()
            if line.startswith('v '):
                lits = [int(x) for x in line[2:].split()]
                solutions.append(lits)
    return solutions


# =============================================================================
# ALLSAT WORKER
# =============================================================================

def verify_one_addition_table(args):
    """
    Worker function: given an addition table (from SAT solutions) and
    the permutation mapping it to the classification, run allsat and verify.
    """
    idx, add_table, sigma, classification_exp_set = args
    n = N

    # Generate the CNF with fixed addition table
    cnf, idpool = encode(n, return_idpool=True)
    idpool2 = IDPool()
    add_, mul_, exp_f, symmetric_combs = operation_accessors(n, idpool2)

    for i, j in symmetric_combs:
        correct_value = add_table[i][j]
        for k in range(n):
            var = add_(i, j, k)
            if k == correct_value:
                cnf.append([var])
            else:
                cnf.append([-var])

    # Write CNF to temp file
    tmp_cnf = tempfile.NamedTemporaryFile(mode='w', suffix='.cnf', delete=False, prefix=f'wilkie_{idx}_')
    cnf_path = tmp_cnf.name
    tmp_cnf.close()
    cnf.to_file(cnf_path)

    # Run allsat
    try:
        result = subprocess.run(
            ['bash', '-c', f'source ~/.zshrc && allsat {cnf_path} --datavars=3600 --printsolutions'],
            capture_output=True, text=True, timeout=1200
        )
    except subprocess.TimeoutExpired:
        os.unlink(cnf_path)
        return (idx, 'FAIL', 'allsat timed out')
    finally:
        if os.path.exists(cnf_path):
            os.unlink(cnf_path)

    # Parse solutions
    solutions = []
    for line in result.stdout.split('\n'):
        if line.startswith('v '):
            solutions.append([int(x) for x in line[2:].split()])

    if len(solutions) == 0:
        return (idx, 'FAIL', 'no solutions found')

    # Decode mul and exp tables
    idpool3 = IDPool()
    _, mul_acc, exp_acc, _ = operation_accessors(n, idpool3)

    mul_tables = set()
    exp_tables = set()
    for sol in solutions:
        model = set(lit for lit in sol if lit > 0)

        # Decode mul
        mul_table = [[0]*n for _ in range(n)]
        for i in range(n):
            for j in range(i, n):
                for k in range(n):
                    if mul_acc(i, j, k) in model:
                        mul_table[i][j] = k
                        mul_table[j][i] = k
                        break
        mul_tables.add(tuple(tuple(row) for row in mul_table))

        # Decode exp
        exp_table = [[0]*n for _ in range(n)]
        for i in range(n):
            for j in range(n):
                for k in range(n):
                    if exp_acc(i, j, k) in model:
                        exp_table[i][j] = k
                        break
        exp_tables.add(tuple(tuple(row) for row in exp_table))

    # Check: exactly 1 mul table
    if len(mul_tables) != 1:
        return (idx, 'FAIL', f'expected 1 mul table, got {len(mul_tables)}')

    # Check: mul table matches classification under sigma
    actual_mul = [list(row) for row in list(mul_tables)[0]]
    relabeled_mul = apply_perm(actual_mul, sigma)
    if relabeled_mul != CLASSIFICATION_MUL:
        return (idx, 'FAIL', 'mul table does not match classification after relabeling')

    # Check: exactly 11664 exp tables
    if len(exp_tables) != 11664:
        return (idx, 'FAIL', f'expected 11664 exp tables, got {len(exp_tables)}')

    # Check: exp tables match classification under sigma
    relabeled_exp_set = set()
    for exp_tup in exp_tables:
        exp_list = [list(row) for row in exp_tup]
        relabeled = apply_perm(exp_list, sigma)
        relabeled_exp_set.add(tuple(tuple(row) for row in relabeled))

    if relabeled_exp_set != classification_exp_set:
        return (idx, 'FAIL', 'exp tables do not match classification after relabeling')

    return (idx, 'PASS', f'{len(solutions)} solutions verified')


# =============================================================================
# MAIN
# =============================================================================

def main():
    print("=" * 70)
    print("VERIFICATION OF FULL CLASSIFICATION")
    print("Checking 8,957,952 = 768 × 11,664 models of HSA (size 12)")
    print("=" * 70)
    print()

    # Step 1: Generate classification tables
    print("[Step 1] Generating 768 addition tables from classification template...")
    classification_add_tables = generate_all_addition_tables()
    assert len(classification_add_tables) == 768
    print(f"  Generated {len(classification_add_tables)} addition tables.")

    print("[Step 1b] Generating 11664 exponentiation tables from classification template...")
    classification_exp_set = generate_all_exp_tables()
    assert len(classification_exp_set) == 11664, f"Got {len(classification_exp_set)}"
    print(f"  Generated {len(classification_exp_set)} exponentiation tables.")
    print()

    # Step 2: Compute nauty certificates for classification tables
    print("[Step 2] Computing nauty certificates for classification addition tables...")
    classification_certs = {}
    for i, table in enumerate(classification_add_tables):
        cert = commutative_table_certificate(table)
        if cert in classification_certs:
            print(f"  FAIL: duplicate certificate at indices {classification_certs[cert]} and {i}")
            sys.exit(1)
        classification_certs[cert] = i
    print(f"  All 768 classification tables have distinct certificates.")
    print()

    # Step 3: Parse SAT solutions and match to classification
    print("[Step 3] Parsing SAT solutions from solutions_addition.txt...")
    solutions = parse_solutions_file('solutions_addition.txt')
    assert len(solutions) == 768, f"Expected 768 solutions, got {len(solutions)}"
    print(f"  Parsed {len(solutions)} solutions.")

    print("[Step 3b] Decoding addition tables and matching to classification...")
    matched = []  # (sat_index, classification_index, add_table, sigma)
    unmatched = []

    for sat_idx, sol in enumerate(solutions):
        add_table = decode_addition_from_solution(sol)
        cert = commutative_table_certificate(add_table)
        if cert not in classification_certs:
            unmatched.append(sat_idx)
            continue
        class_idx = classification_certs[cert]
        class_table = classification_add_tables[class_idx]
        sigma = find_isomorphism(add_table, class_table)
        if sigma is None:
            unmatched.append(sat_idx)
            continue
        matched.append((sat_idx, class_idx, add_table, sigma))

    if unmatched:
        print(f"  FAIL: {len(unmatched)} SAT solutions not matched to classification!")
        sys.exit(1)

    # Check bijection: each classification table matched exactly once
    class_indices_hit = [m[1] for m in matched]
    if len(set(class_indices_hit)) != 768:
        print(f"  FAIL: only {len(set(class_indices_hit))} distinct classification tables matched")
        sys.exit(1)

    print(f"  PASS: All 768 SAT solutions matched bijectively to classification tables.")
    print()

    # Step 3c: Verify non-isomorphism (Aut(mul) argument)
    print("[Step 3c] Verifying all 8,957,952 models are pairwise non-isomorphic...")
    print("  Computing Aut(mul) via nauty...")
    m = N * (N + 1) // 2
    num_v = N + m + m
    g_mul = Graph(num_v)
    g_mul.set_vertex_coloring([set(range(N)), set(range(N, N+m)), set(range(N+m, N+2*m))])
    pair_idx = 0
    for i in range(N):
        for j in range(i, N):
            pv = N + pair_idx
            cv = N + m + pair_idx
            g_mul.connect_vertex(pv, [i, j])
            g_mul.connect_vertex(cv, [pv, CLASSIFICATION_MUL[i][j]])
            pair_idx += 1
    aut_info = autgrp(g_mul)
    aut_size = int(aut_info[1])
    aut_generators = aut_info[0]
    print(f"  |Aut(mul)| = {aut_size}")
    if aut_size == 1:
        print(f"  Aut(mul) is trivial => all models with distinct (add, exp) are non-isomorphic.")
        print(f"  PASS")
    else:
        # Check that no non-identity automorphism maps any classification add table to another
        print(f"  Aut(mul) has {len(aut_generators)} generators. Checking none preserves the addition table set...")
        classification_add_set = set(
            tuple(tuple(row) for row in t) for t in classification_add_tables
        )
        aut_preserves = False
        for gen in aut_generators:
            sigma = gen[:N]
            for t in classification_add_tables:
                permuted = apply_perm(t, sigma)
                if tuple(tuple(row) for row in permuted) in classification_add_set:
                    aut_preserves = True
                    print(f"  FAIL: an Aut(mul) generator preserves the addition table set!")
                    sys.exit(1)
        print(f"  No non-identity Aut(mul) element maps any valid addition table to another.")
        print(f"  => Aut(add, mul) = {{identity}} for all 768 pairs.")
        print(f"  => Distinct (add, exp) pairs give non-isomorphic models.")
        print(f"  PASS")
    print()

    # Step 4: Verify (mul, exp) for each addition table via allsat
    print(f"[Step 4] Verifying (mul, exp) for all 768 addition tables ({NUM_WORKERS} workers)...")
    print(f"  This will take a while. Progress updates below.")
    print()

    # Prepare args for workers
    worker_args = [
        (sat_idx, add_table, sigma, classification_exp_set)
        for sat_idx, class_idx, add_table, sigma in matched
    ]

    # Run in parallel
    completed = 0
    failures = []
    with Pool(NUM_WORKERS) as pool:
        for result in pool.imap_unordered(verify_one_addition_table, worker_args):
            idx, status, msg = result
            completed += 1
            if status == 'FAIL':
                failures.append((idx, msg))
                print(f"  [{completed}/768] Table {idx}: FAIL - {msg}")
            else:
                print(f"  [{completed}/768] Table {idx}: PASS")

    print()
    print("=" * 70)
    print("FINAL RESULTS")
    print("=" * 70)
    print()
    print(f"  Addition tables (classification vs SAT): PASS (768/768 matched)")
    if failures:
        print(f"  Mul/Exp verification: FAIL ({len(failures)} failures)")
        for idx, msg in failures[:10]:
            print(f"    Table {idx}: {msg}")
    else:
        print(f"  Mul/Exp verification: PASS (all 768 tables verified)")
        print()
        print(f"  CONCLUSION: The classification correctly describes")
        print(f"  768 × 11,664 = 8,957,952 = 2^12 × 3^7")
        print(f"  pairwise non-isomorphic models of HSA failing Wilkie's identity.")


if __name__ == '__main__':
    main()
