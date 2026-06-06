import argparse
import itertools
from pathlib import Path
import amo_encoder
import lex
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver

# create variables once for encoding/decoding
def operation_accessors(n, idpool):
    add = lambda i, j, k: idpool.id(f"add_{i}_{j}_{k}")
    mul = lambda i, j, k: idpool.id(f"mul_{i}_{j}_{k}")
    exp = lambda i, j, k: idpool.id(f"exp_{i}_{j}_{k}")

    symmetric_combs = [] # (i, j) with i <= j
    for i in range(n):
        symmetric_combs.extend([(i, j) for j in range(i, n)])

    # access add then mul then exp, to force variable ordering
    for i, j in symmetric_combs:
        for k in range(n):
            add(i, j, k)
    for i, j in symmetric_combs:
        for k in range(n):
            mul(i, j, k)
    for i, j in itertools.product(range(n), repeat=2):
        for k in range(n):
            exp(i, j, k)

    # commutativity of addition and multiplication is encoded by considering unordered pairs
    add_ = lambda i, j, k: add(min(i, j), max(i, j), k)
    mul_ = lambda i, j, k: mul(min(i, j), max(i, j), k)

    return add_, mul_, exp, symmetric_combs


def encode(n, return_idpool=False):
    cnf = CNF()
    idpool = IDPool()
    add_, mul_, exp, symmetric_combs = operation_accessors(n, idpool)


    for i, j in symmetric_combs: # tried recursive but it was worse than pairwise
        cnf.extend(amo_encoder.exactly_one_pairwise([add_(i, j, k) for k in range(n)]))
    for i, j in symmetric_combs:
        cnf.extend(amo_encoder.exactly_one_pairwise([mul_(i, j, k) for k in range(n)]))
    for i, j in itertools.product(range(n), repeat=2):
        cnf.extend(amo_encoder.exactly_one_pairwise([exp(i, j, k) for k in range(n)]))


    # x * 1 = x
    for x in range(n):
        cnf.append([mul_(x, 1, x)])

    # x^1 = x
    for x in range(n):
        cnf.append([exp(x, 1, x)])

    # 1^x = 1
    for x in range(n):
        cnf.append([exp(1, x, 1)])

    # associativity of addition
    # add_2(i, j, k, l) := i+(j+k) = (i+j)+k = l
    add_2 = lambda i, j, k, l: idpool.id(f"add_2_{i}_{j}_{k}_{l}")
    for i, k in symmetric_combs:
        for j in range(n):
            cnf.extend(amo_encoder.at_most_one_pairwise([add_2(i, j, k, l) for l in range(n)]))
            for l, m in itertools.product(range(n), repeat=2):
                cnf.append([-add_(j, k, m), -add_(i, m, l), add_2(i, j, k, l)])
                cnf.append([-add_(i, j, m), -add_(m, k, l), add_2(i, j, k, l)])

    # associativity of multiplication
    # mul_2(i, j, k, l) := i*(j*k) = (i*j)*k = l
    mul_2 = lambda i, j, k, l: idpool.id(f"mul_2_{i}_{j}_{k}_{l}")
    for i, k in symmetric_combs:
        for j in range(n):
            cnf.extend(amo_encoder.at_most_one_pairwise([mul_2(i, j, k, l) for l in range(n)]))
            for l, m in itertools.product(range(n), repeat=2):
                cnf.append([-mul_(j, k, m), -mul_(i, m, l), mul_2(i, j, k, l)])
                cnf.append([-mul_(i, j, m), -mul_(m, k, l), mul_2(i, j, k, l)])

    # distributivity
    # x * (y+z) = x*y + x*z
    dist = lambda x, y, z, l: idpool.id(f"dist_{x}_{y}_{z}_{l}")
    for x in range(n):
        for y, z in symmetric_combs:
            cnf.extend(amo_encoder.at_most_one_pairwise([dist(x, y, z, l) for l in range(n)]))
            for l, m in itertools.product(range(n), repeat=2):
                cnf.append([-add_(y, z, m), -mul_(x, m, l), dist(x, y, z, l)])
            for l, m1, m2 in itertools.product(range(n), repeat=3):
                cnf.append([-mul_(x, y, m1), -mul_(x, z, m2), -add_(m1, m2, l), dist(x, y, z, l)])

    # exponent distributes over addition in the exponent
    # x^(y+z) = x^y * x^z
    exp_add = lambda x, y, z, l: idpool.id(f"exp_add_{x}_{y}_{z}_{l}")
    for x in range(n):
        for y, z in symmetric_combs:
            cnf.extend(amo_encoder.at_most_one_pairwise([exp_add(x, y, z, l) for l in range(n)]))
            for l, m in itertools.product(range(n), repeat=2):
                cnf.append([-add_(y, z, m), -exp(x, m, l), exp_add(x, y, z, l)])
            for l, m1, m2 in itertools.product(range(n), repeat=3):
                cnf.append([-exp(x, y, m1), -exp(x, z, m2), -mul_(m1, m2, l), exp_add(x, y, z, l)])

    # exponent distributes over multiplication in the base
    # (x*y)^z = x^z * y^z
    exp_mul = lambda x, y, z, l: idpool.id(f"exp_mul_{x}_{y}_{z}_{l}")
    for x, y in symmetric_combs:
        for z in range(n):
            cnf.extend(amo_encoder.at_most_one_pairwise([exp_mul(x, y, z, l) for l in range(n)]))
            for l, m in itertools.product(range(n), repeat=2):
                cnf.append([-mul_(x, y, m), -exp(m, z, l), exp_mul(x, y, z, l)])
            for l, m1, m2 in itertools.product(range(n), repeat=3):
                cnf.append([-exp(x, z, m1), -exp(y, z, m2), -mul_(m1, m2, l), exp_mul(x, y, z, l)])

    # exponent associativity
    # (x^y)^z = x^(y*z)
    exp_2 = lambda x, y, z, l: idpool.id(f"exp_2_{x}_{y}_{z}_{l}")
    for x, y, z in itertools.product(range(n), repeat=3):
        cnf.extend(amo_encoder.at_most_one_pairwise([exp_2(x, y, z, l) for l in range(n)]))
        for l, m in itertools.product(range(n), repeat=2):
            cnf.append([-exp(x, y, m), -exp(m, z, l), exp_2(x, y, z, l)])
            cnf.append([-mul_(y, z, m), -exp(x, m, l), exp_2(x, y, z, l)])

    # Wilkie's disequality at (a,b) = (0,4), in Zhang's formulation
    # the idea is to construct the parse tree of the expression
    c = lambda l: idpool.id(f"wilkie_c_{l}")
    P = lambda l: idpool.id(f"wilkie_P_{l}")
    Q = lambda l: idpool.id(f"wilkie_Q_{l}")
    ac = lambda l: idpool.id(f"wilkie_ac_{l}")
    R = lambda l: idpool.id(f"wilkie_R_{l}")
    one_c = lambda l: idpool.id(f"wilkie_one_c_{l}")
    cc = lambda l: idpool.id(f"wilkie_cc_{l}")
    S = lambda l: idpool.id(f"wilkie_S_{l}")

    P_a = lambda l: idpool.id(f"wilkie_P_a_{l}")
    Q_a = lambda l: idpool.id(f"wilkie_Q_a_{l}")
    P_a_Q_a = lambda l: idpool.id(f"wilkie_P_a_Q_a_{l}")
    left_1 = lambda l: idpool.id(f"wilkie_left_1_{l}")
    R_b = lambda l: idpool.id(f"wilkie_R_b_{l}")
    S_b = lambda l: idpool.id(f"wilkie_S_b_{l}")
    R_b_S_b = lambda l: idpool.id(f"wilkie_R_b_S_b_{l}")
    left_2 = lambda l: idpool.id(f"wilkie_left_2_{l}")
    left = lambda l: idpool.id(f"wilkie_left_{l}")

    P_b = lambda l: idpool.id(f"wilkie_P_b_{l}")
    Q_b = lambda l: idpool.id(f"wilkie_Q_b_{l}")
    P_b_Q_b = lambda l: idpool.id(f"wilkie_P_b_Q_b_{l}")
    right_1 = lambda l: idpool.id(f"wilkie_right_1_{l}")
    R_a = lambda l: idpool.id(f"wilkie_R_a_{l}")
    S_a = lambda l: idpool.id(f"wilkie_S_a_{l}")
    R_a_S_a = lambda l: idpool.id(f"wilkie_R_a_S_a_{l}")
    right_2 = lambda l: idpool.id(f"wilkie_right_2_{l}")
    right = lambda l: idpool.id(f"wilkie_right_{l}")

    def one_value(t):
        cnf.extend(amo_encoder.at_most_one_pairwise([t(l) for l in range(n)]))

    def op_cc(t, op, x, y):
        one_value(t)
        for l in range(n):
            cnf.append([-op(x, y, l), t(l)])

    def op_vc(t, op, x, y):
        one_value(t)
        for i, l in itertools.product(range(n), repeat=2):
            cnf.append([-x(i), -op(i, y, l), t(l)])

    def op_cv(t, op, x, y):
        one_value(t)
        for j, l in itertools.product(range(n), repeat=2):
            cnf.append([-y(j), -op(x, j, l), t(l)])

    def op_vv(t, op, x, y):
        one_value(t)
        for i, j, l in itertools.product(range(n), repeat=3):
            cnf.append([-x(i), -y(j), -op(i, j, l), t(l)])

    op_cc(c, mul_, 0, 0)          # c = a*a
    op_cc(P, add_, 1, 0)          # P = 1+a
    op_vv(Q, add_, P, c)          # Q = P+c
    op_cv(ac, mul_, 0, c)         # ac = a*c
    op_cv(R, add_, 1, ac)         # R = 1+a*c
    op_cv(one_c, add_, 1, c)      # one_c = 1+c
    op_vv(cc, mul_, c, c)         # cc = c*c
    op_vv(S, add_, one_c, cc)     # S = 1+c+c*c

    op_vc(P_a, exp, P, 0)
    op_vc(Q_a, exp, Q, 0)
    op_vv(P_a_Q_a, add_, P_a, Q_a)
    op_vc(left_1, exp, P_a_Q_a, 4)
    op_vc(R_b, exp, R, 4)
    op_vc(S_b, exp, S, 4)
    op_vv(R_b_S_b, add_, R_b, S_b)
    op_vc(left_2, exp, R_b_S_b, 0)
    op_vv(left, mul_, left_1, left_2)

    op_vc(P_b, exp, P, 4)
    op_vc(Q_b, exp, Q, 4)
    op_vv(P_b_Q_b, add_, P_b, Q_b)
    op_vc(right_1, exp, P_b_Q_b, 0)
    op_vc(R_a, exp, R, 0)
    op_vc(S_a, exp, S, 0)
    op_vv(R_a_S_a, add_, R_a, S_a)
    op_vc(right_2, exp, R_a_S_a, 4)
    op_vv(right, mul_, right_1, right_2)

    for l in range(n):
        cnf.append([-left(l), -right(l)])

   
    def add_table_lex_leader(left, right):
        current = []
        image = []
        def swap(value, left, right):
            if value == left:
                return right
            if value == right:
                return left
            return value
        for op in [add_, mul_, exp]:
            pairs = None
            if op == add_ or op == mul_:
                pairs = itertools.combinations(range(n), 2)
            else:
                pairs = itertools.product(range(n), repeat=2)
            for x, y in pairs:
                for value in range(n):
                    current.append(op(x, y, value))
                    image.append(
                    op(swap(x, left, right), swap(y, left, right), swap(value, left, right))
                    )
        lex.lex_smaller_eq(cnf, idpool, current, image, maxcomparisons=None)

    def add_table_transposition_lex_leaders(protected=(0,1,2,3,4)):
        protected = set(value for value in protected if value < n)
        labels = [value for value in range(n) if value not in protected]

        # all transpositions
        for left, right in itertools.combinations(labels, 2):
            add_table_lex_leader(left, right)

        # adjacent transpositions (in some cases just enforcing this was more efficient)
        # for i in range(len(labels)-1):
        #     add_table_lex_leader(labels[i], labels[i+1])

    add_table_transposition_lex_leaders()

    cnf.append([add_(1, 1, 2)]) # Zhang's
    cnf.append([add_(2, 1, 3)]) # Zhang's
    cnf.append([-add_(1, 0, 1)]) # 1 + a != 1
    cnf.append([-add_(2, 0, 1)]) # 2 + a != 1
    cnf.append([-add_(0, 0, 1)]) # a + a != 1
    cnf.append([-mul_(0, 0, 1)]) # a * a != 1
    cnf.append([-add_(0, 0, 0)]) # a + a != a
    cnf.append([-mul_(0, 0, 0)]) # a * a != a
    cnf.append([-add_(1, 0, 0)]) # 1 + a != a
    cnf.append([-add_(2, 0, 0)]) # 2 + a != a


    cnf.append([exp(2, 0, 4)])

    # Lee
    for x in range(n):
        cnf.append([-mul_(0, x, 4)])

    # Jackson
    # 4 != x + (y*0) for all x,y in {1,2,3}
    for y in [1,2,3]:
        for z in range(n):
            for x in [1,2,3]:
                cnf.append([-add_(x, z, 4), -mul_(y, 0, z)])
    
    for x in range(n):
        for i, l in itertools.product(range(n), repeat=2):
            cnf.append([-P(i), -Q(l), -mul_(i, x, l)])  # Q != P*x
            cnf.append([-Q(i), -P(l), -mul_(i, x, l)])  # P != Q*x
            cnf.append([-R(i), -S(l), -mul_(i, x, l)])  # S != R*x
            cnf.append([-S(i), -R(l), -mul_(i, x, l)])  # R != S*x

    if return_idpool:
        return cnf, idpool
    return cnf

def print_table(name, table):
    width = max(1, max(len(str(value)) for row in table for value in row))
    print(name)
    print(" " * (width + 2) + " ".join(f"{i:>{width}}" for i in range(len(table))))
    for i, row in enumerate(table):
        print(f"{i:>{width}}: " + " ".join(f"{value:>{width}}" for value in row))
    print()


def decode(n, model, add_only=False):
    idpool = IDPool()
    add_, mul_, exp, _ = operation_accessors(n, idpool)
    model = set(lit for lit in model if lit > 0)

    def value(var):
        for k in range(n):
            if var(k) in model:
                return k
        return "?"

    add_table = [[value(lambda k, i=i, j=j: add_(i, j, k)) for j in range(n)] for i in range(n)]
    if add_only:
        print_table("addition", add_table)
        return
        
    mul_table = [[value(lambda k, i=i, j=j: mul_(i, j, k)) for j in range(n)] for i in range(n)]
    exp_table = [[value(lambda k, i=i, j=j: exp(i, j, k)) for j in range(n)] for i in range(n)]

    print_table("addition", add_table)
    print_table("multiplication", mul_table)
    print_table("exponentiation", exp_table)

def solve_and_decode(n, cnf):
    solver = Solver(name="Cadical195", bootstrap_with=cnf.clauses)
    try:
        if not solver.solve():
            print("UNSAT")
            return False
        decode(n, solver.get_model())
        return True
    finally:
        solver.delete()

def gen_instances_from_addition_models(n, models, model_indices=None, output_dir="formulas/post-add"):
    num_models_per_addition = {}
    if model_indices is None:
        model_indices = range(len(models))
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    for model_index in model_indices:
        if model_index < 0 or model_index >= len(models):
            raise IndexError(f"model index {model_index} is outside 0..{len(models) - 1}")
        model = models[model_index]
        cnf = encode(n)
        for lit in model:
            # DIMACS model lines use 0 as a terminator, not as a literal.
            if lit == 0:
                continue
            cnf.append([lit])
        # solver = Solver(name="Cadical195", bootstrap_with=cnf.clauses)
        # num_models = 0
        # for model in solver.enum_models():
        #     num_models += 1
        #     print(f"Found model #{num_models} for addition # {model_index}")
            
        # num_models_per_addition[model_index] = num_models
        cnf_filename = output_dir / f"wilkies_{n}_{model_index}.cnf"
        cnf.to_file(str(cnf_filename))
        print(f"Serialized to {cnf_filename}")
        
def process_models(filename):
    models = []
    current_model = []
    with open(filename, "r") as f:
        for line in f:
            line = line.strip()
            if not line.startswith("v "):
                continue
            for lit in (int(token) for token in line.split()[1:]):
                if lit == 0:
                    models.append(current_model)
                    current_model = []
                else:
                    current_model.append(lit)
    if current_model:
        models.append(current_model)
    print(f"Found {len(models)} models")
    return models

def selected_model_indices(model_count, index=None, start=None, stop=None):
    if index is not None:
        if start is not None or stop is not None:
            raise ValueError("--post-addition-index cannot be combined with range options")
        indices = [index]
    else:
        start = 0 if start is None else start
        stop = model_count if stop is None else stop
        if start < 0 or stop < start or stop > model_count:
            raise ValueError(f"model range {start}..{stop} is outside 0..{model_count}")
        indices = range(start, stop)

    for model_index in indices:
        if model_index < 0 or model_index >= model_count:
            raise ValueError(f"model index {model_index} is outside 0..{model_count - 1}")
    return indices


if __name__ == "__main__":
    argparser = argparse.ArgumentParser()
    argparser.add_argument("-n", "--n", type=int, default=5)
    argparser.add_argument("--decode", action="store_true", help="solve with PySAT and print operation tables")

    argparser.add_argument("--decode-file", type=str, default=None)
    argparser.add_argument("--decode-add-only", action="store_true", help="decode only addition table")
    argparser.add_argument("--gen-post-addition", type=str, default=None)
    argparser.add_argument("--post-addition-index", type=int, default=None, help="generate only this addition-model index")
    argparser.add_argument("--post-addition-start", type=int, default=None, help="first addition-model index to generate")
    argparser.add_argument("--post-addition-stop", type=int, default=None, help="exclusive end addition-model index to generate")
    argparser.add_argument("--post-addition-output-dir", type=str, default="formulas/post-add", help="directory for post-addition CNFs")

    args = argparser.parse_args()

    if args.decode_file:
        models = process_models(args.decode_file)
        for model in models:
            decode(args.n, model, add_only=args.decode_add_only)
        exit(0)
    if args.gen_post_addition:
        models = process_models(args.gen_post_addition)
        model_indices = selected_model_indices(
            len(models),
            index=args.post_addition_index,
            start=args.post_addition_start,
            stop=args.post_addition_stop,
        )
        gen_instances_from_addition_models(
            args.n,
            models,
            model_indices=model_indices,
            output_dir=args.post_addition_output_dir,
        )
        exit(0)

    cnf = encode(args.n)
    filename = f"wilkies_{args.n}.cnf"
    cnf.to_file(filename)
    print(f"Serialized to {filename}")
    
    if args.decode:
        solve_and_decode(args.n, cnf)
