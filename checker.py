
def check(add, mult, exp):
    n = len(add)


    # 1. Check commutativity of addition
    for i in range(n):
        for j in range(n):
            if add[i][j] != add[j][i]:
                return False
    
    # 2. Check associativity of addition
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if add[i][add[j][k]] != add[add[i][j]][k]:
                    return False

    # 3. Check x * 1 = x
    for i in range(n):
        if mult[i][1] != i:
            return False

    # 4. Check commutativity of multiplication
    for i in range(n):
        for j in range(n):
            if mult[i][j] != mult[j][i]:
                return False

    # 5. Check associativity of multiplication
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if mult[i][mult[j][k]] != mult[mult[i][j]][k]:
                    return False

    # 6. Check distributivity of * over +
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if mult[i][add[j][k]] != add[mult[i][j]][mult[i][k]]:
                    return False

    # 7. Check 1^x = 1
    for i in range(n):
        if exp[1][i] != 1:
            return False

    # 8. Check x^1 = x
    for i in range(n):
        if exp[i][1] != i:
            return False

    # 9. i^(j + k) = i^j * i^k
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if exp[i][add[j][k]] != mult[exp[i][j]][exp[i][k]]:
                    return False

    # 10. (i * j)^k = i^k * j^k
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if exp[mult[i][j]][k] != mult[exp[i][k]][exp[j][k]]:
                    return False

    # 11. (i^j)^k = i^(j * k)
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if exp[exp[i][j]][k] != exp[i][mult[j][k]]:
                    return False

    # Fail wilkie's for 0, 4.
    x = 0
    y = 4
    P = add[1][x]
    Q = add[1][add[x][mult[x][x]]]
    R = add[1][mult[x][mult[x][x]]]
    S = add[1][add[mult[x][x]][mult[x][mult[x][mult[x][x]]]]]
    L1 = add[exp[P][x]][exp[Q][x]]
    L2 = add[exp[R][y]][exp[S][y]]
    R1 = add[exp[P][y]][exp[Q][y]]
    R2 = add[exp[R][x]][exp[S][x]]
    return mult[exp[L1][y]][exp[L2][x]] != mult[exp[R1][x]][exp[R2][y]]

def process_table(table_lines):
    n = len(table_lines)
    table = [None for _ in range(n)]
    for i, line in enumerate(table_lines):
        if line.strip() == '':
            continue
       
        tokens = line.split(': ')[1].split()
        row = list(map(int, tokens))
        # print(f"row {i}: {row}")
        table[i] = row
    return table

def run_checker(filename):
    with open(filename, 'r') as f:
        total_text = f.read()
        parts = total_text.split('\n\n')
        addition = parts[0].split('\n')[2:]
        multiplication = parts[1].split('\n')[2:]
        exponentiation = parts[2].split('\n')[2:]
        add_table = process_table(addition)
        mult_table = process_table(multiplication)
        exp_table = process_table(exponentiation)
        print(check(add_table, mult_table, exp_table))
        

if __name__ == "__main__":
    run_checker("output.txt")