import z3
import SATfunctions2 as SATf
from scipy.optimize import minimize
from math import log,ceil

def read_input_file(file_path):
    with open(file_path, 'r') as file:
        m = int(file.readline().strip())
        n = int(file.readline().strip())
        #s = [0 for _ in range(m)]
        s = list(map(int, file.readline().strip().split()))
        w = list(map(int, file.readline().strip().split()))

        # Inizializza la matrice delle distanze D
        D = [[0 for _ in range(n+1)] for _ in range(n+1)]

        # Leggi i valori della matrice delle distanze dalla restante parte del file
        for i in range(n+1):
            row_values = list(map(int, file.readline().strip().split()))
            D[i] = row_values

    #U vettore di n variabili (1 e n) con valore da 1 a n

    return m, n, s, w, D

def SAT_mcp(m, n, s, w, D):
    mb = SATf.int2boolList(m)
    nb = SATf.int2boolList(n)
    sb = [SATf.int2boolList(s[i]) for i in range(m)]
    wb = [SATf.int2boolList(w[i]) for i in range(n)]
    Db = [[SATf.int2boolList(D[i][j]) for j in range(n+1)] for i in range(n+1)]
    # Inizializza il solver Z3
    solver = z3.Solver()

    X = [[[z3.Bool(f'X_{i}_{j}_{k}') for k in range(n)] for j in range(n)] for i in range(m)]  #i courier, j item, k order

    #C1     each item must be delivered once
    for j in range(n):
        solver.add(SATf.exactly_one_T([X[i][j][k] for i in range(m) for k in range(n)]))

    #C2 all zeros at the end of the order (to avoid symmetries)
    for i in range(m):
        for k in range(1,n):
            solver.add(z3.Or(SATf.at_least_one_T([X[i][j][k-1] for j in range(n)]),SATf.all_F([X[i][j][k-1] for j in range(n)])))

    #C3   weight constraint
    for i in range(m):
        solver.add(SATf.gte(sb[i],SATf.sum_b_list([SATf.enable(wb[j],SATf.at_least_one_T([X[i][j][k] for k in range(n)])) for j in range(n)])))

    #loss
    lb = min(D[n])+min([D[i][n] for i in range(n+1)])
    ub = sum([max(D[i]) for i in range(n+1)])

    if solver.check() == z3.sat:
        model = solver.model()
        print("Sat:")
        print(model)
    else:
        print("Unsat")


m,n,s,w,D = read_input_file('../instances/SAT_instance.txt')
print(m,n,s,w,D)
SAT_mcp(m, n, s, w, D)


