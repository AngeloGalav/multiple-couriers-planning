import z3
import SATfunctions2 as SATf
from scipy.optimize import minimize
from math import log,floor

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
    dist = [[] for _ in range(m)]    #list of distances of each courier
    loss = [z3.Bool(f'loss_{j}') for j in range(floor(log(ub,2))+1)]
    for i in range(m):
        dist[i] = SATf.sum_b_list([SATf.enable(Db[j1][j2],z3.And(X[i][j1][k-1],X[i][j2][k])) for j1 in range(n) for j2 in range(n) for k in range(1,n)])
        dist[i] = SATf.sum_b(dist[i],SATf.sum_b_list([SATf.enable(Db[n][j],X[i][j][0]) for j in range(n)]))
        #manca da aggiungere la distanza delritorno all'origine
        solver.add(SATf.gte(loss,dist[i]))
    
    solver.add(SATf.at_least_one_T([SATf.eq(loss,dist[i]) for i in range(m)]))
    solver.add(SATf.gte(loss,SATf.int2boolList(lb)))
    solver.add(SATf.gte(SATf.int2boolList(ub),loss))

    while ub != lb:
        mid = lb + (ub - lb)//2
        print(f"Loss <= {mid}")
        res = solver.check(SATf.lte(loss, SATf.int2boolList(mid)))
        if res == z3.sat:
            print(f"Sat")
            ub = mid
            bestModel = solver.model()
        else:
            print("Unsat")
            lb = mid + 1
        print()

m,n,s,w,D = read_input_file('./instances/instance1_unformatted.txt')
print(m,n,s,w,D)
SAT_mcp(m, n, s, w, D)