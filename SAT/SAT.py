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

    x = [[z3.Bool(f'x_{i}_{j}') for j in range(len(mb))] for i in range(n)]
    tour = [[z3.Bool(f'tour_{i}_{j}') for j in range(len(nb))] for i in range(n)]
    #Domains
    for i in range(n):
        solver.add(SATf.at_least_one_T(x[i]))
        solver.add(SATf.at_least_one_T(tour[i]))
        solver.add(SATf.lte(x[i],mb))
        solver.add(SATf.lte(tour[i],SATf.sum_b_list([SATf.eq(x[i],x[k]) for k in range(n)])))

    #C1     weight constraint
    for i in range(m):
        solver.add(SATf.gte(sb[i],SATf.sum_b_list([SATf.enable(wb[j],SATf.eq(SATf.int2boolList(i+1),x[j])) for j in range(n)])))
        solver.add(SATf.gte(sb[0],SATf.sum_b_list([SATf.enable(wb[0],SATf.eq(SATf.int2boolList(i+1),x[0]))])))

    #C2   a courier cannot deliver two items at the same time
    for i in range(n):
        for j in range(i+1,n):
            solver.add(z3.Or(SATf.ne(x[i],x[j]),SATf.ne(tour[i],tour[j])))

    #loss
    lb = min(D[n])+min([D[i][n] for i in range(n+1)])
    ub = sum([max(D[i]) for i in range(n+1)])
    dist = [[] for _ in range(m)]    #list of distances of each courier
    loss = [z3.Bool(f'loss_{j}') for j in range(ceil(log(ub,2)))]
    for i in range(m):
        dist[i]=SATf.sum_b_list([SATf.enable(Db[j][k],z3.And(SATf.eq(x[j],SATf.int2boolList(i+1)),SATf.eq(x[k],SATf.int2boolList(i+1)),SATf.eq(SATf.sum_b(x[j],[True]),x[k]))) for j in range(n) for k in range(n)])
        dist[i]=SATf.sum_b(dist[i],SATf.sum_b_list([SATf.enable(Db[n][j],z3.And(SATf.eq(SATf.int2boolList(i+1),x[j]),SATf.eq([True],tour[j]))) for j in range(n)]))
        dist[i]=SATf.sum_b(dist[i],SATf.sum_b_list([SATf.enable(Db[n][j],z3.And(SATf.eq(SATf.int2boolList(i+1),x[j]),SATf.eq(SATf.sum_b_list([SATf.eq(x[i],x[k]) for k in range(n)]),tour[j]))) for j in range(n)]))
        solver.add(SATf.gte(loss,dist[i]))

    solver.add(SATf.at_least_one_T([SATf.eq(loss,dist[i]) for i in range(m)]))
    solver.add(SATf.gte(loss,SATf.int2boolList(lb)))
    solver.add(SATf.gte(SATf.int2boolList(ub),loss))

    if solver.check() == z3.sat:
        model = solver.model()
        print("Sat:")
        print(model)
    else:
        print("Unsat")


m,n,s,w,D = read_input_file('../instances/SAT_instance.txt')
print(m,n,s,w,D)
SAT_mcp(m, n, s, w, D)


