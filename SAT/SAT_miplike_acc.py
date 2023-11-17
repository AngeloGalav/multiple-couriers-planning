from math import ceil, floor, log2
import z3
from z3 import Bool, Implies, Not
import SATfunctions2 as sf
import numpy as np
import time, sys
from argparse import ArgumentParser
sys.path.append('./')
from dzn_handlers import saveAsJson, compute_bounds
from mcp_input_parser import actual_parse


parser = ArgumentParser()
parser.add_argument("-t", "--timelimit", type=int, default=300)
parser.add_argument("-i", "--instance", type=int, default=3)

args = parser.parse_args()._get_kwargs()

time_limit = args[0][1]
instance = args[1][1]

inst_name = "inst"+str(instance).zfill(2)+".dat"
m,n,l,s,D = actual_parse('./instances/'+inst_name)
LB, UB = compute_bounds(D, m, n)

print("UB LB computed!")

mb = sf.int2boolList(m)
nb = sf.int2boolList(n)
lb = [sf.int2boolList(l[i]) for i in range(m)]
sb = [sf.int2boolList(s[i]) for i in range(n)]
Db = [[sf.int2boolList(D[i][j]) for j in range(n+1)] for i in range(n+1)]

def cost(i, j):
    return Db[i-1][j-1]

def size(i):
    return sb[i-1]

def maxload(k):
    return lb[k-1]

def myRange(r):
    return range(1, r+1)

'''
Logical formulations:
-- C1 --
for each i in 1..n: ExactlyOne(k in 1..m, j in 1..n+1){X[i, j, k]} //each node has to be departed from once

for each j in 1..n: ExactlyOne(k in 1..m, i in 1..n+1){X[i, j, k]} //each node has to be arrived to once

-- C2 --
for each i in 1..n, for each k in 1..m: Y[i, k] <-> AtLeastOne(j in 1..n+1){X[i, j, k]} //courier k departs from node i <--> item i is assigned to k

for each j in 1..n, for each k in 1..m: Y[j, k] <-> AtLeastOne(i in 1..n+1){X[i, j, k]} //courier k arrives at node j <--> item j is assigned to k

Note: we use AtLeastOne instead of exactly one since C1 already ensures that a node is arrived to exactly once.  

-- C3 --
for each k in 1..m: sum(i in 1..n){s[i]*Y[i, k]} <= l[k]

-- C4 --
for each k in 1..m: ExactlyOne(j in 1..n){X[n+1, j, k]} //each courier leaves the origin once
for each k in 1..m: ExactlyOne(i in 1..n){X[i, n+1, k]} //each courier arrives at the origin once
for each k in 1..m: AtleastOne(i in 1..n){Y[i, k]} // this is implied

-- C5 --
for each k in 1..m, for each i in 1..n, for each j in 1..n (j != i): X[i, j, k] -> GreaterThan(U[j], U[i])

-- cost constraints --
// we create auxiliary variables we call 'accumulators' that contain the costs of the single arc costs of courier paths
StartAcc[k] contains the cost of the first step taken by courier k (cost to leave the origin)
DepAcc[i, k] contains the cost of the departure from node i for courier k, and it is 0 if courier k isn't assigned to such item

for each k in 1..m, for each j in 1..n: X[n+1, j, k] -> StartCost[k] = D[i, j]
for each k in 1..m, for each i in 1..n: Not(Y[i, k]) -> DepCost[i, k] = 0
for each k in 1..m, for each 1 in 1..n, for each j in 1..n+1 (j != i): X[i, j, k] -> DepCost[i, k] = D[i, j]

for each k in 1..m: C[k] = sum(i in 1..n)(DepCost[i, k])+StartCost[k]

is_max(MaxCost, C[k] for k in 1..m)

-- domain constraints --

for each k in 1..m: C[k] <= UB
LB <= MaxCost <= UB

Notes on domain constraints: 
1_ since imposing the constraint [for each i in 1..n: 1 <= U[i] <= n] is not strictly necessary for the correct
functioning of C5 (since the encodings are always non negative and a bound is given by the number of bits),
we don't do it in SAT, since it saves the solver some additional constraints (as opposed to mip where having
 bounds is neccessary and the stricter the domains the easier the search)

2_ for MaxCost we set [MaxCost <= UB] as an assertion during binary search

3_ need to test weather [LB <= MaxCost] is a useful constraint for speeding up the solver or not (we still
use LB in the binary search)
'''

solver = z3.Solver()

# variable declarations (indexing starts from 1)
X={}
Y={}
U={}
C={}
StartCost={}
DepCost={}
MaxCost = [Bool(f"MaxCost[{i}]") for i in range(floor(log2(UB))+1)]

for i in myRange(n+1):
    for j in myRange(n+1):
        for k in myRange(m):
            if i!=j:
                X[i, j, k] = Bool(f"X_{i},{j},{k}")

for i in myRange(n):
    for k in myRange(m):
        Y[i, k] = Bool(f"Y_{i},{k}")

for i in myRange(n):
    U[i] = [Bool(f"U_{i}[{q}]") for q in range(floor(log2(n))+1)]

for k in myRange(m):
    C[k] = [Bool(f"C_{k}[{q}]") for q in range(floor(log2(UB))+1)]

for k in myRange(m):
    StartCost[k] = [Bool(f"StartCost_{k}[{q}]") for q in range(max([len(Db[n][j]) for j in range(n)]))]
    for i in myRange(n):
        DepCost[i, k] = [Bool(f"ArrCost_{i},{k}[{q}]") for q in range(max([len(Db[i][j]) for j in range(n+1)]))]

# constraints declaration

# C1
for i in myRange(n):
    solver.add(sf.exactly_one_T([X[i, j, k] for j in myRange(n+1) if i != j for k in myRange(m)]))

for j in myRange(n):
    solver.add(sf.exactly_one_T([X[i, j, k] for i in myRange(n+1) if i != j for k in myRange(m)]))

# C2
for i in myRange(n):
    for k in myRange(m):
        solver.add(Y[i, k] == sf.at_least_one_T([X[i, j, k] for j in myRange(n+1) if i != j]))

for j in myRange(n):
    for k in myRange(m):
        solver.add(Y[j, k] == sf.at_least_one_T([X[i, j, k] for i in myRange(n+1) if i != j]))

# C3
for k in myRange(m):
    sizes_b = [size(i) for i in myRange(n)]
    mask = [Y[i, k] for i in myRange(n)]
    solver.add(sf.lte(sf.masked_sum_n(sizes_b, mask), maxload(k)))

# C4
for k in myRange(m):
    solver.add(sf.exactly_one_T([X[n+1, j, k] for j in myRange(n)]))
    solver.add(sf.exactly_one_T([X[i, n+1, k] for i in myRange(n)]))
    solver.add(sf.at_least_one_T([Y[i, k] for i in myRange(n)]))

# C5
for k in myRange(m):
    for i in myRange(n):
        for j in myRange(n):
            if i != j:
                solver.add(Implies(X[i, j, k], sf.gt(U[j], U[i])))

# cost constraints

for k in myRange(m):
    for j in myRange(n):
        solver.add(Implies(X[n+1, j, k], sf.eq(cost(n+1, j), StartCost[k])))

for k in myRange(m):
    for i in myRange(n):
        solver.add(Implies(Not(Y[i, k]), sf.all_F(DepCost[i, k])))
        for j in myRange(n+1):
            if i != j:
                solver.add(Implies(X[i, j, k], sf.eq(cost(i, j), DepCost[i, k])))

for k in myRange(m):
    solver.add(sf.eq(C[k], sf.sum_b_list([DepCost[i, k] for i in myRange(n)]+[StartCost[k]])))

solver.add(sf.max_elem([C[k] for k in myRange(m)], MaxCost))

solver.add(sf.gte(MaxCost, sf.int2boolList(LB)))

# -- solve and visualization --

def printTour(model, k):
    print(np.array(
        [[1 if j != i and model[X[i, j, k]] else 0 for j in myRange(n+1)] for i in myRange(n+1)]
    ))

def printAssignments(model, k):
    print(np.array(
        [1 if model[Y[i, k]] else 0 for i in myRange(n)]
    ))

def print_cost_courier(model, k):
    c_b = [model[C[k][i]] for i in range(len(C[k]))]
    print(f"Cost: {sf.bool2int(c_b)}")

def print_solution(model):
    for k in myRange(m):
        print(f"-- courier {k} --")
        printTour(model, k)
        print()
        printAssignments(model, k)
        print_cost_courier(model, k)
        print_accs(k)
        print()

def print_costs():
    print(np.array(
        [[D[i][j] for j in range(n+1)] for i in range(n+1)]
    ))
    print()

def print_accs(k):
    sc = [model[StartCost[k][i]] for i in range(len(StartCost[k]))]
    print(f"Start cost acc: {sf.bool2int(sc)}")
    dc = [sf.bool2int([model[DepCost[i, k][q]] for q in range(len(DepCost[i, k]))]) for i in myRange(n)]
    print(f"Departure cost accs: {dc}")

def search():
    model = None
    high = UB
    low = LB
    while high != low:
        mid = low + (high - low)//2
        print(f"trying MaxCost <= {mid}")
        remaining_time = time_limit - (time.time()-start_time)
        
        solver.set("timeout", ceil(remaining_time)*1000)
        res = solver.check(sf.lte(MaxCost, sf.int2boolList(mid)))
        
        if time_limit < (time.time()-start_time):
            return

        if res == z3.sat:
            print(f"Sat")
            high = mid
            model = solver.model()
        else:
            print("Unsat")
            low = mid + 1
        print()
    return model

print('Start!')
start_time = time.time()
model = search()
elapsed = round(time.time()-start_time, 2)

def getSolution():
    if model is None:
        obj = 0
        sol = "N/A"
    else:
        mod = model
        obj = sf.bool2int([mod[MaxCost[i]] for i in range(len(MaxCost))])
        sol = []
        for k in myRange(m):
            path = []
            current = n+1
            dest = 0
            path = []
            while(dest != n+1):
                dest = 1
                while(current == dest or mod[X[current, dest, k]] == False):
                    dest += 1
                if dest != n+1:
                    path.append(dest)
                    current = dest
            sol.append(path)
    return elapsed, obj, sol

saveAsJson(str(instance), "miplike_acc", "./res/SAT/", getSolution())

print_costs()
print_solution(model)

