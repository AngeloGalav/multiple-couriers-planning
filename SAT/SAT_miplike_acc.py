from itertools import combinations
from math import ceil, floor, log2
import z3
from z3 import Bool, Implies, Not, And
import SATfunctions2 as sf
import numpy as np
import time
from sat_utils import *

time_limit, instance, verbose, strategy = get_args()
m,n,l,s,D,LB,UB = get_input(instance)
mb, nb, lb, sb, Db = binarize_input(m, n, l, s, D)

name = "miplike_" + strategy

'''
Logical formulations:
-- C1 --
for each i in 1..n: AtLeastOnce(k in 1..m, j in 1..n+1){X[i, j, k]} //each node has to be departed from atleast once

for each j in 1..n: AtLeastOnce(k in 1..m, i in 1..n+1){X[i, j, k]} //each node has to be arrived to atleast once

-- C2 --
for each i in 1..n, for each k in 1..m: Y[i, k] <-> AtLeastOne(j in 1..n+1){X[i, j, k]} //courier k departs from node i <--> item i is assigned to k
for each j in 1..n, for each k in 1..m: Y[j, k] <-> AtLeastOne(i in 1..n+1){X[i, j, k]} //courier k arrives at node j <--> item j is assigned to k

-- C2.5 --
each item is assigned to exactly one courier

for each i in 1..n: ExaxtlyOne(k in 1..m){Y[i, k]}

-- C3 --
for each k in 1..m: sum(i in 1..n){s[i]*Y[i, k]} <= l[k]

-- C4 --
for each k in 1..m: AtMostOne(j in 1..n){X[n+1, j, k]} //each courier leaves the origin once
for each k in 1..m: AtMostOne(i in 1..n){X[i, n+1, k]} //each courier arrives at the origin once

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

# variable declarations
X = [[[Bool(f"X_{k},{i},{j}") if i != j else None for j in range(n+1)] for i in range(n+1)] for k in range(m)]
Y = [[Bool(f"Y_{k},{i}") for i in range(n)]for k in range(m)]
U = [[Bool(f"U_{i}[{q}]") for q in range(floor(log2(n))+1)] for i in range(n)]
C = [[Bool(f"C_{k}[{q}]") for q in range(floor(log2(UB))+1)] for k in range(m)]
StartCost = [[Bool(f"StartCost_{k}[{q}]") for q in range(max([len(Db[n][j]) for j in range(n)]))] for k in range(m)]
DepCost = [[[Bool(f"DepCost_{k},{i}[{q}]") for q in range(max([len(Db[i][j]) for j in range(n+1)]))] for i in range(n)] for k in range(m)]
MaxCost = [Bool(f"MaxCost[{q}]") for q in range(floor(log2(UB))+1)]

# constraints declaration

start_time = time.time()

# C1
for i in range(n):
    solver.add(sf.at_least_one_T([X[k][i][j] for j in range(n+1) if i != j for k in range(m)]))
    solver.add(sf.at_least_one_T([X[k][j][i] for j in range(n+1) if i != j for k in range(m)]))
    for k in range(m):
        solver.add(sf.at_most_one_T([X[k][j][i] for j in range(n+1) if i != j]))

if verbose:
    print(f"constraint C1 added")

# C2
for i in range(n):
    for k in range(m):
        solver.add(Y[k][i] == sf.at_least_one_T([X[k][i][j] for j in range(n+1) if i != j]))
        solver.add(Y[k][i] == sf.at_least_one_T([X[k][j][i] for j in range(n+1) if i != j]))        

# C2.5
for i in range(n):
    solver.add(sf.exactly_one_T([Y[k][i] for k in range(m)]))

if verbose:
    print(f"constraint C2 added")

# C3
for k in range(m):
    sizes_b = [sb[i] for i in range(n)]
    mask = Y[k]
    solver.add(sf.lte(sf.masked_sum_n(sizes_b, Y[k]), lb[k]))

if verbose:
    print(f"constraint C3 added")

# C4
for k in range(m):
    solver.add(sf.exactly_one_T([X[k][n][j] for j in range(n)]))
    solver.add(sf.exactly_one_T([X[k][i][n] for i in range(n)]))
    solver.add(sf.at_least_one_T([Y[k][i] for i in range(n)]))

if verbose:
    print(f"constraint C4 added")

# C5
if time_limit - floor(time.time() - start_time) > 0:
    for i in range(n):
        for j in range(n):
            if i != j:
                arc_traversed = sf.at_least_one_T([X[k][i][j] for k in range(m)])
                solver.add(Implies(arc_traversed, sf.gt(U[j], U[i])))

if verbose:
    print(f"constraint C5 added")

# cost constraints
if time_limit - floor(time.time() - start_time) > 0:
    for k in range(m):
        for j in range(n):
            solver.add(Implies(X[k][n][j], sf.eq(Db[n][j], StartCost[k])))

    for k in range(m):
        for i in range(n):
            solver.add(Implies(Not(Y[k][i]), sf.all_F(DepCost[k][i])))
            for j in range(n+1):
                if i != j:
                    solver.add(Implies(X[k][i][j], sf.eq(D[i][j], DepCost[k][i])))

    for k in range(m):
        solver.add(sf.eq(C[k], sf.sum_b_list([DepCost[k][i] for i in range(n)]+[StartCost[k]])))

    solver.add(sf.max_elem([C[k] for k in range(m)], MaxCost))
    solver.add(sf.gte(MaxCost, sf.int2boolList(LB)))

if verbose:
    print(f"cost constraints added")

if verbose:
    print(f"Time spent for constraints: {time.time() - start_time}")

const_time = time.time() - start_time
remaining_time = max(0, time_limit - floor(time.time() - start_time))

# -- solve and visualization --

def printTour(model, k):
    print(np.array(
        [[1 if j != i and model[X[k][i][j]] else 0 for j in range(n+1)] for i in range(n+1)]
    ))

def printAssignments(model, k):
    print(np.array(
        [1 if model[Y[k][i]] else 0 for i in range(n)]
    ))

def print_cost_courier(model, k):
    c_b = [model[C[k][i]] for i in range(len(C[k]))]
    print(f"Cost: {sf.bool2int(c_b)}")

def print_solution(model):
    for k in range(m):
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
    dc = [sf.bool2int([model[DepCost[k][i][q]] for q in range(len(DepCost[k][i]))]) for i in range(n)]
    print(f"Departure cost accs: {dc}")

if strategy == 'binary':
    model, search_time = binary_search(UB, LB, MaxCost, solver, remaining_time, verbose)
elif strategy == 'sequential':
    model, search_time = seqential_search(UB, LB, MaxCost, solver, remaining_time, verbose)
else:
    raise Exception("Invalid strategy argument")

def getSolution():
    if model is None:
        obj = 0
        sol = "N/A"
    else:
        obj = sf.bool2int([model[MaxCost[q]] for q in range(len(MaxCost))])
        sol = []
        for k in range(m):
            path = []
            current = n
            dest = 0
            path = []
            while(dest != n):
                dest = 0
                while(current == dest or model[X[k][current][dest]] == False):
                    dest += 1
                if dest != n:
                    path.append(dest+1)
                    current = dest
            sol.append(path)
    return round(const_time+search_time, 2), obj, sol

save_solution(instance, name, getSolution())

if verbose and model is not None:
    print_costs()
    print_solution(model)

