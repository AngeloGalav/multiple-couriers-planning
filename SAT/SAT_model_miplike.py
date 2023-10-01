from math import ceil, floor, log2
import uuid
import z3
import SATfunctions2 as sf
import numpy as np
from z3 import And, Bool, Not, Xor, Or, Implies

m = 3
n = 7
l = [15, 10, 7]
s = [3, 2, 6, 8, 5, 4, 4]
D = [[0, 3, 3, 6, 5, 6, 6, 2], 
    [3, 0, 4, 3, 4, 7, 7, 3],
    [3, 4, 0, 7, 6, 3, 5, 3],
    [6, 3, 7, 0, 3, 6, 6, 4], 
    [5, 4, 6, 3, 0, 3, 3, 3], 
    [6, 7, 3, 6, 3, 0, 2, 4], 
    [6, 7, 5, 6, 3, 2, 0, 4], 
    [2, 3, 3, 4, 3, 4, 4, 0]]
LB = 8
UB = 51

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

for each j in 1..n, for each k in 1..m: Y[i, k] <-> AtLeastOne(i in 1..n+1){X[i, j, k]} //courier k arrives at node j <--> item j is assigned to k

Note: we use AtLeastOne instead of exactly one since C1 already ensures that a node is arrived to exactly once.  

-- C3 --
for each k in 1..m: sum(i in 1..n){s[i]*Y[i, k]} <= l[k]

-- C4 --
for each k in 1..m: atMostOne(j in 1..n){X[n+1, j, k]} //each courier can leave the origin at most once

for each k in 1..m: atMostOne(i in 1..n){X[i, n+1, k]} //each courier can arrive at the origin at most once

-- C5 --
for each k in 1..m, for each i in 1..n, for each j in 1..n (j != i): X[i, j, k] -> GreaterThan(U[j], U[i])

-- cost constraints --
for each k in 1..m: C[k] = sum(i in 1..n+1){sum(j in 1..n+1){D[i, j]*X[i, j, k]}}
is_max(MaxCost, C[k] for k in 1..m)

-- domain constraints --
for each i in 1..n: 0 <= U[i] <= n-1
for each k in 1..m: C[k] <= UB
LB <= MaxCost <= UB
'''

solver = z3.Solver()

# variable declarations (indexing starts from 1)
X={}
Y={}
U={}
C={}
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
    solver.add(sf.at_most_one_T([X[n+1, j, k] for j in myRange(n)]))
    solver.add(sf.at_most_one_T([X[i, n+1, k] for i in myRange(n)]))

# C5
for k in myRange(m):
    for i in myRange(n):
        for j in myRange(n):
            if i != j:
                solver.add(Implies(X[i, j, k], sf.gt(U[j], U[i])))

# cost constraints
costs_b = [cost(i, j) for i in myRange(n+1) for j in myRange(n+1) if i != j]
for k in myRange(m):
    mask = [X[i, j, k] for i in myRange(n+1) for j in myRange(n+1) if i != j]
    solver.add(sf.eq(C[k], sf.masked_sum_n(costs_b, mask)))

solver.add(sf.max_elem([C[k] for k in myRange(m)], MaxCost))

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
        print()

high = UB
low = LB
bestModel = None

while high != low:
    mid = low + (high - low)//2
    print(f"trying MaxCost <= {mid}")
    res = solver.check(sf.lte(MaxCost, sf.int2boolList(mid)))
    if res == z3.sat:
        print(f"Sat")
        high = mid
        bestModel = solver.model()
    else:
        print("Unsat")
        low = mid + 1
    print()

print(f"final max cost: {high}")
print_solution(bestModel)
