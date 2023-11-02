from math import ceil, floor, log2
import uuid
import z3
import numpy as np
from z3 import And, Bool, Not, Xor, Or, Implies
from itertools import combinations

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

def at_least_one_T(bools) -> z3.BoolRef:                                      
    return Or(bools)

#at most 1  (max 1 T)
def at_most_one_T(bools) -> z3.BoolRef:
    if len(bools) <= 4: # base case
        return And([Not(And(b1, b2)) for b1, b2 in combinations(bools, 2)])
    
    # recursive step
    y = Bool(f"yamo_{str(uuid.uuid4())}")
    first = bools[:3]
    first.append(y)
    c_first = at_most_one_T(first)

    last = bools[3:]
    last.insert(0, Not(y))
    c_last = at_most_one_T(last)

    return And(c_first, c_last)

# 1 T
def exactly_one_T(bools) -> z3.BoolRef:                                      
    return And(at_most_one_T(bools), at_least_one_T(bools))


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
for each k in 1..m: atMostOne(j in 1..n){X[n+1, j, k]} //each courier can leave the origin at most once

for each k in 1..m: atMostOne(i in 1..n){X[i, n+1, k]} //each courier can arrive at the origin at most once

-- C5 --
for each k in 1..m, for each i in 1..n, for each j in 1..n (j != i): X[i, j, k] -> GreaterThan(U[j], U[i])

-- cost constraints --
for each k in 1..m: C[k] = sum(i in 1..n+1){sum(j in 1..n+1){D[i, j]*X[i, j, k]}}
is_max(MaxCost, C[k] for k in 1..m)

-- domain constraints --

for each k in 1..m: C[k] <= UB
LB <= MaxCost <= UB

Notes on domain constraints: 
1_ since imposing the constraint [for each i in 1..n: 1 <= U[i] <= n] is not strictly necessary for the correct
functioning of C5 (since the encodings are always non negative and a bound is given by the number of bits),
we don't do it in SAT, since it saves the solver some additional constraints (as opposed to mip where having
 bounds is neccessary and the stricter the domains the easier the search)

2_ foe MaxCost we set [MaxCost <= UB] as an assertion during binary search

3_ need to test weather [LB <= MaxCost] is a useful constraint for speeding up the solver or not (we still
use LB in the binary search)
'''

solver = z3.Optimize()

X={}
Y={}
U={}
C={}
M={}
M2 = {}
MaxCost = z3.Int(f"MaxCost")

for i in range(n+1):
    for j in range(n+1):
        for k in range(m):
            if i!=j:
                X[i, j, k] = Bool(f"X_{i},{j},{k}")
                M2[i, j, k]= z3.Int(f"M_{i}{j}{k}")

for i in range(n):
    for k in range(m):
        Y[i, k] = Bool(f"Y_{i},{k}")
        M[i, k] = z3.Int(f"M_{i},{k}")

for i in range(n):
    U[i] = z3.Int(f"U_{i}")

for k in range(m):
    C[k] = z3.Int(f"C_{k}")


# constraints declaration

# C1
for i in range(n):
    solver.add(exactly_one_T([X[i, j, k] for j in range(n+1) if i != j for k in range(m)]))

for j in range(n):
    solver.add(exactly_one_T([X[i, j, k] for i in range(n+1) if i != j for k in range(m)]))

# C2
for i in range(n):
    for k in range(m):
        solver.add(Y[i, k] == z3.Or([X[i, j, k] for j in range(n+1) if i != j]))

for j in range(n):
    for k in range(m):
        solver.add(Y[j, k] == z3.Or([X[i, j, k] for i in range(n+1) if i != j]))

# C3
for k in range(m):
    for i in range(n):
        solver.add(z3.Implies(Y[i,k],M[i,k]==s[i]))
        solver.add(z3.Implies(z3.Not(Y[i,k]),M[i,k]==0))
    solver.add(l[k]>=z3.Sum([M[i,k] for i in range(n)]))

# C4
for k in range(m):
    solver.add(at_most_one_T([X[n, j, k] for j in range(n)]))
    solver.add(at_most_one_T([X[i, n, k] for i in range(n)]))

# C5
for k in range(m):
    for i in range(n):
        for j in range(n):
            if i != j:
                solver.add(Implies(X[i, j, k], (U[j] > U[i])))

# cost constraints
for i in range(n+1):
    for j in range(n+1):
        for k in range(m):
            if i!=j:
                solver.add(z3.Implies(X[i,j,k],M2[i,j,k]==D[i][j]))
                solver.add(z3.Implies(z3.Not(X[i,j,k]),M2[i,j,k]==0))


for k in range(m):
    solver.add(C[k]==z3.Sum([M2[i,j,k] for i in range(n+1) for j in range(n+1) if i!=j]))
    solver.add(MaxCost>=C[k])
solver.add(at_least_one_T([MaxCost==C[k] for k in range(m)]))

### PROVARE
# solver.add(sf.gte(MaxCost, sf.int2boolList(LB)))

# -- solve and visualization --

def printTour(model, k):
    print(np.array(
        [[1 if j != i and model[X[i, j, k]] else 0 for j in range(n+1)] for i in range(n+1)]
    ))

def printAssignments(model, k):
    print(np.array(
        [1 if model[Y[i, k]] else 0 for i in range(n)]
    ))

def print_cost_courier(model, k):
    print(f"Cost: {model[C[k]]}")

def print_solution(model):
    for k in range(m):
        print(f"-- courier {k} --")
        printTour(model, k)
        print()
        printAssignments(model, k)
        print_cost_courier(model, k)
        print()

high = UB
low = LB
bestModel = None

# binary search for the minimum cost solution
while high != low:
    mid = low + (high - low)//2
    print(f"trying MaxCost <= {mid}")
    res = solver.check(MaxCost<=mid)
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