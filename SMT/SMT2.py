import uuid
import z3
import numpy as np
from z3 import And, Bool, Not, Or, Implies
from itertools import combinations
import sys
sys.path.append('./')
from data_handlers import saveAsJson, computeBounds, parseInstance
from argparse import ArgumentParser
import time


# --- ARGS ---
parser = ArgumentParser()
parser.add_argument("-s", "--solver", type=str, choices=['Z3'], default='Z3')
parser.add_argument("-t", "--timelimit", type=int, default=300)
parser.add_argument("-i", "--instance", type=int, default=1)

args = parser.parse_args()._get_kwargs()

solv_arg = args[0][1]
time_limit = args[1][1]
instance = args[2][1]

inst_name = "inst"+str(instance).zfill(2)+".dat"
m,n,l,s,D = parseInstance('./instances/'+inst_name)
low,high = computeBounds(D, m, n)


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
for each k in 1..m: exactlyOneT(j in 1..n){X[n+1, j, k]} //each courier must leave the origin  once

for each k in 1..m: exactlyOneT(i in 1..n){X[i, n+1, k]} //each courier must arrive at the origin  once

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
    solver.add(exactly_one_T([X[n, j, k] for j in range(n)]))
    solver.add(exactly_one_T([X[i, n, k] for i in range(n)]))

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
solver.add(MaxCost>=low)
solver.add(MaxCost<=high)

bestModel = None
start_time = time.time()
# binary search for the minimum cost solution
while high > low:
    mid = (high + low)//2
    #print(f"trying MaxCost <= {mid}")
    res = solver.check(MaxCost<=mid)
    if res == z3.sat:
        print(f"Sat for {mid}")
        high = mid
        bestModel = solver.model()
    else:
        print(f"Unsat for {mid}")
        low = mid+1
    #print()

#print(f"final max cost: {high}")
#sol = print_solution(bestModel)
t = time.time() - start_time
def getSolution(status, best, n, m, t):
    if t >= time_limit*1000 - 1:
        t = time_limit
    if status != 1:
        obj = 0
        sol = "N/A"
    else:
        obj = best[MaxCost]
        sol = []
        for k in range(m):
            path = []
            current = n
            dest = 0
            path = []
            while(dest != n):
                dest = 0
                while(current == dest or best[X[current, dest, k]] != 1):
                    dest += 1
                if dest != n:
                    path.append(dest)
                    current = dest
            sol.append(path)
    return t, obj, sol


saveAsJson(str(instance), solv_arg, "./res/SMT/", getSolution(res, bestModel, n, m, t))