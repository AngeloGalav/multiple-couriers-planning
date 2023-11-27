import sys, time, z3
import numpy as np
from math import floor
from z3 import Int, Sum, Implies, If, And, Or
from argparse import ArgumentParser
from itertools import combinations
sys.path.append('./')
from data_handlers import computeBounds, parseInstance, saveAsJson
from utils import print_input


# input
parser = ArgumentParser()
parser.add_argument("-t", "--timelimit", type=int, default=300)
parser.add_argument("-i", "--instance", type=int, default=3)
parser.add_argument("-v", "--verbose", action='store_true')

args = parser.parse_args()._get_kwargs()

time_limit = args[0][1]
instance = args[1][1]
verbose = args[2][1]

inst_name = "inst"+str(instance).zfill(2)+".dat"
m,n,l,s,D = parseInstance('./instances/'+inst_name)
LB, UB = computeBounds(D, m, n)

name = "cplike"

solver = z3.Optimize()

x = [Int(f"x_{i}") for i in range(n)]
tour = [Int(f"tour_{j}") for j in range(n)]
count = [Int(f"count_{k}") for k in range(m)]

StartCost = [Int(f"StartCost_{k}") for k in range(m)]
DepCost = [[Int(f"DepCost_{k}_{i}") for i in range(n)] for k in range(m)]
C = [Int(f"C_{k}") for k in range(m)]
MaxCost = Int('MaxCost')

# --- constraints definition

start_time = time.time()

# domains
for i in range(n):
    solver += x[i] < m
    solver += x[i] >= 0
    solver += tour[i] > 0

for k in range(m):
    solver += count[k] > 0

# C1
for k in range(m):
    load = Sum([If(x[i]==k, s[i], 0) for i in range(n)])
    solver += load <= l[k]

# C2
for i, j in combinations(range(n), r=2):
    solver += Implies(x[i]==x[j], tour[i] != tour[j])

# C3 + count constraints
for k in range(m):
    solver += count[k] == Sum([x[i]==k for i in range(n)])

for i in range(n):
    for k in range(m):
        solver += Implies(x[i]==k, tour[i] <= count[k])

# cost constraints
for k in range(m):
    for j in range(n):
        solver += Implies(And(tour[j]==1, x[j]==k), StartCost[k]==D[n][j])

for k in range(m):
    for i in range(n):
        is_last_item = count[k] == tour[i]
        solver += Implies(x[i] != k, DepCost[k][i]==0) # if courier k doesn't deliver i, then DepCost[i] = 0
        solver += Implies(And(x[i]==k, is_last_item), DepCost[k][i] == D[i][n])
        for j in range(n):
            if i != j:
                travels_arc = And(And(x[i]==k, x[j]==k), tour[j]==(tour[i]+1))
                solver += Implies(travels_arc, DepCost[k][i] == D[i][j])

for k in range(m):
    solver += C[k] == (Sum([DepCost[k][i] for i in range(n)]) + StartCost[k])
    solver += MaxCost >= C[k]

solver += Or([MaxCost == C[k] for k in range(m)])
solver += MaxCost <= UB
solver += MaxCost >= LB

if verbose:
    print(f"Constraints added in time {time.time()-start_time}")

const_time = time.time() - start_time
remaining_time = max(0, time_limit - floor(time.time() - start_time))

# --- visualization
def print_accs(model, k):
    print(f"Start cost acc: {model[StartCost[k]]}")
    print(f"Departure cost accs: {[model[DepCost[k][i]] for i in range(n)]}")

def print_solution(model):
    x_vals = [model[x[i]] for i in range(n)]
    tour_vals = [model[tour[i]] for i in range(n)]
    count_vals = [model[count[k]] for k in range(m)]
    print(f"Assignments: {x_vals}")
    print(f"Tours      : {tour_vals}")
    print(f"Count      : {count_vals}")
    print(f"Objective: {model[MaxCost]}\n")
    for k in range(m):
        print(f"-- courier {k}")
        print_accs(model, k)
        print(f"Path cost: {model[C[k]]}")

# --- solving
res = solver.minimize(MaxCost)
solver.set("timeout", floor(remaining_time)*1000)
start_time = time.time()
solver.check()
search_time = time.time()-start_time
model = solver.model()

def getSolution():
    if model is None:
        obj = 0
        sol = "N/A"
    else:
        obj = int(str(model[MaxCost]))
        x_vals = np.array([int(str(model[x[i]])) for i in range(n)], dtype=np.int32)
        tour_vals = np.array([int(str(model[tour[i]])) for i in range(n)])
        count_vals = [int(str(model[count[k]])) for k in range(m)]
        sol = []
        for k in range(m):
            tour_k = tour_vals.copy()
            tour_k[x_vals != k] = n+1
            tour_k = tour_k.argsort() + 1
            sol.append(tour_k[:count_vals[k]].tolist())
    return round(const_time+search_time, 2), obj, sol

saveAsJson(str(instance), name, "./res/SMT/", getSolution())

if verbose and model is not None:
    print_input(D, s, l)
    print_solution(model)