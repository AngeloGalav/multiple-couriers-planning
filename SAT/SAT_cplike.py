from math import ceil, floor, log2
import z3
from z3 import Bool, Implies, Not, And
import SATfunctions2 as sf
import numpy as np
import time
from sat_utils import *
from itertools import combinations

name = "cplike"

time_limit, instance, verbose = get_args()
m,n,l,s,D,LB,UB = get_input(instance)
mb, nb, lb, sb, Db = binarize_input(m, n, l, s, D)

def cost(i, j):
    return Db[i-1][j-1]

def size(i):
    return sb[i-1]

def maxload(k):
    return lb[k-1]

def myRange(r):
    return range(1, r+1)

"""
x[1..n] - x[i] contains the index k of the courier assigned to item i (domain 0..m-1). 
tour[1..n] - If courier k has to deliver item i, tour[i] is the step of the path at which courier k deliver item i (domain 0..n-m)
count[1..m] - count[k] contains the number of items assigned to courier k

Note: simplify domain definition, we consider the indexes as starting from 0 in the implementation of constraints, so x[i] = k-1 means that
item i is assigned to courier k, and tour[i]=s-1 means an item is assigned at step s

C1 - The total weight of items transported by a courier must be lower or equal than the courier's 
maximum laod. We use vaiable x to define this constraint.

C2 - items delivered by the same courier must be delivered at different steps, so if x[j1]==x[j2], then
tour[j1] != tour[j2] must hold.

C3 - if courier i must deliver k items [k1..kp], the relative values of tour tour[k1..kp] must be
constrained between 1 and k (0 and k-1 in the encodings)
"""

# variable declaration

X = {}
Tour = {}
Count = {}

C = {}
StartCost = {}
DepCost = {}
MaxCost = [Bool(f"MaxCost[{i}]") for i in range(floor(log2(UB))+1)]

for i in myRange(n):
    X[i] = [Bool(f"X_{i}[{q}]") for q in range(floor(log2(m))+1)]
    Tour[i] = [Bool(f"Tour_{i}[{q}]") for q in range(floor(log2(n-m+1))+1)]

for k in myRange(m):
    Count[k] = [Bool(f"Count_{k}[{q}]") for q in range(floor(log2(n-m+1))+1)]

for k in myRange(m):
    C[k] = [Bool(f"C_{k}[{q}]") for q in range(floor(log2(UB))+1)]

for k in myRange(m):
    StartCost[k] = [Bool(f"StartCost_{k}[{q}]") for q in range(max([len(Db[n][j]) for j in range(n)]))]
    for i in myRange(n):
        DepCost[i, k] = [Bool(f"DepCost_{i},{k}[{q}]") for q in range(max([len(Db[i][j]) for j in range(n+1)]))]

solver = z3.Solver()

# constraint declarations

# domain costraints (Tour's upper bounds are defined in C3)
for i in myRange(n):
    solver += sf.lte(X[i], sf.int2boolList(m-1))

# C1
for k in myRange(m):
    mask = [sf.eq(X[i], sf.int2boolList(k-1)) for i in myRange(n)]
    load = sf.masked_sum_n(sb, mask)
    solver += sf.lte(load, maxload(k))

# C2
for i, j in combinations(myRange(n), r=2):
    solver += Implies(sf.eq(X[i], X[j]), sf.ne(Tour[i], Tour[j]))

# C3
for i in myRange(n):
    for k in myRange(m):
        kb = sf.int2boolList(k-1)
        solver += Implies(sf.eq(X[i], kb), sf.lt(Tour[i], Count[k]))

# count constraints
for k in myRange(m):
    kb = sf.int2boolList(k-1)
    solver += sf.eq(Count[k], sf.sum_b_list([[sf.eq(X[j], kb)] for j in myRange(n)]))
    solver += sf.at_least_one_T(Count[k])

# Cost constraints
for k in myRange(m):
    kb = sf.int2boolList(k-1)
    for j in myRange(n):
        solver += Implies(And(sf.all_F(Tour[j]), sf.eq(X[j], kb)), sf.eq(StartCost[k], cost(n+1, j)))
    
    for i in myRange(n):
        s_is_assigned = sf.eq(X[i], kb)
        is_last_item = sf.eq(Count[k], sf.sum_b(Tour[i], [True]))
        solver += Implies(Not(s_is_assigned), sf.all_F(DepCost[i, k])) # if courier k doesn't deliver i, then DepCost[i] = 0
        solver += Implies(And(s_is_assigned, is_last_item), sf.eq(DepCost[i, k], cost(i, n+1)))
        for j in myRange(n):
            if i != j:
                d_is_assigned = sf.eq(X[j], kb)
                travels_arc = And(And(s_is_assigned, d_is_assigned), sf.eq(sf.sum_b(Tour[i], [True]), Tour[j]))
                solver += Implies(travels_arc, sf.eq(DepCost[i, k], cost(i, j)))
                
for k in myRange(m):
    solver.add(sf.eq(C[k], sf.sum_b_list([DepCost[i, k] for i in myRange(n)]+[StartCost[k]])))

solver.add(sf.max_elem([C[k] for k in myRange(m)], MaxCost))
solver.add(sf.gte(MaxCost, sf.int2boolList(LB)))

# solving
solver.check()
model = solver.model()

# visualization
def print_costs():
    print(np.array(
        [[D[i][j] for j in range(n+1)] for i in range(n+1)]
    ))
    print()

def print_sizes():
    print("sizes:")
    print(np.array(
        [s[i] for i in range(n)]
    ))
    print()

def print_maxloads():
    print("maxloads:") 
    print(np.array(
        [l[i] for i in range(m)]
    ))
    print()

def print_input():
    print_costs()
    print_sizes()
    print_maxloads()

def print_accs(k):
    sc = [model[StartCost[k][i]] for i in range(len(StartCost[k]))]
    print(f"Start cost acc: {sf.bool2int(sc)}")
    dc = [sf.bool2int([model[DepCost[i, k][q]] for q in range(len(DepCost[i, k]))]) for i in myRange(n)]
    print(f"Departure cost accs: {dc}")

def print_courier(k):
    print(f"-- Courier {k-1} --")
    print(f"Count: {sf.bool2int([model[Count[k][q]] for q in range(len(Count[k]))])}")
    print_accs(k)
    c_b = [model[C[k][i]] for i in range(len(C[k]))]
    print(f"Cost: {sf.bool2int(c_b)}")

def print_solution(model):
    x_vals = [sf.bool2int([model[X[i][q]] for q in range(len(X[i]))]) for i in myRange(n)]
    tour_vals = [sf.bool2int([model[Tour[i][q]] for q in range(len(Tour[i]))]) for i in myRange(n)]
    print(f"Assignemnts: {x_vals}")
    print(f"Tours:       {tour_vals}")
    for k in myRange(m):
        print_courier(k)

print_input()
print_solution(model)