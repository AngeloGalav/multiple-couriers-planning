from pulp import *
import numpy as np
import os.path
import sys
sys.path.append('../')
from dzn_handlers import saveAsJson
from enum import Enum

"""
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
LB = 4
UB = 36

"""

m = 10
n = 13
l = [185, 190, 200, 180, 200, 190, 200, 180, 195, 190]
s = [22, 17, 10, 8, 14, 12, 17, 19, 25, 25, 6, 21, 6]

D =[[0,  21, 86,  14,  84,  72,  24, 54,  83,  70,  8,  91,  42,  57],
    [21, 0,  71,  35,  70,  51,  16, 75,  62,  91,  29, 70,  57,  52],
    [86, 71, 0,   100, 39,  70,  87, 137, 81,  73,  78, 103, 128, 33],
    [14, 35, 100, 0,   98,  86,  38, 49,  97,  56,  22, 105, 29,  71],
    [84, 70, 39,  98,  0,   109, 86, 135, 120, 57,  76, 129, 126, 27],
    [63, 51, 70,  77,  109, 0,   49, 117, 11,  133, 71, 64,  90,  103],
    [24, 16, 87,  38,  86,  49,  0,  78,  60,  94,  32, 67,  41,  60],
    [63, 84, 137, 49,  135, 135, 87, 0,   146, 79,  59, 154, 65,  108],
    [74, 62, 81,  88,  120, 11,  60, 128, 0,   144, 82, 68,  94,  114],
    [70, 91, 73,  56,  57,  142, 94, 79,  153, 0,   63, 161, 72,  40],
    [8,  29, 78,  22,  76,  80,  32, 59,  91,  63,  0,  99,  50,  49],
    [91, 70, 133, 105, 129, 64,  67, 145, 68,  161, 99, 0,   91,  122],
    [42, 57, 128, 29,  126, 90,  41, 65,  94,  72,  50, 91,  0,   99],
    [57, 52, 33,  71,  27,  103, 60, 108, 114, 40,  49, 122, 99,  0]]

LB = 27+27+8
UB = 145+153+161+161

# --- ARGS ---
solv_arg = 'highs' # choices: [cbc, glpk, scip, highs]
time_limit = 300

if solv_arg == 'glpk':
    solver = GLPK_CMD(timeLimit=time_limit)
elif solv_arg == 'cbc':
    solver = PULP_CBC_CMD(timeLimit=time_limit)
elif solv_arg == 'scip':
    solver = SCIP_CMD(timeLimit=time_limit, keepFiles=True)
elif solv_arg == 'highs':
    solver = HiGHS_CMD(timeLimit=time_limit)
else:
    raise Exception("invalid solver argument")

def cost(i, j):
    return D[i-1][j-1]

def size(i):
    return s[i-1]

def maxload(k):
    return l[k-1]

def myRange(r):
    return range(1, r+1)

prob = LpProblem("Multiple_Couriers_Planning", LpMinimize)


# decision variable declarations

X={}
Y={}
U={}
C={}
B={}
MaxCost = LpVariable("MaxCost", LB, UB, LpInteger)

for i in myRange(n+1):
    for j in myRange(n+1):
        for k in myRange(m):
            if i!=j:
                X[i, j, k] = LpVariable(f"X_{i},{j},{k}", cat=LpBinary)

for i in myRange(n):
    for k in myRange(m):
        Y[i, k] = LpVariable(f"Y_{i},{k}", cat=LpBinary)

for i in myRange(n):
    U[i] = LpVariable(f"U_{i}", lowBound=1, upBound=n, cat=LpInteger)

for k in myRange(m):
    C[k] = LpVariable(f"C_{k}", lowBound=0, upBound=UB, cat=LpInteger)

for k in myRange(m):
    B[k] = LpVariable(f"B_{k}", cat=LpBinary)

# constraints declaration

# C1
for i in myRange(n):
    prob += lpSum([lpSum([X[i, j, k] for j in myRange(n+1) if j != i]) for k in myRange(m)]) == 1

for j in myRange(n):
    prob += lpSum([lpSum([X[i, j, k] for i in myRange(n+1) if i != j]) for k in myRange(m)]) == 1

# C2
for i in myRange(n):
    for k in myRange(m):
        prob += lpSum([X[i, j, k] for j in myRange(n+1) if i != j]) == Y[i, k]

for j in myRange(n):
    for k in myRange(m):
        prob += lpSum([X[i, j, k] for i in myRange(n+1) if i != j]) == Y[j, k]

# C3
for k in myRange(m):
    prob += lpSum([size(i)*Y[i, k] for i in myRange(n)]) <= maxload(k)

# C4
for k in myRange(m):
    prob += lpSum([X[n+1, j, k] for j in myRange(n)]) == 1
    prob += lpSum([X[i, n+1, k] for i in myRange(n)]) == 1

    prob += lpSum([Y[i, k] for i in myRange(n)]) >= 1

# C5
for k in myRange(m):
    for i in myRange(n):
        for j in myRange(n):
            if i != j:
                prob += U[i] - U[j] + (n+1)*X[i, j, k] <= n

# cost constraints
for k in myRange(m):
    prob += C[k] == lpSum(
        [lpSum([X[i, j, k]*cost(i, j) for j in myRange(n+1) if i != j]) for i in myRange(n+1)])

# linearized max constraints
prob += lpSum([B[k] for k in myRange(m)]) == 1

for k in myRange(m):
    prob += MaxCost >= C[k]
    prob += MaxCost <= C[k] + UB - UB*(B[k])

# objective
prob += MaxCost

# ---- solve and visualization ----
status = prob.solve(solver)

def printTour(X, k):
    print(np.array(
        [[int(X[i, j, k].value()) if j != i else 0 for j in myRange(n+1)] for i in myRange(n+1)]
    ))

def printAssignments(Y, k):
    print(np.array(
        [int(Y[i, k].value()) for i in myRange(n)]
    ))

print(prob.variablesDict()['MaxCost'].value())

print('SOLUTION:')
for k in myRange(m):
    print(f"-- courier {k} --")
    printTour(X, k)
    printAssignments(Y, k)
    print(f"Cost = {int(C[k].varValue)}")
    print()

print('\n')
print(f'OBJECTIVE VALUE: {prob.objective.value()}')


def getSolution(prob, X, n, m):
    time = round(prob.solutionTime, 2)
    if time >= time_limit-1:
        time = time_limit
        optimal = False
    else:
        optimal = True
    obj = prob.objective.value()
    sol = []
    # create sol from grids
    for k in myRange(m):
        path = []
        if sum([X[n+1, i, k].value() for i in myRange(n)]) > 0: # check weather the currier has packages
            current = n+1
            dest = 0
            path = []
            while(dest != n+1):
                dest = 1
                while(current == dest or X[current, dest, k].value() != 1):
                    dest += 1
                if dest != n+1:
                    path.append(dest)
                    current = dest
        sol.append(path)
    return time, obj, sol

saveAsJson("3", solv_arg, "../res/MIP/", getSolution(prob, X, n, m))
