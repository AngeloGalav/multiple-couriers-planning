from pulp import *
import numpy as np

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
UB = 51

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
    prob += lpSum([X[n+1, j, k] for j in myRange(n)]) <= 1
    prob += lpSum([X[i, n+1, k] for i in myRange(n)]) <= 1

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

prob.solve()

def printTour(X, k):
    print(np.array(
        [[int(X[i, j, k].varValue) if j != i else 0 for j in myRange(n+1)] for i in myRange(n+1)]
    ))

def printAssignments(Y, k):
    print(np.array(
        [int(Y[i, k].varValue) for i in myRange(n)]
    ))

print('SOLUTION:')
for k in myRange(m):
    print(f"-- courier {k} --")
    printTour(X, k)
    printAssignments(Y, k)
    print(f"Cost = {int(C[k].varValue)}")
    print()

print('\n')
print(f'OBJECTIVE VALUE: {prob.objective.value()}')