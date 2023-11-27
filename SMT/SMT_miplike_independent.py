import uuid
import numpy as np
from itertools import combinations
import sys
sys.path.append('./')
from data_handlers import saveAsJson, computeBounds, parseInstance
from argparse import ArgumentParser
import time
from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import Solver,get_model
from math import ceil
from pysmt.shortcuts import Symbol, And, GE, Plus, Or, Not, Implies, GT, LE, EqualsOrIff, Int
from pysmt.typing import INT


# --- ARGS ---
parser = ArgumentParser()
parser.add_argument("-t", "--timelimit", type=int, default=300)
parser.add_argument("-i", "--instance", type=int, default=3)
parser.add_argument("-v", "--verbose", action='store_true')
parser.add_argument("-s", "--solver", type=str, choices=['z3','msat','cvc4'], default='z3')

args = parser.parse_args()._get_kwargs()

time_limit = args[0][1]
instance = args[1][1]
verbose = args[2][1]
solv_arg = args[3][1]

inst_name = "inst"+str(instance).zfill(2)+".dat"
m,n,l,s,D = parseInstance('./instances/'+inst_name)
LB, UB = computeBounds(D, m, n)

name = "miplike"


#at most 1  (max 1 T)
def at_most_one_T(bools):
    if len(bools) <= 4: # base case
        return And([Not(And(b1, b2)) for b1, b2 in combinations(bools, 2)])
    
    # recursive step
    y = Symbol(f"yamo_{str(uuid.uuid4())}")
    first = bools[:3]
    first.append(y)
    c_first = at_most_one_T(first)

    last = bools[3:]
    last.insert(0, Not(y))
    c_last = at_most_one_T(last)

    return And(c_first, c_last)

# 1 T
def exactly_one_T(bools):                                      
    return And(at_most_one_T(bools), Or(bools))

X = [[[Symbol(f"X_{k}_{i}_{j}") if i != j else None for j in range(n+1)] for i in range(n+1)] for k in range(m)]
Y = [[Symbol(f"Y_{k}_{i}") for i in range(n)]for k in range(m)]
U = [Symbol(f"U_{i}",INT) for i in range(n)]
C = [Symbol(f"C_{k}",INT) for k in range(m)]
MaxCost = Symbol('MaxCost',INT)

def add_constraints(solver):
    # domains
    for i in range(n):
        solver.add_assertion(GT(U[i],Int(0)))
        solver.add_assertion(LE(U[i],Int(n)))
        

    # C1
    for i in range(n):
        solver.add_assertion(Or([X[k][i][j] for j in range(n+1) if i != j for k in range(m)]))
        solver.add_assertion(Or([X[k][j][i] for j in range(n+1) if i != j for k in range(m)]))
        for k in range(m):
            solver.add_assertion(at_most_one_T([X[k][j][i] for j in range(n+1) if i != j]))
            if time_limit - (time.time()-start_time) < 0:
                return

    if verbose:
        print(f"constraint C1 added")

    # C2
    for i in range(n):
        for k in range(m):
            solver.add(Y[k][i] == sf.at_least_one_T([X[k][i][j] for j in range(n+1) if i != j]))
            solver.add(Y[k][i] == sf.at_least_one_T([X[k][j][i] for j in range(n+1) if i != j]))   
            if time_limit - (time.time()-start_time) < 0:
                return     

    # C2.5
    for i in range(n):
        solver.add_assertion(exactly_one_T([Y[k][i] for k in range(m)]))
        if time_limit - (time.time()-start_time) < 0:
                return

    if verbose:
        print(f"constraint C2 added")

    # C3
    for k in range(m):
        solver.add_assertion(Plus([If(Y[k][i], s[i], 0) for i in range(n)]) <= l[k])      #NON SO COME TRADURLO IN PYSMT
        if time_limit - (time.time()-start_time) < 0:
                return

    if verbose:
        print(f"constraint C3 added")

    # C4
    for k in range(m):
        solver.add_assertion(exactly_one_T([X[k][n][j] for j in range(n)]))
        solver.add_assertion(exactly_one_T([X[k][i][n] for i in range(n)]))
        solver.add_assertion(Or([Y[k][i] for i in range(n)]))
        if time_limit - (time.time()-start_time) < 0:
                return

    if verbose:
        print(f"constraint C4 added")

    # C5
    for i in range(n):
        for j in range(n):
            if i != j:
                arc_traversed = Or([X[k][i][j] for k in range(m)])
                solver.add_assertion(Implies(arc_traversed, GT(U[j], U[i])))
                if time_limit - (time.time()-start_time) < 0:
                    return

    if verbose:
        print(f"constraint C5 added")

    for k in range(m):
        solver.add_assertion(EqualsOrIff(C[k], Plus([If(X[k][i][j], D[i][j], 0) for i in range(n+1) for j in range(n+1) if i != j])))     #NEMMENO QUESTO
        solver.add_assertion(GE(MaxCost, C[k]))

    solver.add_assertion(Or([EqualsOrIff(MaxCost, C[k]) for k in range(m)]))
    solver.add_assertion(LE(MaxCost, UB))
    solver.add_assertion(GE(MaxCost, LB))
bestModel = None
start_time = time.time()
solver=Solver(name=solv_arg)
add_constraints(solver)
if verbose:
    print('Start searching...')
# binary search for the minimum cost solution
while high > low:
    if time.time()-start_time>time_limit:
        break
    mid = (high + low)//2
    solver.push()
    solver.add_assertion(LE(MaxCost,Int(mid)))
    #solver.set('timeout',ceil(time.time()-start_time)*1000)
    if solver.solve():
        print(f"Sat for {mid}")
        bestModel = solver.get_model()
        high =int(bestModel.get_value(MaxCost).constant_value())
    else:
        solver.pop()
        print(f"Unsat for {mid}")
        low = mid+1
    #print()
t = time.time() - start_time

def getSolution(best, n, m, t):
    if t >= time_limit - 1:
        t = time_limit
    if best is None:
        obj = 0
        sol = "N/A"
    else:
        obj = int(best.get_value(MaxCost).constant_value())
        sol = []
        for k in range(m):
            path = []
            current = n
            dest = 0
            path = []
            while(dest != n):
                dest = 0
                while(current == dest or best.get_value(X[current, dest, k]).constant_value() == False):
                    dest += 1
                if dest != n:
                    path.append(dest+1)
                    current = dest
            sol.append(path)
    return t, obj, sol
#print(getSolution(bestModel, n, m, t))
saveAsJson(str(instance), solv_arg, "./res/SMT/solver_ind", getSolution(bestModel, n, m, t))