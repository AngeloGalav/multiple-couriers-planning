import uuid
import numpy as np
from itertools import combinations
import sys
sys.path.append('./')
from data_handlers import saveAsJson, computeBounds, parseInstance
from argparse import ArgumentParser
import time
from pysmt.shortcuts import Solver,get_model
from math import ceil
from pysmt.shortcuts import Symbol, And, GE, Plus, Or, Not, Implies, GT, LE, EqualsOrIff, Int, Ite
from pysmt.typing import INT


# --- ARGS ---
parser = ArgumentParser()
parser.add_argument("-t", "--timelimit", type=int, default=300)
parser.add_argument("-i", "--instance", type=int, default=1)
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
                while(current == dest or best.get_value(X[k][current][ dest]).constant_value() == False):
                    dest += 1
                if dest != n:
                    path.append(dest+1)
                    current = dest
            sol.append(path)
    return t, obj, sol

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

start_time = time.time()
solver=Solver(name=solv_arg)

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
            solver.add_assertion(EqualsOrIff(Y[k][i], Or([X[k][i][j] for j in range(n+1) if i != j])))
            solver.add_assertion(EqualsOrIff(Y[k][i], Or([X[k][j][i] for j in range(n+1) if i != j])))  
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
        solver.add_assertion(Plus([Ite(Y[k][i], Int(s[i]), Int(0)) for i in range(n)]) <= Int(l[k]))
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
        solver.add_assertion(EqualsOrIff(C[k], Plus([Ite(X[k][i][j], Int(D[i][j]), Int(0)) for i in range(n+1) for j in range(n+1) if i != j])))
        solver.add_assertion(GE(MaxCost, C[k]))

    solver.add_assertion(Or([EqualsOrIff(MaxCost, C[k]) for k in range(m)]))
    solver.add_assertion(LE(MaxCost, Int(UB)))
    solver.add_assertion(GE(MaxCost, Int(LB)))
bestModel = None

add_constraints(solver)
if verbose:
    print('Start searching...')
# binary search for the minimum cost solution
while UB > LB:
    if time.time()-start_time>time_limit:
        break
    mid = (UB + LB)//2
    solver.push()
    solver.add_assertion(LE(MaxCost,Int(mid)))
    if solver.solve():
        if time.time()-start_time<=time_limit:
            print(f"Sat for {mid}")
            bestModel = solver.get_model()
            UB =int(bestModel.get_value(MaxCost).constant_value())
            #print(getSolution(bestModel, n, m, time_limit))
    else:
        solver.pop()
        print(f"Unsat for {mid}")
        LB = mid+1
    #print()
t = time.time() - start_time

saveAsJson(str(instance), solv_arg, "./res/SMT/", getSolution(bestModel, n, m, t))