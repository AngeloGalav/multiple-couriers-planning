import sys, time, z3
import numpy as np
from math import floor
from z3 import Int, Sum, Implies, If, And, Or, Bool, Not
from argparse import ArgumentParser
from itertools import combinations
sys.path.append('./')
from data_handlers import computeBounds, parseInstance, saveAsJson
from utils import print_input
import SAT.SATfunctions2 as sf
from pebble import concurrent
from concurrent.futures import TimeoutError

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

name = "miplike"

@concurrent.process(timeout=time_limit+20)
def run():
    solver = z3.Optimize()

    # -- variables

    X = [[[Bool(f"X_{k},{i},{j}") if i != j else None for j in range(n+1)] for i in range(n+1)] for k in range(m)]
    Y = [[Bool(f"Y_{k},{i}") for i in range(n)]for k in range(m)]
    U = [Int(f"U_{i}") for i in range(n)]

    # StartCost = [Int(f"StartCost_{k}") for k in range(m)]
    DepCost = [[Int(f"DepCost_{k}_{i}") for i in range(n+1)] for k in range(m)]
    C = [Int(f"C_{k}") for k in range(m)]
    MaxCost = Int('MaxCost')

    def add_constraints(solver):
        # domains
        for i in range(n):
            solver += U[i] > 0
            solver += U[i] <= n

        # C1
        for i in range(n):
            solver.add(sf.at_least_one_T([X[k][i][j] for j in range(n+1) if i != j for k in range(m)]))
            solver.add(sf.at_least_one_T([X[k][j][i] for j in range(n+1) if i != j for k in range(m)]))
            for k in range(m):
                solver.add(sf.at_most_one_T([X[k][j][i] for j in range(n+1) if i != j]))
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
            solver.add(sf.exactly_one_T([Y[k][i] for k in range(m)]))
            if time_limit - (time.time()-start_time) < 0:
                    return

        if verbose:
            print(f"constraint C2 added")

        # C3
        for k in range(m):
            solver.add(Sum([If(Y[k][i], s[i], 0) for i in range(n)]) <= l[k])
            if time_limit - (time.time()-start_time) < 0:
                    return

        if verbose:
            print(f"constraint C3 added")

        # C4
        for k in range(m):
            solver.add(sf.exactly_one_T([X[k][n][j] for j in range(n)]))
            solver.add(sf.exactly_one_T([X[k][i][n] for i in range(n)]))
            solver.add(sf.at_least_one_T([Y[k][i] for i in range(n)]))
            if time_limit - (time.time()-start_time) < 0:
                    return

        if verbose:
            print(f"constraint C4 added")

        # C5
        for i in range(n):
            for j in range(n):
                if i != j:
                    arc_traversed = sf.at_least_one_T([X[k][i][j] for k in range(m)])
                    solver.add(Implies(arc_traversed, U[j] > U[i]))
                    if time_limit - (time.time()-start_time) < 0:
                        return

        for k in range(m):
            for j in range(n):
                solver.add(Implies(X[k][n][j], DepCost[k][n] == D[n][j]))
                if time_limit - (time.time()-start_time) < 0:
                    return

        for k in range(m):
            for i in range(n):
                solver.add(Implies(Not(Y[k][i]), DepCost[k][i] == 0))
                for j in range(n+1):
                    if i != j:
                        solver.add(Implies(X[k][i][j], DepCost[k][i] == D[i][j]))
                        if time_limit - (time.time()-start_time) < 0:
                            return

        if verbose:
            print(f"constraint C5 added")

        for k in range(m):
            # solver += C[k] == Sum([If(X[k][i][j], D[i][j], 0) for i in range(n+1) for j in range(n+1) if i != j])
            solver += C[k] == Sum(DepCost[k])
            solver += MaxCost >= C[k]

        solver += Or([MaxCost == C[k] for k in range(m)])
        solver += MaxCost <= UB
        solver += MaxCost >= LB

    start_time = time.time()
    add_constraints(solver)

    const_time = time.time() - start_time
    remaining_time = max(0, time_limit - floor(time.time() - start_time))

    # -- solve

    res = solver.minimize(MaxCost)
    solver.set("timeout", floor(remaining_time)*1000)
    start_time = time.time()
    solver.check()
    search_time = time.time()-start_time
    model = solver.model()

    # -- visualization

    def printTour(model, k):
        print(np.array(
            [[1 if j != i and model[X[k][i][j]] else 0 for j in range(n+1)] for i in range(n+1)]
        ))

    def printAssignments(model, k):
        print(np.array(
            [1 if model[Y[k][i]] else 0 for i in range(n)]
        ))

    def print_solution(model):
        for k in range(m):
            print(f"-- courier {k} --")
            printTour(model, k)
            print()
            printAssignments(model, k)
            print(f"Cost: {model[C[k]]}")
            print()

    if verbose and model is not None:
        print_solution(model)

    # -- save solution
    def getSolution():
        if model is None or len(model) == 0:
            obj = 0
            sol = "N/A"
        else:
            obj = int(str(model[MaxCost]))
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

    saveAsJson(str(instance), name, "./res/SMT/", getSolution())

if __name__ == '__main__':
    future = run()

    try:
        print(f"Process terminated normally: {future.result()}")
    except TimeoutError:
        print('Process terminated forcefully: time limit reached')
        saveAsJson(str(instance), name, "./res/SMT/", (time_limit, 0, "N/A"))