from math import ceil, floor, log2
import z3
from z3 import Bool, Implies, Not, And
import SATfunctions2 as sf
import numpy as np
import time
from sat_utils import *
from itertools import combinations
sys.path.append('./')
from utils import print_input
from pebble import concurrent
from concurrent.futures import TimeoutError

time_limit, instance, verbose, strategy = get_args()
m,n,l,s,D,LB,UB = get_input(instance)
mb, nb, lb, sb, Db = binarize_input(m, n, l, s, D)

name = "cplike_" + strategy

"""
x[1..k][1..n] bool - x[k][i] is true if courier k delivers item i. 
tour[1..n] - If courier k has to deliver item i, tour[i] is the step of the path at which courier k deliver item i (domain 0..n-m)
count[1..m] - count[k] contains the number of items assigned to courier k

Note: simplify domain definition, we consider the indexes as starting from 0 in the implementation of constraints, so x[i] = k-1 means that
item i is assigned to courier k, and tour[i]=s-1 means an item is assigned at step s

C1 - The total weight of items transported by a courier must be lower or equal than the courier's 
maximum laod. We use vaiable x to define this constraint.
    - each courierdelivers atleast one item
    - each item is delivered by exactly one courier

C2 - items delivered by the same courier must be delivered at different steps, so if x[i]==x[j], then
tour[i] != tour[j] must hold.

C3 - if courier i must deliver k items [k1..kp], the relative values of tour tour[k1..kp] must be
constrained between 1 and k (0 and k-1 in the encodings)
"""

@concurrent.process(timeout=time_limit+20)
def run():

    solver = z3.Solver()

    # variable declaration
    Tour = [[Bool(f"Tour_{i}[{q}]") for q in range(floor(log2(n-m))+1)] for i in range(n)]
    Count = [[Bool(f"Count_{k}[{q}]") for q in range(floor(log2(n-m+1))+1)] for k in range(m)]
    XMat = [[Bool(f"XMat_{k},{i}")for i in range(n)] for k in range(m)]

    StartCost = [[Bool(f"StartCost_{k}[{q}]") for q in range(max([len(Db[n][j]) for j in range(n)]))] for k in range(m)]
    DepCost = [[[Bool(f"DepCost_{k},{i}[{q}]") for q in range(max([len(Db[i][j]) for j in range(n+1)]))] for i in range(n)] for k in range(m)]
    C = [[Bool(f"C_{k}[{q}]") for q in range(floor(log2(UB))+1)] for k in range(m)]
    MaxCost = [Bool(f"MaxCost[{q}]") for q in range(floor(log2(UB))+1)]

    # constraint declarations

    def add_constraints(solver):
        # C1
        for k in range(m):
            load = sf.masked_sum_n(sb, XMat[k])
            solver += sf.lte(load, lb[k])
            if time_limit - (time.time()-start_time) < 0:
                return

        for k in range(m):
            solver += sf.at_least_one(XMat[k])
            if time_limit - (time.time()-start_time) < 0:
                return

        for i in range(n):
            solver += sf.exactly_one([XMat[k][i] for k in range(m)])
            if time_limit - (time.time()-start_time) < 0:
                return

        if verbose:
            print(f"constraint C1 added")

        # C2
        for i, j in combinations(range(n), r=2):
            solver += Implies(sf.eq([XMat[k][i] for k in range(m)], [XMat[k][j] for k in range(m)]), sf.ne(Tour[i], Tour[j]))
            if time_limit - (time.time()-start_time) < 0:
                return

        if verbose:
            print(f"constraint C2 added")

        # C3
        for i in range(n):
            for k in range(m):
                kb = sf.int2boolList(k)
                solver += Implies(XMat[k][i], sf.lt(Tour[i], Count[k]))
                if time_limit - (time.time()-start_time) < 0:
                    return

        if verbose:
            print(f"constraint C3 added")

        # count constraints
        for k in range(m):
            solver += sf.eq(Count[k], sf.sum_b_list([XMat[k][i] for i in range(n)]))
            if time_limit - (time.time()-start_time) < 0:
                return

        if verbose:
            print(f"constraint C4 added")

        # Cost constraints
        for k in range(m):
            kb = sf.int2boolList(k)
            for j in range(n):
                solver += Implies(And(sf.all_F(Tour[j]), XMat[k][j]), sf.eq(StartCost[k], D[n][j]))
                if time_limit - (time.time()-start_time) < 0:
                    return

        for k in range(m):
            for i in range(n):
                is_last_item = sf.eq(Count[k], sf.sum_b(Tour[i], [True]))
                solver += Implies(Not(XMat[k][i]), sf.all_F(DepCost[k][i])) # if courier k doesn't deliver i, then DepCost[i] = 0
                solver += Implies(And(XMat[k][i], is_last_item), sf.eq(DepCost[k][i], D[i][n]))
                for j in range(n):
                    if i != j:
                        travels_arc = And(And(XMat[k][i], XMat[k][j]), sf.eq(sf.sum_b(Tour[i], [True]), Tour[j]))
                        solver += Implies(travels_arc, sf.eq(DepCost[k][i], D[i][j]))
                        if time_limit - (time.time()-start_time) < 0:
                            return
                        
        for k in range(m):
            solver.add(sf.eq(C[k], sf.sum_b_list([DepCost[k][i] for i in range(n)]+[StartCost[k]])))
            if time_limit - (time.time()-start_time) < 0:
                return 

        solver.add(sf.max_elem([C[k] for k in range(m)], MaxCost))
        solver.add(sf.gte(MaxCost, sf.int2boolList(LB)))

    start_time = time.time()
    add_constraints(solver)

    if verbose:
        print(f"Time spent for constraints: {time.time() - start_time}")

    const_time = time.time() - start_time
    remaining_time = max(0, time_limit - floor(time.time() - start_time))

    # visualization
    def print_accs(k):
        sc = [model[StartCost[k][i]] for i in range(len(StartCost[k]))]
        print(f"Start cost acc: {sf.bool2int(sc)}")
        dc = [sf.bool2int([model[DepCost[k][i][q]] for q in range(len(DepCost[k][i]))]) for i in range(n)]
        print(f"Departure cost accs: {dc}")

    def print_courier(k):
        print(f"-- Courier {k} --")
        print(f"Count: {sf.bool2int([model[Count[k][q]] for q in range(len(Count[k]))])}")
        print_accs(k)
        c_b = [model[C[k][q]] for q in range(len(C[k]))]
        print(f"Cost: {sf.bool2int(c_b)}")
        print(f"Assignments mat row {[1 if model[XMat[k][i]] else 0 for i in range(len(XMat[k]))]}")

    def print_solution(model):
        tour_vals = [sf.bool2int([model[Tour[i][q]] for q in range(len(Tour[i]))]) for i in range(n)]
        print(f"Tours:       {tour_vals}")
        for k in range(m):
            print_courier(k)

    # solving
    if remaining_time > 0:
        if strategy == 'binary':
            model, search_time = binary_search(UB, LB, MaxCost, solver, remaining_time, verbose)
        elif strategy == 'sequential':
            model, search_time = seqential_search(UB, LB, MaxCost, solver, remaining_time, verbose)
        else:
            raise Exception("Invalid strategy argument")
    else:
        model = None
        const_time = time_limit
        search_time = 0

    def getSolution():
        if model is None:
            obj = 0
            sol = "N/A"
        else:
            obj = sf.bool2int([model[MaxCost[q]] for q in range(len(MaxCost))])
            xmat_vals = np.array([[1 if model[XMat[k][i]] else 0 for i in range(n)] for k in range(m)])
            tour_vals = np.array([sf.bool2int([model[Tour[i][q]] for q in range(len(Tour[i]))]) for i in range(n)])
            count_vals = [sf.bool2int([model[Count[k][q]] for q in range(len(Count[k]))]) for k in range(m)]
            sol = []
            for k in range(m):
                tour_k = tour_vals.copy()
                tour_k[xmat_vals[k, :] == 0] = n+1
                tour_k = tour_k.argsort() + 1
                sol.append(tour_k[:count_vals[k]].tolist())
        return round(const_time+search_time, 2), obj, sol

    save_solution(instance, name, getSolution())

    if verbose and model is not None:
        print_input(D, s, l)
        print_solution(model)

if __name__ == '__main__':
    future = run()

    try:
        future.result()
    except TimeoutError:
        print('Process terminated forcefully: time limit reached')
        save_solution(instance, name, (time_limit, 0, "N/A"))
