from argparse import ArgumentParser
from math import ceil
import sys, time, z3
sys.path.append('./')
from data_handlers import computeBounds, parseInstance, saveAsJson
import SATfunctions2 as sf

def get_args():
    parser = ArgumentParser()
    parser.add_argument("-t", "--timelimit", type=int, default=300)
    parser.add_argument("-i", "--instance", type=int, default=3)
    parser.add_argument("-v", "--verbose", action='store_true')

    args = parser.parse_args()._get_kwargs()

    time_limit = args[0][1]
    instance = args[1][1]
    verbose = args[2][1]

    return time_limit, instance, verbose

def get_input(instance: int):
    inst_name = "inst"+str(instance).zfill(2)+".dat"
    m,n,l,s,D = parseInstance('./instances/'+inst_name)
    LB, UB = computeBounds(D, m, n)
    return m, n, l, s, D, LB, UB

def binarize_input(m, n, l, s, D):
    mb = sf.int2boolList(m)
    nb = sf.int2boolList(n)
    lb = [sf.int2boolList(l[i]) for i in range(m)]
    sb = [sf.int2boolList(s[i]) for i in range(n)]
    Db = [[sf.int2boolList(D[i][j]) for j in range(n+1)] for i in range(n+1)]
    return mb, nb, lb, sb, Db

def save_solution(instance, name, solution):
    saveAsJson(str(instance), name, "./res/SAT/", solution)

def binary_search(upper_b, lower_b, ObjVar, solver, time_limit, verbose):
    model = None
    high = upper_b
    low = lower_b
    if verbose:
        print('Start!')
    start_time = time.time()
    while high != low:
        mid = low + (high - low)//2
        if verbose:
            print(f"Trying with objective <= {mid}")
        remaining_time = time_limit - (time.time()-start_time)
        
        solver.set("timeout", ceil(remaining_time)*1000)
        res = solver.check(sf.lte(ObjVar, sf.int2boolList(mid)))
        
        if time_limit < (time.time()-start_time):
            return model, time_limit

        if res == z3.sat:
            model = solver.model()
            res_obj = sf.bool2int([model[ObjVar[q]] for q in range(len(ObjVar))])
            if verbose:
                print(f"Solution found with objective value {res_obj}\n")
            high = res_obj
        else:
            if verbose:
                print("Unsat\n")
            low = mid + 1
    return model, round(time.time()-start_time, 2)

def seqential_search(upper_b, lower_b, ObjVar, solver, time_limit, verbose):
    model = None
    if verbose:
        print('Start!')
    start_time = time.time()
    found_optimal = False
    current = upper_b

    while not found_optimal:
        if verbose:
            print(f"Trying with objective <= {current}")
        remaining_time = time_limit - (time.time()-start_time)
        solver.set("timeout", ceil(remaining_time)*1000)
        res = solver.check(sf.lte(ObjVar, sf.int2boolList(current)))
        if time_limit < (time.time()-start_time):
            return model, time_limit
        if res == z3.sat:
            model = solver.model()
            res_obj = sf.bool2int([model[ObjVar[q]] for q in range(len(ObjVar))])
            if verbose:
                print(f"Solution found with objective value {res_obj}\n")
            if res_obj == lower_b:
                found_optimal = True
            current = res_obj-1
        else:
            if verbose:
                print("Unsat\n")
            found_optimal = True
    return model, round(time.time()-start_time, 2)
            
