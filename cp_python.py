import os
import time
from minizinc import *
from datetime import timedelta
from data_handlers import computeBounds, get_values_from_dzn, parseInstance
from data_handlers import saveAsJson

timeout = timedelta(seconds=300)

def run_cp_instance(modelFile, solverName, dataFile) :
    model = Model(modelFile)
    solver = Solver.lookup(solverName)
    instance = Instance(solver=solver, model=model)

    if (not dataFile.endswith(".dzn")) :
        m, n, l, s, D = parseInstance(dataFile)
    else :
        with open(dataFile) as f:
            input_data = f.read()
            m, n, l, s, D = get_values_from_dzn(input_data)

    LB, UB = computeBounds(D, m, n)

    # load instance data into the model
    instance["m"] = m
    instance["n"] = n
    instance["l"] = l
    instance["s"] = s
    instance["D"] = D
    instance["LB"] = LB
    instance["UB"] = UB

    start = time.time()
    result = instance.solve(timeout=timeout)
    end = time.time()

    total_time = end-start

    print(result.solution.x, result.solution.objective)
    print("Time:", total_time)

    # save as json with instance name
    saveAsJson(os.path.basename(dataFile).split('.')[0], solverName, "res/CP/",
               (total_time, result.solution.objective, result.solution.x))

def modify_model_heuristics(modelFile, onCopy=True):
    strategies = ["input_order", "first_fail", "smallest", "dom_w_deg"]
    heuristics = ["indomain_min", "indomain_median", "indomain_random", "indomain_split"]
    restart = ["restart_linear(<scale>)", "restart_geometric(<base>,<scale>)", "restart_luby(<scale>)"]

    # solve :: seq_search([
    #          int_search(s, smallest, indomain_min),
    #          int_search([end], input_order, indomain_min)])
    #   minimize end

    # works on the copy of a file, not directly on the model
    if onCopy:
        ...

    # TODO: modify model and create new model file so that the heuristics are there


# demo
run_cp_instance("CP/model_3.1.mzn", "gecode", "./instances/inst02.dat")