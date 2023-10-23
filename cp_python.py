from minizinc import *
from os import path
from dzn_handlers import compute_bounds, get_values_from_dzn
from dzn_handlers import saveAsJson
import time

def run_cp_instance(modelFile, solverName, dataFile) :
    model = Model(modelFile)
    solver = Solver.lookup(solverName)
    model.add_file(dataFile, parse_data=True)
    instance = Instance(solver=solver, model=model)

    with open("instances/instance1.dzn") as f:
        input_data = f.read()
    print(input_data)

    m, n, _, _, D = get_values_from_dzn(input_data)
    LB, UB = compute_bounds(D, m, n)

    instance["LB"] = LB
    instance["UB"] = UB
    start = time.time()
    result = instance.solve()
    end = time.time()

    total_time = end-start

    print(result.solution.x, result.solution.objective)
    print("Time:", total_time)

    # save as json with instance name
    saveAsJson(path.basename(dataFile).split('.')[0], solverName, "res/CP/",
               (total_time, result.solution.objective, result.solution.x))

# demo
run_cp_instance("CP/model_3.1.mzn", "gecode", "instances/instance1.dzn")