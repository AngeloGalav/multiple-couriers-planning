from minizinc import *
from dzn_handlers import compute_bounds, get_values_from_dzn
import time

def run_cp_instance(model_file, solver_name, data_file) :
    model = Model(model_file)
    solver = Solver.lookup(solver_name)
    model.add_file(data_file, parse_data=True)
    instance = Instance(solver=solver, model=model)

    with open("instances/input.dzn") as f:
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

    print(result)
    print("Time:", total_time)

# demo
run_cp_instance("CP/model_3.1.mzn", "gecode", "instances/instance1.dzn")