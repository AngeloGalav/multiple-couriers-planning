import os
import time
from minizinc import *
from argparse import ArgumentParser
from datetime import timedelta
from data_handlers import computeBounds, get_values_from_dzn, parseInstance
from data_handlers import saveAsJson
import numpy as np

timeout = timedelta(seconds=300)

strategies = ["input_order", "first_fail", "smallest", "dom_w_deg"]
heuristics = ["indomain_min", "indomain_median", "indomain_random", "indomain_split"]
restarts = ["restart_linear(<scale>)", "restart_geometric(<base>,<scale>)", "restart_luby(<scale>)", "restart_none"]
solvers = ["gecode", "chuffed"]

# --- ARGS ---
parser = ArgumentParser()
parser.add_argument("-s", "--strategy", type=str,
                    choices=strategies, default='input_order')
parser.add_argument("-he", "--heuristic", type=str,
                    choices=["min", "median", "random", "split"], default='min')
parser.add_argument("-r", "--restart", type=str,
                    choices=["linear", "geometric", "luby", "none"], default="linear")
parser.add_argument("-sc", "--scale", type=int, default=100)
parser.add_argument("-b", "--base", type=int, default=2)
parser.add_argument("-i", "--instance", type=int, default=3)
parser.add_argument('-a', '--all', action='store_true')
parser.add_argument("-so", "--solver", type=str,
                    choices=solvers, default='gecode')

args = parser.parse_args()._get_kwargs()

instance_id = args[5][1]
inst_file = './instances/'+"inst"+str(instance_id).zfill(2)+".dat"
run_all_ = args[6][1]

template_path = "CP/model_2_symmb.mzn"
replace_template = """%annotations here
solve :: int_search(tour, <strat>, <indom_heur>) minimize cost :: <restart>;"""

def clean_up_template() :
    # tidying up
    with open(template_path, 'r') as file:
        file_content = file.read()
    index = file_content.find("%annotations here")

    if index != -1:
        newline_index = file_content.find('\n\n', index)
        if newline_index != -1:
            # Replacing the content after target_string until the newline character
            replaced_text = file_content[:index] + '%annotations here' + file_content[newline_index:]

            # Write the updated content back to the file
            with open(template_path, 'w') as file:
                file.write(replaced_text)

def getSolution(solution, original_order):
    tour_vals = np.array(solution.tour, dtype=np.int32)
    seg_vals = np.array(solution.seg, dtype=np.int32)
    sol = []
    for i in range(len(seg_vals)-1):
        sol.append(tour_vals[seg_vals[i]:seg_vals[i+1]-1].tolist())
    
    ordered_sol = []
    for i in original_order:
        ordered_sol.append(sol[i])
    
    return ordered_sol
    
def run_cp_instance(model, solverName, dataFile, heur_info=None) :
    # model = Model(modelFile)
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

    # order the loads so that couriers with equal loads are adjacent (less constraints)
    courier_order = np.array(l).argsort()
    ordered_l = np.array(l)[courier_order].tolist()
    original_order = courier_order.argsort()

    instance["m"] = m
    instance["n"] = n
    instance["l"] = ordered_l
    instance["s"] = s
    instance["D"] = D
    instance["LB"] = LB
    instance["UB"] = UB

    start_time = time.time()
    result = instance.solve(timeout=timeout)
    flat_time = time.time()-start_time

    print("Flat time:", flat_time)

    solv_info = ''
    if heur_info != None :
        ss, rs, hs = heur_info
        solv_info = solverName + '_' + ss + '_' + rs + '_' + hs + '_symmb'
    else :
        solv_info = solverName + '_symmb'

    # save as json with instance name
    if result != None and result.solution != None:
        print(result.solution)
        if flat_time > 295:
            time_search = 300
        else:
            time_search = round((result.statistics['initTime']+result.statistics['solveTime']).total_seconds(), 2)
        saveAsJson(str(instance_id), solv_info, "res/CP/",
                (time_search, result.solution.cost, getSolution(result.solution, original_order)))
    else :
        saveAsJson(str(instance_id), solv_info, "res/CP/",
                (300, 0, "N/A"))


def modify_model_heuristics(modelFile, strategy_choice,
                            heuristic_choice, restart_choice, restart_scale, restart_base):
    # modifying string to replace
    to_replace = replace_template
    to_replace = to_replace.replace("<strat>", strategy_choice)
    to_replace = to_replace.replace("<indom_heur>", heuristic_choice)
    
    to_replace = to_replace.replace("<restart>", restart_choice)
    if 'restart_geometric' in restart_choice :
        to_replace = to_replace.replace("<base>", str(restart_base))
    to_replace = to_replace.replace("<scale>", str(restart_scale))

    # actually reading the file
    with open(modelFile, 'r') as file:
        file_content = file.read()

    index = file_content.find("%annotations here")

    if index != -1:
        newline_index = file_content.find('\n\n', index)
        if newline_index != -1:
            # Replacing the content after target_string until the newline character
            replaced_text = file_content[:index] + to_replace + file_content[newline_index:]

            # Write the updated content back to the file
            with open(modelFile, 'w') as file:
                file.write(replaced_text)

    model = Model(modelFile)
    return model


def run_all() :
    for i in strategies :
        for j in heuristics :
            for k in restarts :
                for s in solvers :
                    # indomain_random is not supported in chuffed
                    if (s == "chuffed" and j == "indomain_random") : break
                    model = modify_model_heuristics(template_path,
                                        i, j, k, 2, 2)
                    rest_name = k.split('(')[0]
                    print("--- Testing " + i + ", " + rest_name + ", " + j + " using solver " + s + " ---")
                    run_cp_instance(model, s, inst_file, (i, j, rest_name))

    print("Tested all configurations on instance " + str(instance_id) + ", tidying up now...")
    clean_up_template()


if run_all_ :
    run_all()
else :
    strategy_choice = args[0][1]

    # get heuristic choice string
    heuristic_choice = ''
    for i in heuristics :
        if args[1][1] in i :
            heuristic_choice = i
            break

    # get restart choice string
    restart_choice = ''
    for i in restarts :
        if args[2][1] in i :
            restart_choice = i
            break

    restart_scale = args[3][1]
    restart_base = args[4][1]
    solver_choice = args[7][1]

    model = modify_model_heuristics(template_path,
                                    strategy_choice, heuristic_choice, restart_choice,
                                    restart_scale, restart_base)
    run_cp_instance(model, solver_choice, inst_file)
    # clean_up_template()