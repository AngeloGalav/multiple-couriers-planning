import os
import time
from minizinc import *
from argparse import ArgumentParser
from datetime import timedelta
from data_handlers import computeBounds, get_values_from_dzn, parseInstance
from data_handlers import saveAsJson

timeout = timedelta(seconds=300)

strategies = ["input_order", "first_fail", "smallest", "dom_w_deg"]
heuristics = ["indomain_min", "indomain_median", "indomain_random", "indomain_split"]
restarts = ["restart_linear(<scale>)", "restart_geometric(<base>,<scale>)", "restart_luby(<scale>)"]

# --- ARGS ---
parser = ArgumentParser()
parser.add_argument("-s", "--strategy", type=str,
                    choices=["input_order", "first_fail", "smallest", "dom_w_deg"], default='input_order')
parser.add_argument("-he", "--heuristic", type=str,
                    choices=["min", "median", "random", "split"], default='min')
parser.add_argument("-r", "--restart", type=str,
                    choices=["linear", "geometric", "luby"], default=None)
parser.add_argument("-sc", "--scale", type=int, default=1)
parser.add_argument("-b", "--base", type=int, default=1)
parser.add_argument("-i", "--instance", type=int, default=3)
parser.add_argument('-a', '--all', action='store_true')

args = parser.parse_args()._get_kwargs()

instance_id = args[5][1]
inst_file = './instances/'+"inst"+str(instance_id).zfill(2)+".dat"
run_all = args[6][1]

replace_template = """%annotations here
solve
:: seq_search([
            int_search(x, <strat1>, <indom_heur1>),
            int_search(tour, <strat2>, <indom_heur2>)])
:: <restart>
minimize cost;"""

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

    solv_info = ''
    if heur_info != None :
        ss, rs, hs = heur_info
        solv_info = solverName + '_' + ss + '_' + rs + '_' + hs
    else :
        solv_info = solverName

    # save as json with instance name
    if result.solution != None :
        saveAsJson(str(instance_id), solv_info, "res/CP/",
                (total_time, result.solution.objective, result.solution.x))
    else :
        saveAsJson(str(instance_id), solv_info, "res/CP/",
                (total_time, "N/A", "N/A"))


def modify_model_heuristics(modelFile, strategy_choice,
                            heuristic_choice, restart_choice, restart_scale, restart_base):
    # modifying string to replace
    to_replace = replace_template
    to_replace = to_replace.replace("<strat1>", strategy_choice)
    to_replace = to_replace.replace("<strat2>", strategy_choice)
    to_replace = to_replace.replace("<indom_heur1>", heuristic_choice)
    to_replace = to_replace.replace("<indom_heur2>", heuristic_choice)
    if restart_choice == None :
        to_replace = to_replace.replace("<restart>", "")
    else :
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
    template_path = "CP/model_3.2_template.mzn"
    for i in strategies :
        for j in heuristics :
            for k in restarts :
                model = modify_model_heuristics(template_path,
                                    i, j, k, 2, 2)
                rest_name = k.split('(')[0]
                print("--- Testing " + i + ", " + rest_name + ", " + j + " ---")
                run_cp_instance(model, "gecode", inst_file, (i, j, rest_name))

    print("Tested all configurations on instance " + str(instance_id) + ", tidying up now...")
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

if run_all :
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

    model = modify_model_heuristics("CP/model_3.2_template.mzn",
                                    strategy_choice, heuristic_choice, restart_choice,
                                    restart_scale, restart_base)
    run_cp_instance(model, "gecode", inst_file)
