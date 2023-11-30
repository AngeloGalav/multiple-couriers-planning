'''
Executes all models and available
'''

import os
import subprocess
from argparse import ArgumentParser

parser = ArgumentParser()
parser.add_argument("-i", "--instance", type=int, default=3)
parser.add_argument('-a', '--all', action='store_true')
parser.add_argument("-mf", "--model-family", type=str, choices=["SAT", "CP", "SMT", "MIP"], default=None)

args = parser.parse_args()._get_kwargs()

instance_id = args[0][1]
run_all = args[1][1]
model_family = args[2][1]

# definitions
models = {"SAT" : ["SAT/SAT_cplike.py", "SAT/SAT_miplike_acc.py"],
          "MIP" : ["MIP/mip_model.py"],
          "SMT" : ["SMT/SMT_independent.py"],
          "CP"  : ["cp_model2_symmb.py", "cp_model2.py"]}

opts = {"SAT" : ["-s binary", "-s sequential"],
        "MIP" : ["-s glpk", "-s cbc", "-s scip", "-s highs"],
        "SMT" : ["-s z3","-s msat"],
        "CP"  : ["-a"]}

def run_model(instance, opts, model) :
    try:
        print("\n--- Running ", model,
                " on instance ", instance, " with args ", opts, " ---\n")
        cmd = ['python3', '-W', 'ignore', model, "-i", str(instance)]

        if opts != "" :
            cmd.extend(opts.split(' '))

        print(cmd)
        subprocess.run(cmd)
        print("Done!")
    except Exception as e:
        print(f"An error occurred while executing {model}: {e}")

def run_models(instance) :
    if model_family == None :
        # set it and forget it
        for key in models.keys() :
            for m in models[key] :
                for op in opts[key] :
                    run_model(instance, op, m)
    else:
        for m in models[model_family] :
            for op in opts[model_family] :
                run_model(instance, op, m)

def run_on_all_instances() :
    for i in range(1, 22) :
        run_models(i)

if run_all :
    run_on_all_instances()
else :
    run_models(instance_id)