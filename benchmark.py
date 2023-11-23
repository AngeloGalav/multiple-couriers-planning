'''
Executes all models and available
'''

import os
import subprocess
from argparse import ArgumentParser

parser = ArgumentParser()
parser.add_argument("-i", "--instance", type=int, default=3)
parser.add_argument('-a', '--all', action='store_true')
parser.add_argument("-f", "--file", type=str, default=None)
parser.add_argument("-mf", "--model-family", type=str, choices=["SAT", "CP", "SMT", "MIP"], default=None)

args = parser.parse_args()._get_kwargs()
instance_id = args[0][1]
run_all = args[1][1]
inst_file = './instances/'+"inst"+str(instance_id).zfill(2)+".dat"
file = args[2][1]
model_family = args[3][1]

# definitions
models = {"SAT" : ["SAT/SAT_cplike.py", "SAT/SAT_miplike_acc.py"],
          "MIP" : ["MIP/mip_model.py"],
          "SMT" : ["SMT/SMT1.py", "SMT/SMT2.py"],
          "CP"  : ["cp_python.py"]}

opts = {"SAT" : ["-s binary", "-s sequential"],
        "MIP" : ["-s glpk", "-s cbc", "-s scip", "-s highs"],
        "SMT" : [""],
        "CP"  : ["-a"]}

# Replace 'your_folder_path' with the actual path to your folder containing Python files
def execute_all_files() :
    folders = ["MIP", "CP", "SAT", "SMT"]
    files = []
    for fol in folders :
        filesToAdd = (os.listdir(fol))
        x = []
        for i in filesToAdd :
            x.append(str(os.path.join(fol, i)))
        files.extend(x)

    files.remove('MIP/fixed_apis.py') # exclude this library, need to find a better workaround for this (libs folder?)

    python_files = [file for file in files if file.endswith('.py')]
    python_files.append('cp_python.py')

    instances = [file for file in os.listdir("instances") if file.endswith(".dat")]

    # execute files
    for python_file in python_files:
        for inst in instances:
            try:
                print("\n\n --- Running ", python_file, " on instance ", inst, "---\n")
                subprocess.run(['python', python_file])
            except Exception as e:
                print(f"An error occurred while executing {python_file}: {e}")

def run_models(instance) :
    if model_family == None :
        print("sry but as of now executing all files is disabled!")
        # execute_all_files()
        # todo: remove execute all files and instead do a more ordered version of that program
    else:
        for m in models[model_family] :
            for op in opts[model_family] :
                try:
                    print("\n\n --- Running ", m,
                          " on instance ", instance, " with args ", op, " ---\n")
                    # print(['python', m, "-i", instance, op])
                    cmd = ['python', m, "-i", str(instance)]
                    cmd.extend(op.split(' '))
                    subprocess.run(cmd)
                except Exception as e:
                    print(f"An error occurred while executing {m}: {e}")

def run_on_all_instances() :
    for i in range(1, 22) :
        run_models(i)

if run_all :
    run_on_all_instances()
else :
    run_models(instance_id)