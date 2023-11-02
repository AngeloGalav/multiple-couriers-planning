'''
Executes all models and available
'''

import os
import subprocess

# Replace 'your_folder_path' with the actual path to your folder containing Python files
folders = ["MIP", "CP", "SAT", "SMT"]
files = []
for fol in folders :
    filesToAdd = (os.listdir(fol))
    x = []
    for i in filesToAdd :
        x.append(str(os.path.join(fol, i)))
    files.extend(x)

files.remove('MIP/fixed_apis.py') # exclude this library, need to find a better workaround for this (libs folder?)
# Filter for Python files (assuming they have the '.py' extension)
python_files = [file for file in files if file.endswith('.py')]

# Loop through the Python files and execute them
for python_file in python_files:
    try:
        print("\n\n --- Running ", python_file, " ---\n")
        subprocess.run(['python', python_file])
    except Exception as e:
        print(f"An error occurred while executing {python_file}: {e}")

print("Execution of Python files completed.")
