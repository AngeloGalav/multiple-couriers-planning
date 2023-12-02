# Using each model

Each of the model has a set of options (i.e. solver, heuristics, instance to solve...) that can be set up through the arguments of their relative command.

## CP
To test the model you can either:
- Use the MiniZinc IDE. Refer to the official MiniZinc documents.
- Use the provided scripts.

There are 3 Python scripts that are associated with the models that exploit Constraint Programming in MiniZinc. These scripts are `cp_model2.py`, `cp_model2_symmb.py`, `cp_model3.py`. Each script runs a different model that can be found in the `CP` folder. In particular:
- `cp_model2.py` runs `model_2.mzn`
- `cp_model2_symmb.py` run `model_2_symmb.mzn`
- `cp_model3.py` runs `model_3.2.mzn`

To run a model through the Python scripts type:
```
python3 cp_model3.py [-s {input_order,first_fail,smallest,dom_w_deg}] [-he {min,median,random,split}] [-r {linear,geometric,luby,none}] [-sc SCALE] [-b BASE] [-i INSTANCE] [-a] [-so {gecode,chuffed}]
```
Where:
- `-s` allows to specify the variable choice annotations. The possible options are {input_order,first_fail,smallest,dom_w_deg}.
- `-he` allows to specify the indomain choice heuristic. The possible options are {min,median,random,split}.
- `-r` allows to specify the restart strategy. The possible options are {linear,geometric,luby,none}. When a restart strategy is selected, other parameters can also be tuned:
    - `-sc` allows to select the scale of the restart options, and is an integer value.
    - `-b` allows to select the base when using the `geometric` restart, and is an integer value as well.
- `-i` allows to select the instance to solve. You must specify an integer value, that is the id of the instance.
- `-a` allows to run the model with all the possible option choices on a defined instance.
- `-so` allows to specify the solver to use. The possible options are {gecode, chuffed}.


Use the command `python3 cp_model3.py -h` to see more information about the possible options that can tuned up through this script.

## MIP
The MIP model can be run through the `mip_model.py` script inside of the `MIP` folder.
The script must be run from the __root folder__ of the project.

To execute the model, run the command:
```
python3 MIP/mip_model.py [-s {cbc,glpk,scip,highs}] [-t TIMELIMIT] [-i INSTANCE]
```
- `-s` allows to specify the solver for this model. The possible options are {cbc,glpk,scip,highs}.
- `-t` allows to set the time limit. I suggest to not use this parameter, as the timelimit value is 300 by default.
- `-i` allows to select the instance to use the solver on. You must specify an integer value, that is the id of the instance.

For more information about the arguments of this script, type `python3 MIP/mip_model.py -h`.

## SAT
We made 2 models using SAT: `SAT_cplike.py` and `SAT_miplike_acc.py`. Each of them uses different techniques to solve the problem, as it's specified in the report.
The scripts must be run from the __root folder__ of the project.
Each of the SAT scripts uses the same arguments.

To execute the model, run the command:
```
python3 SAT/SAT_cplike.py [-t TIMELIMIT] [-i INSTANCE] [-v] [-s {binary,sequential}]
```

- `-s` allows to specify the search strategy for this model. The possible options are {binary,sequential}.
- `-t` allows to set the time limit. I suggest to not use this parameter, as the timelimit value is 300 by default.
- `-i` allows to select the instance to use the solver on. You must specify an integer value, that is the id of the instance.
- `-v` allows to print a verbose output when running the script.

For more information about the arguments of this script, type `python3 SAT/SAT_cplike.py -h`.

## SMT
We made 3 models using SMT, which can be found in the following Python script:
- `SMT_cplike.py` and `SMT_miplike.py`, which provide a solver dependent SMT model.
- `SMT_independent.py`, which runs a solver independent SMT model.

As such, there are some differences in options that can be used for each model.

All the scripts must be run from the __root folder__ of the project.

### SMT_cplike.py and SMT_miplike.py

Both of these scripts have the same cli arguments.
To execute the model, run the command:
```
python3 SMT/SMT_cplike.py [-v] [-t TIMELIMIT] [-i INSTANCE]
```
- `-t` allows to set the time limit. I suggest to not use this parameter, as the timelimit value is 300 by default.
- `-i` allows to select the instance to use the solver on. You must specify an integer value, that is the id of the instance.
- `-v` allows to print a verbose output when running the script.

For more information about the arguments of this script, type `python3 SMT/SMT_cplike.py -h`.

### SMT_independent.py

To execute the model, run the command:
```
python3 SMT/SMT_independent.py [-t TIMELIMIT] [-i INSTANCE] [-v] [-s {z3,msat,cvc4}]
```
- `-t` allows to set the time limit. I suggest to not use this parameter, as the timelimit value is 300 by default.
- `-i` allows to select the instance to use the solver on. You must specify an integer value, that is the id of the instance.
- `-v` allows to print a verbose output when running the script.
- `-s` allows to specify the solver to use. The possible options are {z3,msat,cvc4}.

For more information about the arguments of this script, type `python3 SMT/SMT_independent.py -h`.