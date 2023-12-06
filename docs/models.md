# Using each model

Each of the model has a set of options (i.e. solver, heuristics, instance to solve...) that can be set up through the arguments of their relative command.


> [!WARNING]
> - In order for the models to properly work, a _folder_ named `instances` __placed on the root of the project folder__. All instances inside of the `instance` folder must have the proper filename (which is `inst[n].dat`)
> - In addition, all the commands specified in this guide __must also be run on the root of the project__ folder, as specified for each in each section of this document.
> - While other options can be set for each script, __we recommend only to use the options/arguments specified in this document__.

## CP
To test the model you can either:
- Use the MiniZinc IDE. Refer to the official MiniZinc documents.
- Use the provided scripts.

There are 2 Python scripts that are associated with the models that exploit Constraint Programming in MiniZinc. These scripts are `cp_model2.py` and `cp_model2_symmb.py`. Each script runs a different model that can be found in the `CP` folder. In particular:
- `cp_model2.py` runs `model_2.mzn`
- `cp_model2_symmb.py` run `model_2_symmb.mzn`

To run a model through the Python scripts type:
```
python3 cp_model2.py [-i INSTANCE] [-so {gecode,chuffed}]
```
Where:
- `-i` allows to select the instance to solve. You must specify an integer value, that is the id of the instance.
- `-so` allows to specify the solver to use. The possible options are {gecode, chuffed}.

## MIP
The MIP model can be run through the `mip_model.py` script inside of the `MIP` folder.
The script must be run from the __root folder__ of the project, specifying the relative path of the script as shown in the example below.

To execute the model, run the command:
```
python3 MIP/mip_model.py [-s {cbc,glpk,scip,highs}] [-i INSTANCE]
```
- `-s` allows to specify the solver for this model. The possible options are {cbc,glpk,scip,highs}.
- `-i` allows to select the instance to use the solver on. You must specify an integer value, that is the id of the instance.

## SAT
We made 2 models using SAT: `SAT_cplike.py` and `SAT_miplike_acc.py`. Each of them uses different techniques to solve the problem, as it's specified in the report.
The scripts must be run from the __root folder__ of the project, specifying the relative path of the script as shown in the example below.
Each of the SAT scripts uses the same arguments.

To execute the model, run the command:
```
python3 SAT/SAT_cplike.py [-i INSTANCE] [-v] [-s {binary,sequential}]
```

- `-s` allows to specify the search strategy for this model. The possible options are {binary,sequential}.
- `-i` allows to select the instance to use the solver on. You must specify an integer value, that is the id of the instance.
- `-v` allows to print a verbose output when running the script.


## SMT
We made 3 models using SMT, which can be found in the following Python script:
- `SMT_cplike.py` and `SMT_miplike.py`, which provide a solver dependent SMT model.
- `SMT_independent.py`, which runs a solver independent SMT model.

As such, there are some differences in options that can be used for each model.

All the scripts must be run from the __root folder__ of the project, specifying the relative path of the script as shown in the example below.


### SMT_cplike.py and SMT_miplike.py

Both of these scripts have the same cli arguments.
To execute the model, run the command:
```
python3 SMT/SMT_cplike.py [-v] [-i INSTANCE]
```
- `-i` allows to select the instance to use the solver on. You must specify an integer value, that is the id of the instance.
- `-v` allows to print a verbose output when running the script.

### SMT_independent.py

To execute the model, run the command:
```
python3 SMT/SMT_independent.py [-i INSTANCE] [-v] [-s {z3,msat,cvc4}]
```
- `-i` allows to select the instance to use the solver on. You must specify an integer value, that is the id of the instance.
- `-v` allows to print a verbose output when running the script.
- `-s` allows to specify the solver to use. The possible options are {z3,msat,cvc4}.