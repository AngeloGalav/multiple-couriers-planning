# What is res for?

The `res` folder should be used for publishing the solutions.
The solutions are json files, and they are they structured in this way:
```
filename : [instance_name]_solution.json
content :
{
    "technique1_modelname":
        {
        "time": 300,
        "optimal": false,
        "obj": 12,
        "sol" : [[3, 6, 5], [4, 2], [7, 1]]
        },
    "technique2_modelname":
        {
        "time": 120,
        "optimal": true,
        "obj": 12,
        "sol" : [[3, 6, 5], [4, 2], [7, 1]]
        }
}
```
The `res` contents are generated by the `gen_models_solutions.py` script.