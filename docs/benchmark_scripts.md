# How to use the benchmark script?

## What is the benchmark script?
The benchmark script allows to populate the res folder with the adequate files, by running groups of models of different sizes in a single batch.

## Using the benchmark script
To run all models using all instances and all the heuristics/options available, simply use:
```
python benchmark.py -a
```
Otherwise, to run all models of a specific family on all instances using all options available, you can use the command:
```
python benchmark.py -mf [family of models] -a
```
i.e., `python benchmark.py -mf SAT -a`.

Finally, to run a specific family of models using all heuristics on a specific instance using all options available, use the command: 
```
python benchmark.py -mf [family of models] -i [id of the instance]
```
i.e. `python benchmark.py -mf SAT -i 3`

If by chance you want to run benchmarks on multiple instances, so that you don't have to restart the benchmark for each instance each time, simply use:
```
for x in `seq 1 10`; python benchmark.py -mf SAT -i $x ; done; python benchmark.py -mf SAT -i 13
```
N.B.: you need to be using a `bash` compatible shell in order to run in this (in Windows, use MSYS2 or Cygwin)

Happy benchmarking!