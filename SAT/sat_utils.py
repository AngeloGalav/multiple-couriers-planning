from argparse import ArgumentParser
import sys
sys.path.append('./')
from data_handlers import computeBounds, parseInstance, saveAsJson
import SATfunctions2 as sf

def get_args():
    parser = ArgumentParser()
    parser.add_argument("-t", "--timelimit", type=int, default=300)
    parser.add_argument("-i", "--instance", type=int, default=3)

    args = parser.parse_args()._get_kwargs()

    time_limit = args[0][1]
    instance = args[1][1]

    return time_limit, instance

def get_input(instance: int):
    inst_name = "inst"+str(instance).zfill(2)+".dat"
    m,n,l,s,D = parseInstance('./instances/'+inst_name)
    LB, UB = computeBounds(D, m, n)
    return m, n, l, s, D, LB, UB

def binarize_input(m, n, l, s, D):
    mb = sf.int2boolList(m)
    nb = sf.int2boolList(n)
    lb = [sf.int2boolList(l[i]) for i in range(m)]
    sb = [sf.int2boolList(s[i]) for i in range(n)]
    Db = [[sf.int2boolList(D[i][j]) for j in range(n+1)] for i in range(n+1)]
    return mb, nb, lb, sb, Db

def save_solution(instance, name, solution):
    saveAsJson(str(instance), name, "./res/SAT/", solution)

