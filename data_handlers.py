import sys
import re
import json
import os
import math

# example text
input_text = """
m = 3;
n = 7;
l = [15, 10, 7];
s = [3, 2, 6, 8, 5, 4, 4];
D =
[|0, 3, 3, 6, 5, 6, 6, 2
 |3, 0, 4, 3, 4, 7, 7, 3
 |3, 4, 0, 7, 6, 3, 5, 3
 |6, 3, 7, 0, 3, 6, 6, 4
 |5, 4, 6, 3, 0, 3, 3, 3
 |6, 7, 3, 6, 3, 0, 2, 4
 |6, 7, 5, 6, 3, 2, 0, 4
 |2, 3, 3, 4, 3, 4, 4, 0 |];
"""

def get_values_from_dzn(text):
    '''
    Parses a file given as input and returns the contents as python variables.
    '''
    integer_pattern = r'(\w+)\s*=\s*(\d+);'
    list_pattern = r'(\w+)\s*=\s*\[([^\]\|]*)\];'
    matrix_pattern = r'(\w+)\s*=\s*\[\|([^\]]*)\|\];'

    integers = dict(re.findall(integer_pattern, text))
    lists = dict(re.findall(list_pattern, text))
    matrices = dict(re.findall(matrix_pattern, text))

    # Convert values to ints
    for key, value in integers.items():
        integers[key] = int(value.strip())

    # Convert list strings to actual lists
    for key, value in lists.items():
        lists[key] = [int(x.strip()) for x in value.split(',')]

    # Convert matrices in actual matrices
    D = [] # the final matrix
    for i in matrices['D'].split('\n'):
        d = [int(x) for x in i.strip(' |').split(', ')]
        D.append(d)

    return integers['m'], integers['n'], lists['l'], lists['s'], D

def build_dzn(m, n, l, s, D) :
    '''
    Parses a file given as input and returns the contents as python variables.
    '''
    # if len(sys.argv) > 1:
    #     filename = sys.argv[1]
    # else:
    #     print("no file given")
    #     return 0
    # f = open(filename, "r")
    for i in range(n+1):
        row = list(map(int, f.readline().split()))
        D.append(row)

    output = "m = " + str(m) + "\n"
    output += ("n = " + str(n) + "\n")
    output += ("l = " + str(l) + "\n")
    output += ("s = " + str(s) + "\n")
    output += ("D = " + "\n")
    output += ("[|" + "\n |".join(", ".join(str(x) for x in row) for row in D) + " |];")

    filename = filename.split('.')[0]

    f = open(filename + ".dzn", "w")
    f.write(output)

def parseInstance(filename):
    f = open(filename, "r")
    m = int(f.readline())
    n = int(f.readline())
    l = list(map(int, f.readline().split()))
    s = list(map(int, f.readline().split()))
    D = []

    for i in range(n+1):
        row = list(map(int, f.readline().split()))
        D.append(row)

    return m,n,l,s,D

def lower_bound(D, m, n):
    Q = math.ceil(n/m)
    mL = min([D[n][i] for i in range(n)]) # last row
    mR = min([D[i][n] for i in range(n)]) # last column
    mins = [min(D[j][i] for j in range(n) if i!=j) for i in range(n)]
    mins.sort()
    min_arr_lb = sum(mins[:Q-1]) + mL + mR

    simple_path_costs = [D[n][i]+D[i][n] for i in range(n)]
    sim_path_lb = max(simple_path_costs)

    return max(sim_path_lb, min_arr_lb)

def upper_bound(D, m, n):
    Q = n-m+1
    ML = max([D[n][i] for i in range(n)]) # last row
    MR = max([D[i][n] for i in range(n)]) # last column

    maxes = [max(D[j][i] for j in range(n) if i!=j) for i in range(n)]
    maxes.sort(reverse=True)

    return sum(maxes[:Q-1]) + ML + MR

def computeBounds(D, m, n):
    return lower_bound(D, m, n), upper_bound(D, m, n)

def saveAsJson(instanceName, solveName, path, solutionInfo):
    time, obj, sol = solutionInfo
    # optimality check
    if time >= 300:
        time = 300
        optimal = False
    else:
        optimal = True

    filepath = path + instanceName + '.json'
    # putting info on file
    if os.path.isfile(filepath):
        f = open(filepath)
        json_sols = json.load(f)
        f.close()
    else:
        json_sols = {}
    json_sols[solveName] = {
        "time": time,
        "optimal": optimal,
        "obj": obj,
        "sol": sol
    }
    # saving file
    save_file = open(filepath, "w")
    json.dump(json_sols, save_file)
    save_file.close()