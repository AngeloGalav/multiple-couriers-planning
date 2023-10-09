import sys
import re
import math

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

def build_dzn(f) :
    '''
    Parses a file given as input and returns the contents as python variables.
    '''
    # if len(sys.argv) > 1:
    #     filename = sys.argv[1]
    # else:
    #     print("no file given")
    #     return 0
    # f = open(filename, "r")

    m = int(f.readline())
    n = int(f.readline())
    l = list(map(int, f.readline().split()))
    s = list(map(int, f.readline().split()))
    D = []
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

def compute_bounds(D, m, n) :
    # computing the LB with Davide's method
    Q = math.ceil(n/m)
    d = [[D[i][j] for j in range(n+1) if i != j] for i in range(n+1)]
    cols = [[D[j][i] for j in range(n+1) if i != j] for i in range(n+1)]

    mL = min(d[-1]) # last row
    mR = min([k[-1] for k in d]) # last column

    mins = [min(cols[i]) for i in range(n)]
    mins.sort()

    lower_b = sum(mins[:Q]) + mL + mR
    upper_b = sum([max(cols[i]) for i in range(n)]) # max for each row
    return lower_b, upper_b

# Quick usage example
m, n, _, _, D = get_values_from_dzn(input_text)
print(compute_bounds(D, m, n))