'''
# how to use
use this command:

python mcp_input_parser.py [filename]

it will output a MiniZinc readable '.dzn' file
'''
import sys

'''
Function that outputs a MiniZinc readable '.dzn' file
'''
def build_dzn() :
    if len(sys.argv) > 1:
        filename = sys.argv[1]
    else:
        print("no file given")
        return 0

    f = open(filename, "r")
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

'''
Parses a file given as input and returns the contents as python variables.
'''
def parse_instance() :
    if len(sys.argv) > 1:
        filename = sys.argv[1]
    else:
        print("no file given")
        return 0

    f = open(filename, "r")
    m = int(f.readline())
    n = int(f.readline())
    l = list(map(int, f.readline().split()))
    s = list(map(int, f.readline().split()))
    D = []

    for i in range(n+1):
        row = list(map(int, f.readline().split()))
        D.append(row)

    # return m,n,l,s,D
    print(m,n,l,s,D)

build_dzn()