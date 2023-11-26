import numpy as np

def print_costs(D):
    print(np.array(D))
    print()

def print_sizes(s):
    print("sizes:")
    print(np.array(s))
    print()

def print_maxloads(l):
    print("maxloads:") 
    print(np.array(l))
    print()

def print_input(D, s, l):
    print_costs(D)
    print_sizes(s)
    print_maxloads(l)