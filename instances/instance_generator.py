import random
import scipy.sparse as sp
import numpy as np

def generate_mcp_instance(n, m, max_distance, max_capacity, max_size):
    D = [[random.randint(1, max_distance) for _ in range(n+1)] for _ in range(n+1)]

    for i in range(n) :
        D[i][i] = 0
    
    generated = False

    while not generated : 
        loads = [random.randint(1, max_capacity) for _ in range(m)]
        sizes = [random.randint(1, max_size) for _ in range(n)]
        generated = np.sum(np.array(loads)) >= np.sum(np.array(sizes)) 
    
    return D, loads, sizes


n = 9
m = 6
max_distance = 9
max_capacity = 5
max_size = 3
D, loads, sizes = generate_mcp_instance(n, m, max_distance, max_capacity, max_size)

dist_m = sp.csgraph.floyd_warshall(D, directed=True)
print(D)
print(dist_m)

f = open("generated_unformatted_instance.txt", "w")
f.write(str(m) + '\n')
f.write(str(n) + '\n')
f.write((" ".join(str(x) for x in loads)) + '\n')
f.write((" ".join(str(x) for x in sizes)) + '\n')
f.write(("\n".join(" ".join(str(int(x)) for x in row) for row in dist_m)))