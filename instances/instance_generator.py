import random

def generate_mcp_instance(n, m, max_distance, max_capacity, max_size):
    D = [[random.randint(1, max_distance) for _ in range(n)] for _ in range(n)]

    for i in range(n) :
        D[i][i] = 0
    
    loads = [random.randint(1, max_capacity) for _ in range(m)]
    sizes = [random.randint(1, max_size) for _ in range(n)]
    
    return D, loads, sizes

n = 8
m = 6
max_distance = 9
max_capacity = 5
max_size = 3
D, loads, sizes = generate_mcp_instance(n, m, max_distance, max_capacity, max_size)
f = open("generated_unformatted_instance.txt", "w")
f.write(str(m) + '\n')
f.write(str(n) + '\n')
f.write((" ".join(str(x) for x in loads)) + '\n')
f.write((" ".join(str(x) for x in sizes)) + '\n')
f.write(("\n".join(" ".join(str(x) for x in row) for row in D)))