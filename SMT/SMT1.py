import z3
from dzn_handlers import saveAsJson, compute_bounds
from mcp_input_parser import actual_parse
from argparse import ArgumentParser


# --- ARGS ---
parser = ArgumentParser()
parser.add_argument("-s", "--solver", type=str, choices=['Z3'], default='Z3')
parser.add_argument("-t", "--timelimit", type=int, default=300)
parser.add_argument("-i", "--instance", type=int, default=3)

args = parser.parse_args()._get_kwargs()

solv_arg = args[0][1]
time_limit = args[1][1]
instance = args[2][1]

inst_name = "inst"+str(instance).zfill(2)+".dat"
m,n,l,s,D = actual_parse('./instances/'+inst_name)
LB, UB = compute_bounds(D, m, n)



# Inizializza il solver Z3
solver = z3.Optimize()

x = [[z3.Int(f"x_{j}_{i}") for i in range(1,1+n)] for j in range(1,1+m)]
tour = [z3.Int(f"tour_{j}") for j in range(1,1+n)]

#Domains
for i in range(n):
    for j in range(m):
        solver.add(z3.Or(x[j][i]==1,x[j][i]==0))
    solver.add(tour[i]>=1)
    solver.add(tour[i] <= z3.Sum([x[j][k]*x[j][i] for k in range(n) for j in range(m)]))

#C1 weight
for i in range(m):
    solver.add(l[i] >= z3.Sum([x[i][j]*s[j] for j in range(n)]))

#C2 different position
for k in range(m):
    for i in range(n):
        for j in range(i + 1, n):
            solver.add(z3.Or(x[k][i]==0,x[k][j]==0, tour[i] != tour[j])) #se entrambi sono 1, allora tour sono diversi

#C3 item delivered only once in x
for j in range(n):
    solver.add(z3.Sum([x[i][j] for i in range(m)])==1)

#C4 no idle courier
for i in range(m):
    solver.add(z3.Sum([x[i][j] for j in range(n)])>0)

#loss
max_distance = z3.Int('max_distance')
dist = [z3.Int(f"dist_{i}") for i in range(1,m+1)]    #list of distances of each courier
for i in range(m):
    dist[i] = z3.Sum([D[j][k]*x[i][j]*x[i][k] for j in range(n) for k in range(n) if (tour[k]-tour[j]==1)]+[D[n][j]*x[i][j] for j in range(n) if (tour[j]==1)]+[D[j][n]*x[i][j] for j in range(n) if (tour[j]==z3.Sum([x[i][k] for k in range(n)]))])
    #^LA LOSS NON FUNZIONA PER GLI if!!!!!!!!!!!!!!
    solver.add(max_distance>=dist[i])

solver.add(z3.Or([max_distance==dist[i] for i in range(m)]))
solver.add(max_distance>=LB)
solver.add(max_distance<=UB)

solver.minimize(max_distance)

'''if solver.check() == z3.sat:
    model = solver.model()
    print("Sat:")
    for i in range(m):
        print([model[x[i][j]] for j in range(n)])
    print()
    print([model[tour[i]] for i in range(n)])
    print()
    print(model[max_distance])
    print()
    print([model[dist[i]] for i in range(m)])
    print()
else:
    print("Unsat")'''
status = solver.check()
print(f"PROBLEM STATUS Z3: {status}")



'''# Test
if __name__ == "__main__":
    m,n,s,w,D = read_input_file('./instances/SAT_instance.txt')
    print(s,w,D)
    result = SMT(m,n,s, w, D)
    if result:
        assignments, max_distance = result
        print("Assegnamento dei corrieri ai pacchi:")
        for i, assignment in enumerate(assignments):
            print(f"Corriere {i+1}: {assignment}")
        print("Distanza massima percorsa da un corriere:", max_distance)'''

def getSolution(solver, status, n, m):
    time = round(solver.solutionTime, 2)
    if time >= time_limit - 1:
        time = time_limit
    if not status:
        obj = 0
        sol = "N/A"
    else:
        model = solver.model()
        obj = model[max_distance]
        sol = []
        for i in range(m):
            path = []
            current = 1
            for j in range(n):
                if model[tour[j]]==current and model[x[i][j]]==1:
                    path.append(j+1)
                    current += 1
            sol.append(path)
    return time, obj, sol

saveAsJson(str(instance), solv_arg, "./res/SMT/", getSolution(solver, status, n, m))
    

