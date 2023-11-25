import z3
import sys
sys.path.append('./')
from data_handlers import saveAsJson, computeBounds, parseInstance
from argparse import ArgumentParser
import time
from math import ceil


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
m,n,l,s,D = parseInstance('./instances/'+inst_name)
LB, UB = computeBounds(D, m, n)



# Inizializza il solver Z3
solver = z3.Solver()

x = [[z3.Int(f"x_{j}_{i}") for i in range(1,1+n)] for j in range(1,1+m)]
tour = [z3.Int(f"tour_{j}") for j in range(1,1+n)]
Dmask = [[z3.Int(f"Dmask_{i}_{j}") for j in range(1,n+2)] for i in range(1,n+2)]
start_time=time.time()
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

#C4 all couriers must have at least one item
for i in range(m):
    solver.add(z3.Sum([x[i][j] for j in range(n)])>0)

#loss
max_distance = z3.Int('max_distance')
#dist = [z3.Int(f"dist_{i}") for i in range(1,m+1)]    #list of distances of each courier
dist=[]
for i in range(n):
    solver.add(z3.Implies(tour[i]==1,Dmask[n][i]==D[n][i]))
    solver.add(z3.Implies(tour[i]!=1,Dmask[n][i]==0))

    solver.add(z3.Implies(tour[i]==z3.Sum([x[k][j]*x[k][i] for j in range(n) for k in range(m)]),Dmask[i][n]==D[i][n]))
    solver.add(z3.Implies(tour[i]!=z3.Sum([x[k][j]*x[k][i] for j in range(n) for k in range(m)]),Dmask[i][n]==0))
    for j in range(n):
            solver.add(z3.Implies(tour[i]-tour[j]==1,Dmask[j][i]==D[j][i]))
            solver.add(z3.Implies(tour[i]-tour[j]!=1,Dmask[j][i]==0))
for k in range(m):
    dist.append(z3.Sum([Dmask[i][j]*x[k][i]*x[k][j] for i in range(n) for j in range(n) ]+[Dmask[n][i]*x[k][i] for i in range(n)]+[Dmask[i][n]*x[k][i] for i in range(n)]))
    solver.add(max_distance>=dist[k])

solver.add(z3.Or([max_distance==dist[i] for i in range(m)]))
solver.add(max_distance>=LB)
solver.add(max_distance<=UB)
'''solver.add(max_distance==14)
solver.add(tour[0]==3)
solver.add(tour[1]==1)
solver.add(tour[2]==2)
solver.add(tour[3]==1)
solver.add(tour[4]==2)
solver.add(tour[5]==3)'''

bestModel = None
print('Start searching...')
# binary search for the minimum cost solution
while UB > LB:
    if time.time()-start_time>time_limit:
        break
    mid = (UB + LB)//2
    solver.set('timeout',ceil(time.time()-start_time)*1000)
    res = solver.check(max_distance<=mid)
    if res == z3.sat:
        print(f"{LB} {UB} Sat for {mid}")
        bestModel = solver.model()
        UB = bestModel[max_distance].as_long()
    else:
        print(f"Unsat for {mid}")
        LB = mid+1

t = time.time() - start_time
def getSolution(best, n, m, t):
    if t >= time_limit - 1:
        t = time_limit
    if best is None:
        obj = 0
        sol = "N/A"
    else:
        obj = best[max_distance].as_long()
        sol = []
        for i in range(m):
            path = []
            current = 1
            flag=True
            while(flag):
                flag=False
                for j in range(n):
                    if best[tour[j]]==current and best[x[i][j]]==1:
                        path.append(j+1)
                        current += 1
                        flag=True
            sol.append(path)
    return t, obj, sol

saveAsJson(str(instance), solv_arg, "./res/SMT/", getSolution(bestModel, n, m, t))
if bestModel is not None:
    for i in range(n+1):
        print([bestModel[Dmask[i][j]] for j in range(n+1)])
    #for i in range(m):
        #print(bestModel[dist[i]])
    

