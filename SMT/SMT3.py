from z3 import *


def read_input_file(file_path):
    with open(file_path, 'r') as file:
        m = int(file.readline().strip())
        n = int(file.readline().strip())
        s = [0 for _ in range(m)]
        w = [0 for _ in range(n)]

        s = list(map(int, file.readline().strip().split()))


        w = list(map(int, file.readline().strip().split()))


        # Inizializza la matrice delle distanze D
        D = [[0 for _ in range(n+2)] for _ in range(n+2)]

        # Leggi i valori della matrice delle distanze dalla restante parte del file
        for i in range(n+2):
            row_values = list(map(int, file.readline().strip().split()))
            D[i] = row_values

    return n, m, s, w, D


def solve_multi_courier_problem(n, m, s, w, D):
    # Inizializza il solver Z3
    solver = Optimize()

    variables={}
    weight={}

    for i in range(1,m+1):
        for j in range(1,n+2):
            variables[f'c{i}p{j}'] = Const(f'c{i}p{j}', IntSort())
            weight[f'c{i}p{j}'] = Const(f'c{i}p{j}', IntSort())
            solver.add(variables[f'c{i}p{j}']>=1,variables[f'c{i}p{j}']<=n+1)
    for i in range(1,m+1):
        for j in range(1,n+1):        
            solver.add(Implies(variables[f'c{i}p{j}']==n+1,variables[f'c{i}p{j+1}']==n+1))

    for val in range(1,n+1):
        solver.add(Sum([variables[f'c{i}p{j}']==val for i in range(1,m+1) for j in range(1,n+2)])==1)
    #solver.add(ForAll([C,O,C2,O2],Or(delivery(i,j)!=delivery(C2,O2),delivery(C,O)==0,And(C==C2,O==O2))))
    #for val in range(1,n+1):
        #solver.add(Exists([C,O],delivery(C,O)==val))
    #solver.add(ForAll([C,O],Implies(And(delivery(C,O)==0,C>=1,C<=m,O>=1,O<n),delivery(C,O+1)==0)))

    #pesi
    for i in range(1,m+1):
        for j in range(1,n+1):
            weight[f'c{i}p{j}'] = Const(f'c{i}p{j}', IntSort())
            for k in range(1,n+1):
                solver.add(Implies(variables[f'c{i}p{j}']==k,weight[f'c{i}p{k}']==w[k-1]))
                solver.add(Implies(variables[f'c{i}p{j}']!=k,weight[f'c{i}p{k}']==0))
        solver.add(Sum([weight[f'c{i}p{j}'] for j in range(1,n+1)])<=s[i-1])

    #loss
    '''d_max = 0
    for i in range(1,m+1):
        d = Sum([D[variables[f'c{i}p{j}']-1][variables[f'c{i}p{j+1}']-1] for j in range(1,n+1)]) + D[n][variables[f'c{i}p{1}']-1]
        d_max = If(d>d_max,d,d_max)
    solver.minimize(d_max)'''
    
    if solver.check() == sat:
        model = solver.model()
        print("Sat:")
        print(model)
    else:
        print("Unsat")



# Test
if __name__ == "__main__":
    n,m,s,w,D = read_input_file('generated_unformatted_instance.txt')
    result = solve_multi_courier_problem(n,m,s, w, D)

    if result:
        assignments, max_distance = result
        print("Assegnamento dei corrieri ai pacchi:")
        for i, assignment in enumerate(assignments):
            print(f"Corriere {i+1}: {assignment}")
        print("Distanza massima percorsa da un corriere:", max_distance)
    

