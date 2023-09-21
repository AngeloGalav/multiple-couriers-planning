from z3 import *


def read_input_file(file_path):
    with open(file_path, 'r') as file:
        m = int(file.readline().strip())
        n = int(file.readline().strip())
        s = [0 for _ in range(m)]
        w = [0 for _ in range(n)]

        # Inizializza la matrice delle distanze D
        D = [[0 for _ in range(n+1)] for _ in range(n+1)]

        # Leggi i valori della matrice delle distanze dalla restante parte del file
        for i in range(n+1):
            row_values = list(map(int, file.readline().strip().split()))
            D[i] = row_values

    return m, n, s, w, D


def solve_multi_courier_problem(m, n, s, w, D):
    # Inizializza il solver Z3
    solver = Optimize()

    x = [Int(f"x_{j}") for j in range(n)]
    tour = [Int(f"tour_{j}") for j in range(n)]
    #x = Array('x', IntSort(), IntSort()) #(declare-fun x () (Array Int Int))
    #tour = Array('tour', IntSort(), IntSort()) #(declare-fun tour () (Array Int Int))

    #Domains
    for i in range(n):
        solver.add(x[i]>=1)
        solver.add(x[i]<=m)
        solver.add(tour[i]>=1)
        solver.add(tour[i]<=Sum([If(x[k]==x[i],1,0) for k in range(n)]))

    #C1
    for i in range(m):
        solver.add(s[i]>=Sum([If(x[j]==i,w[j],0) for j in range(n)]))

    #C2
    for i in range(n):
        for j in range(i + 1, n):  # Solo coppie con i != j
            solver.add(Implies(x[i] == x[j], tour[i] != tour[j]))

    #C3 is already written in the domain part

    #loss
    max_distance = Int('max_distance')
    for i in range(m):
        distance = Int('distance')
        distance = Sum([D[j][k] for j in range(n) for k in range(n) if (x[j]==i and x[k]==i and tour[k]-tour[j]==1)])
        max_distance = If(max_distance<distance,distance, max_distance)

    #solver.add(max_distance == Sum([If(tour[k] == D[n][n+1+k], D[k][k_next], 0) for k_next in range(n+1) for i in range(m)])+D[0][])
    #solver.add(max_distance)
    solver.minimize(max_distance)

    if solver.check() == sat:
        model = solver.model()
        print("Sat:")
        print(model)
    else:
        print("Unsat")



# Test
if __name__ == "__main__":
    m,n,s,w,D = read_input_file('generated_unformatted_instance.txt')
    result = solve_multi_courier_problem(m,n,s, w, D)
    if result:
        assignments, max_distance = result
        print("Assegnamento dei corrieri ai pacchi:")
        for i, assignment in enumerate(assignments):
            print(f"Corriere {i+1}: {assignment}")
        print("Distanza massima percorsa da un corriere:", max_distance)
    

