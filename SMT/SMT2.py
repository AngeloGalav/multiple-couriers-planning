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

    return n, m, s, w, D


def solve_multi_courier_problem(n, m, s, w, D):
    # Inizializza il solver Z3
    solver = Solver()

    array_2d = [[Int(f'array_2d_{i}_{j}') for j in range(n)] for i in range(m)]

    
    #dominio
    for i in range(m):
        for j in range(n):
            solver.add(array_2d[i][j]>=0)
            solver.add(array_2d[i][j]<=n)

    for val in range(1,n+1):  #il paco val c'è solo 1 volta
        solver.add(Sum([If(array_2d[i][j]==val,1,0) for i in range(m) for j in range(n)])==1)
    
    for i in range(m):                  #gli zeri stanno alla fine
        for j in range(n-1):
            solver.add(Implies(array_2d[i][j]==0,array_2d[i][j+1]==0))

    #loss
    max_distance = Int('max_distance')
    for i in range(m):
        solver.add(If(j+1!=0,D[]))
    #solver.minimize(max_distance)
    
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
    print('ciaomain')
    if result:
        assignments, max_distance = result
        print("Assegnamento dei corrieri ai pacchi:")
        for i, assignment in enumerate(assignments):
            print(f"Corriere {i+1}: {assignment}")
        print("Distanza massima percorsa da un corriere:", max_distance)
    

