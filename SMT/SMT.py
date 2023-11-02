import z3


def read_input_file(file_path):
    with open(file_path, 'r') as file:
        m = int(file.readline().strip())
        n = int(file.readline().strip())
        s = [0 for _ in range(m)]
        s = list(map(int, file.readline().strip().split()))
        w = [0 for _ in range(n)]
        w = list(map(int, file.readline().strip().split()))

        # Inizializza la matrice delle distanze D
        D = [[0 for _ in range(n+1)] for _ in range(n+1)]

        # Leggi i valori della matrice delle distanze dalla restante parte del file
        for i in range(n+1):
            row_values = list(map(int, file.readline().strip().split()))
            D[i] = row_values

    return m, n, s, w, D


def SMT(m, n, s, w, D):
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
        solver.add(s[i] >= z3.Sum([x[i][j]*w[j] for j in range(n)]))

    #C2 different position
    for k in range(m):
        for i in range(n):
            for j in range(i + 1, n):
                solver.add(z3.Or(x[k][i]==0,x[k][j]==0, tour[i] != tour[j])) #se entrambi sono 1, allora tour sono diversi

    #C3 item delivered only once in x
    for j in range(n):
        solver.add(z3.Sum([x[i][j] for i in range(m)])==1)

    #loss
    lb = min(D[n])+min([D[i][n] for i in range(n+1)])
    ub = sum([max(D[i]) for i in range(n+1)])
    max_distance = z3.Int('max_distance')
    dist = [z3.Int(f"dist_{i}") for i in range(1,m+1)]    #list of distances of each courier
    for i in range(m):
        dist[i] = z3.Sum([D[j][k]*x[i][j]*x[i][k] for j in range(n) for k in range(n) if (tour[k]-tour[j]==1)]+[D[n][j]*x[i][j] for j in range(n) if (tour[j]==1)]+[D[j][n]*x[i][j] for j in range(n) if (tour[j]==z3.Sum([x[i][k] for k in range(n)]))])
        #^LA LOSS NON FUNZIONA PER GLI if!!!!!!!!!!!!!!
        solver.add(max_distance>=dist[i])

    solver.add(z3.Or([max_distance==dist[i] for i in range(m)]))
    solver.add(max_distance>=lb)
    solver.add(max_distance<=ub)

    solver.minimize(max_distance)

    if solver.check() == z3.sat:
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
        print(lb,ub)
    else:
        print("Unsat")



# Test
if __name__ == "__main__":
    m,n,s,w,D = read_input_file('C:/Users/utente/Desktop/cmdo project/multiple-couriers-planning/instances/SAT_instance.txt')
    print(s,w,D)
    result = SMT(m,n,s, w, D)
    if result:
        assignments, max_distance = result
        print("Assegnamento dei corrieri ai pacchi:")
        for i, assignment in enumerate(assignments):
            print(f"Corriere {i+1}: {assignment}")
        print("Distanza massima percorsa da un corriere:", max_distance)
    

