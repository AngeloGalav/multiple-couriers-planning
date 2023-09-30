import numpy as np
from itertools import combinations

def find_optimal_tours(m, n, l, s, D):
    # Initialize the solution with empty tours for each courier
    solution = [[] for _ in range(m)]
    # Initialize the remaining items as a set
    remaining = set(range(1, n+1))
    # Sort the items in decreasing order of size
    items = sorted(range(1, n+1), key=lambda i: -s[i-1])
    # Loop over all possible combinations of couriers to assign to
    for c in combinations(range(m), len(items)):
        # Create a copy of the remaining items
        remaining_copy = remaining.copy()
        # Loop over the assigned couriers
        for i in c:
            # Create a copy of the remaining items for this courier
            remaining_i = remaining_copy.copy()
            # Sort the remaining items by increasing distance from the origin
            remaining_i = sorted(remaining_i, key=lambda j: D[0][j])
            # Loop over the remaining items for this courier
            for j in remaining_i:
                # Check if the item fits in the courier's load
                if s[j-1] <= l[i]:
                    # Add the item to the courier's tour
                    solution[i].append(j)
                    # Remove the item from the remaining set
                    remaining_copy.remove(j)
                    # Update the courier's load
                    l[i] -= s[j-1]
        # If all items have been assigned, return the solution
        if not remaining_copy:
            return solution
    # If no solution was found, return None
    return None

# Example usage
m = 3
n = 7
l = [15, 10, 7]
s = [3, 2, 6, 8, 5, 4, 4]
D = np.array([
    [0, 3, 3, 6, 5, 6, 6, 2],
    [3, 0, 4, 3, 4, 7, 7, 3],
    [3, 4, 0, 7, 6, 3, 5, 3],
    [6, 3, 7, 0, 3, 6, 6, 4],
    [5, 4, 6, 3, 0, 3, 3, 3],
    [6, 7, 3, 6, 3, 0, 2, 4],
    [6, 7, 5, 6, 3, 2, 0, 4],
    [2, 3, 3, 4, 3, 4, 4, 0]
])
solution = find_optimal_tours(m, n, l, s, D)
print(solution)

