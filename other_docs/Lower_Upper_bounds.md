### LOWER BOUND:
Minimum arrival costs bound:
If there are m couriers and n items, a courier will have to deliver at least [Q=ceil(n/m)] items, so he will go from the origin to the first item, then travel from item to item Q-1 times, and then return to the origin. We can compute the minimum cost of arrival for each node as m_j = min(i 1..n with i!=j){D[i, j]} for j in 1..n, and then select the Q-1 smallest m_j values mC1, .., mCQ-1. This means the optimal solution will have a cost <= mL + mR + mC1 + ... + mCQ-1, where mR and mL are the minimum costs for leaving and returning to the origin respectively.

Maximum simple path cost:
Consider two paths P1 and P2 that both deliver item i, where P1 only delivers item i, while P2 delivers i ans any number of other items. The cost of P1 is D[n+1, i]+D[i, n+1], and the cost of P2 will be D[n+1, k1]+...+D[k2, i]+D[i, k3]+...+D[k4, n+1]. Since the inequality D[i, j] <= D[i, k]+D[k, j] holds, then D[n+1, i] <= D[n+1, k1]+...+D[k2, i] and D[i, n+1] <= D[i, k3]+...+D[k4, n+1], so P1's cost is always lesser or equal than P2's cost. 
We can then compute the cost of all such simple paths Pj (that deliver only one item), and compute the lower bound ad the maximum cost among such simple paths (LB = max(j in 1..n)(D[n+1,j]+D[j,n+1])). 

We ca use both and select the highest lower bound among the two, generally the second bound is way better

### UPPER BOUND:
Minimum arrival costs bound:
A courier can deliver at most Q=n-m+1 items since each courier has atleast one item. In that case it leaves the origin, travels from node to node Q-1 times and returns to the origin. We can compute the maximum cost of arrival for each node as M_j = max(i 1..n with i!=j){D[i, j]} for j in 1..n, and then select the Q-1 biggest M_j values MC1,..,MCQ-1. This means the optimal solution will have a cost >= ML + MR + MC1 + ... + MCQ-1, where MR and ML are the maximum costs for leaving and returning to the origin respectively.


### Keep in mind:
- Cols are the prices of arriving to node i from all other nodes
- Rows are the prices of departing from node i to all of nodes