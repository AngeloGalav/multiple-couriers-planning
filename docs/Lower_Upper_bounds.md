### LOWER BOUND:

First idea:
Since at least one courier has to deliver an item, it needs to leave the origin node and return it.
This means at least one courier will have cost > 0, and the cost for its path will be >= mL+mR, where mL is the minimum cost required to leave the
origin, and mR is the minimum cost to return to the origin.
mL is the min value of the last row (except D[n+1, n+1]) and mR is the min value of the last column (except D[n+1, n+1]).

Improvement:
Example case - if there are 3 couriers and 4 items have to be delivered, a courier will have to deliver at least 2 items.
In this case the cost will be >= mL+mR+mC1, where C1 is the cost of the less costly edge arriving to a node different from n+1.
in this case [mC1 = min(i 1..n+1, j in 1..n where i!=j)(D[i, j])].

General case - if there are m couriers and n items, a courier will have to deliver at least [Q=ceil(n/m)] items, so he will traverse Q-1 arcs that go from item to item, and the cost will be >= mL+mR+mC1+...+mCQ-1,
where mC1,...,mCQ-1 are the Q-1 lowest cost arcs that don't involve n+1.
In general mC1,...,mCQ-1 are the first Q-1 elements of the sorted flattened array [sort(flatten(remove_diagonal(D[1:n+1, 1:n])))]

Second improvement:
In the previous improvement, if two values mCi and mCj are two arcs that arrive at the same node, they can't both be traversed. We can get a tighter lower
bound by computing the minimum cost of arrival for each node as m_j = min(i 1..n with i!=j){D[i, j]} for j in 1..n, and then take as mC1, .., mCQ-1 the lowest m_j values (LB = mL + mR + mC1 + ... + mCQ-1).
This is also more efficient since sorting all costs is O(n^2*log(n^2)), while this algorithm is O(n^2 + nlog(n))=O(n^2)



### UPPER BOUND:

First idea:
The solution with the highest cost is a solution where all items are delivered by one courier, and the path is a an hemiltonian cycle with the highest
possible cost. If we have n nodes, the worst solution will have a cost <= than (M_1 + M_2 + ... + M_n + M_(n+1)), where M_i is the cost of the most costly
edge arriving to node i [M_i = max(j in 1..n+1 where j!=i)(D[j, i])]
