% Define input variables
int: m; % number of couriers
int: n; % number of items
array[1..m] of int: l; % maximum load size for each courier
array[1..n] of int: s; % size of each item
array[1..n+1, 1..n+1] of int: D; % distance matrix

% Define decision variables
array[1..n] of var 1..m: x; % courier assigned to each item
array[1..m, 1..n+2] of var 1..n+1: y; % order of locations visited by each courier

% Define constraints
constraint forall(i in 1..n) (
  sum(j in 1..m) (x[i] = j) = 1 % each item is assigned to exactly one courier
);
constraint forall(j in 1..m) (
  sum(i in 1..n) (s[i] * (x[i] = j)) <= l[j] % total size assigned to each courier does not exceed maximum load
);
constraint forall(j in 1..m) (
  y[j, 1] = y[j, n+2] % each courier starts and ends at origin point
);
constraint forall(j in 1..m) (
  y[j, 1] = n+1 % each courier starts at origin point
);
constraint forall(j in 1..m) (
  y[j, n+2] = n+1 % each courier ends at origin point
);
constraint forall(j in 1..m, k in 2..n+1) (
  y[j, k] != n+1 % each courier visits all locations except origin point
);
constraint forall(j in 1..m) (
  forall(k in 1..n+1) (
    y[j, k] != y[j, k+1] % each courier visits each location exactly once
  )
);
constraint forall(j in 1..m) (
  forall(k in 1..n+1) (
    y[j, k] >= 1 /\ y[j, k] <= n+1 % each location is visited by at least one courier and at most n+1 couriers
  )
);
constraint forall(i in 1..n, j in 1..m) (
  y[j, index(x, j, i)+1] >= index(x, j, i) % items assigned to courier j are visited in the assigned order
);
constraint forall(j in 1..m) (
  sum(k in 2..n+2) (D[y[j, k-1], y[j, k]]) <= sum(k in 1..m) (max(k in 2..n+2) (D[y[k, k-1], y[k, k]]) / m) % minimize the maximum distance travelled by any courier
);

% Define objective
var int: max_distance = max(j in 1..m) (sum(k in 2..n+2) (D[y[j, k-1], y[j, k]]));
solve minimize max_distance;

% Output solution
output ["Maximum distance: \(max_distance)\n"] ++
       ["Courier assigned to item \(i): \(x[i])\n" | i in 1..n] ++
       ["Order of locations visited by courier \(j): \(y[j])\n" | j in 1..m];
