include "globals.mzn"; % cambiare in alldifferent.mzn?

% Define the input data
int: m; % number of couriers
int: n; % number of items
array[1..m] of int: l; % maximum load size for each courier
array[1..n] of int: s; % size of each item
array[1..n+1, 1..n+1] of int: D; % distance matrix
% Note: D[i,j] is the distance between distribution point i and distribution point j

% Define the decision variables
array[1..n] of var 1..m: x; % x[i] contains the index j of the courier assigned to item i. 
array[1..m, 1..n] of var 0..n: tour; % tour[i,k] is the k-th distribution point visited by courier i.
array[1..m] of var 1..n: counter;

% Define the constraints
constraint forall(i in 1..m) (
  sum(j in 1..n where x[j] == i) (s[j]) <= l[i] % each courier's load must be less than or equal to its maximum load (c1)
);

constraint forall(j in 1..n) (
  forall(i in 1..m) (x[j] == i <-> exists(k in 1..n) (tour[i, k] == j))  % (c3.1)
);

constraint forall(i in 1..m) ( 
  count_eq(x, i, counter[i])
); % assigns value to the counter variable

constraint forall(i in 1..m) (
  forall (j in counter[i]+1..n) (tour[i,j] == 0)  
  /\ forall (j in 1..counter[i]) (tour[i,j] > 0)    % (c4.1) the number of occurrences of n+1 in tour[i,..] is constrained to 1.
);

% (c4.2)

set of int: S = {0, n+1};
constraint (
  alldifferent_except_0(tour)
); % (c5) (in theory, we dont have to add another constraint that ensures that all values in the matrix are different, since we have vector x)

var int: lossf = max([sum(k in 2..n where tour[i,k] > 0) (D[tour[i,k-1], tour[i,k]]) + D[n+1, tour[i,1]] + D[tour[i,counter[i]],n+1] | i in 1..m]); % minimize the maximum distance traveled by any courier

% Solve the problem
solve minimize lossf;
