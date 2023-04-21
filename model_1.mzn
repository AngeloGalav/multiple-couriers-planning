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
array[1..m, 1..n+1] of var 0..n+1: tour; % tour[i,k] is the k-th distribution point visited by courier i

% Define the constraints
constraint forall(i in 1..m) (
    sum(j in 1..n where x[j] == i) (s[j]) <= l[i] % each courier's load must be less than or equal to its maximum load (c1)
);

% constraint forall(j in 1..n) (
%    sum(i in 1..m) (x[i,j]) = 1 % each item must be assigned to exactly one courier (implied nella nostra implemetazione )
% );

constraint forall(i in 1..m, j in 1..n) (
   tour[i,j] > 0 <-> x[j] == i % (c3)
); 

constraint forall(i in 1..m) (
   tour[i, n+1] != 0 /\ count_eq(tour[i, ..], n+1, 1) % (c4)
);

constraint forall(i in 1..m) (
  alldifferent_except_0(tour[i, ..]) % (c5)
);

constraint forall(j in 1..n+1) (
    forall(i in 1..m) (tour[i, j] != j)
);

% -----

% constraint forall(i in 1..m, k in 1..n+1) (
%     tour[i,k] in 1..n+1 % each courier's tour must visit a valid distribution point
% );

% constraint forall(i in 1..m, j in 1..n, k in 1..n) (
%    tour[i,k] = j -> x[i,j] = 1 % if item j is visited by courier i, then it must be assigned to courier i
% );

% constraint forall(i in 1..m, k in 1..n) (
%      tour[i,k] != n+1 -> sum(j in 1..n) (x[i,j] * D[tour[i,k],j]) = sum(j in 1..n) (x[i,j] * D[tour[i,k-1],j]) + D[tour[i,k-1],tour[i,k]] % distance traveled by courier i must be consistent with its tour
% );

constraint forall(j in 1..n+1, i in 1..m) (
  tour[i,j] != 0 -> exists(k in 1..n+1) (tour[i,k] = j)
);


var int: lossf = max([sum(k in 1..n+1 where tour[i,k] > 0) (D[k, tour[i,k]]) | i in 1..m]); % minimize the maximum distance traveled by any courier
    % lo scemo non ha messo la prima somma (distanza da 'o' al primo dispatch point del tour di i)
% Solve the problem
solve minimize lossf;
