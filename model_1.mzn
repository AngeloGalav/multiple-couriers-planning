include "globals.mzn"; % we could include the used globals individually

% Define the input data
int: m; % number of couriers
int: n; % number of items
array[1..m] of int: l; % maximum load size for each courier
array[1..n] of int: s; % size of each item
array[1..n+1, 1..n+1] of int: D; % distance matrix
% Note: D[i,j] is the minimum distance between distribution point i and distribution point j

% Define the decision variables
array[1..n] of var 1..m: x; % x[i] contains the index j of the courier assigned to item i. 
array[1..m, 1..n+1] of var 0..n+1: tour; % the row tour[i,..] contains the path of courier i
array[1..m] of var 1..n+1: counter; % counter[j] contains the number of items delivered by courier j

% CONSTRAINT DEFINITION

/* C1 - The total weight of items transported by a courier must be lower or equal than the courier's 
maximum laod. We use vaiable x to define this constraint. */
constraint forall(i in 1..m) (
  sum(j in 1..n where x[j] == i) (s[j]) <= l[i]
);

/* C3.1 - Channeling constraint between tour and x (each courier can only deliver the packages specified
in x, and must deliver all the packages assigned in x)*/
constraint forall(j in 1..n, i in 1..m) (
  x[j] == i <-> exists(k in 1..n+1) (tour[i, k] == j)  % (c3.1)
);

% C3.2 - Channeling constraint between x and counter
constraint forall(i in 1..m) ( 
  count_eq(x, i, counter[i])
);

% C4.2 - the number of occurrences of n+1 in tour[i,..] is constrained to 1
constraint forall(i in 1..m) (
  count_eq(tour[i, ..], n+1, 1)
);

/* C5 - In each courier's path (row of tour), each courier must deliver each package only once.
This would have been possible also by using allifferent in each row separetely. This also models
the already specified constraint which says different couriers have to deliver different items
which could improve propagation.*/
% note: may be worth trying alldifferent_except_0 on each row separately and compare performances
set of int: S = {0, n+1};
constraint (
  alldifferent_except(tour, S)
); % (c5) (in theory, we dont have to add another constraint that ensures that all values in the matrix are different, since we have vector x)

% note: may be worth remodeling tour by removing n+1 entirely and comparing performances
constraint forall(i in 1..m) (
  forall (j in counter[i]+2..n+1) (tour[i,j] == 0) % C6
  /\ forall (j in 1..counter[i]+1) (tour[i,j] > 0) % C6
  /\ tour[i, counter[i]+1] == n+1 % C4.3/C6 - this ensures the exact position of n+1
);

var int: lossf = max([sum(k in 2..n+1 where tour[i,k] > 0) (D[tour[i,k-1], tour[i,k]]) + D[n+1, tour[i,1]] | i in 1..m]); % minimize the maximum distance traveled by any courier

% Solve the problem
solve minimize lossf;
