include "globals.mzn"; % we could include the used globals individually

% Define the input data
int: m; % number of couriers
int: n; % number of items
array[1..m] of int: l; % maximum load size for each courier
array[1..n] of int: s; % size of each item
array[1..n+1, 1..n+1] of int: D; % distance matrix
% Note: D[i,j] is the minimum distance between distribution point i and distribution point j

/* The idea of this second model is to remove the useless decision variables we have in the original version
of tour (given by the high number of zeros we use as padding). In this version tour is a uni dimensional vector
which contains the concatenation of the relevant parts of each row of the previous model. This shoulden't 
complicate constraint definitions much, since we can divide tour in segments through slicing and the counter
variable. This way we reduce the amount of decision variables from m*(n+1) to n. 

example - model_1 vs model_2.

-- model_1
x = [3, 1, 2, 1, 1, 3, 2];
counter = [3, 2, 2]
tour = 
[| 2, 4, 5, 8, 0, 0, 0, 0
 | 7, 3, 8, 0, 0, 0, 0, 0
 | 1, 6, 8, 0, 0, 0, 0, 0
 |];

-- model_2
x = [3, 1, 2, 1, 1, 3, 2];
counter = [3, 2, 2];
tour = [2, 4, 5, 7, 3, 1, 6];
*/

% Define the decision variables
array[1..n] of var 1..m: x; % x[i] contains the index j of the courier assigned to item i. 
array[1..n] of var 0..n: tour; % a segment tour[k..l] defines a path for a courier
array[1..m] of var 1..n: counter; % count[i] contains the number of items delivered by courier i
array[1..m+1] of var 1..n+1: seg; /* seg[1..m] defines the starting indexes of the segments in tour
and seg[m+1] = n+1, so that we can access the i-th segment of tour through slicing with 
tour[seg[i]..seg[i+1]-1]*/

% CONSTRAINT DEFINITION

/* C1 - The total weight of items transported by a courier must be lower or equal than the courier's 
maximum laod. We use vaiable x to define this constraint. */
constraint forall(i in 1..m) (
  sum(j in 1..n where x[j] == i) (s[j]) <= l[i]
);

/* C3.1 - Channeling constraint between tour and x (each courier can only deliver the packages specified
in x, and must deliver all the packages assigned in x)*/
constraint forall(j in 1..n, i in 1..m) (
  x[j] == i <-> exists(k in seg[i]..seg[i+1]-1) (tour[k] == j)
);

% C3.2 - Channeling constraint between x and counter
constraint forall(i in 1..m) ( 
  count_eq(x, i, counter[i])
);

% C3.3 - Channeling constraint between seg and count
constraint (
  forall(i in 1..m)(seg[i] = 1+sum(k in 1..i-1)(counter[k])) /\
  seg[m+1] = n+1
);

% C4.2 and C4.3 are implied

/* C5 - In each courier's path (segment of tour), each courier must deliver each package only once.*/
constraint alldifferent(tour);

var int: lossf = max([sum(k in seg[i]..seg[i+1]-2)(D[tour[k], tour[k+1]]) + D[n+1, tour[seg[i]]] + D[tour[seg[i+1]-1], n+1] | i in 1..m]); % minimize the maximum distance traveled by any courier

% Solve the problem
solve minimize lossf;

output ["Solution:\n"];
output ["x = \(x)\n"];
output ["tour = \(tour)\n"];
output ["Loss = \(lossf)\n\n"];