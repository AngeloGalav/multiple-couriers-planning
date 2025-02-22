include "globals.mzn"; % we could include the used globals individually

% Define the input data
int: m; % number of couriers
int: n; % number of items
array[1..m] of int: l; % maximum load size for each courier
array[1..n] of int: s; % size of each item
array[1..n+1, 1..n+1] of int: D; % distance matrix
int: LB;
int: UB;
% Note: D[i,j] is the minimum distance between distribution point i and distribution point j

/*The idea is to improve on model_2 by modifying the representation of tour. The reason model_2 is slow might be because
the fact that we don't know initially which variables have to be used for each courier, so if for example
courier 2 decides to start from delivering item 5, the position in which we have to put 5 might vary 
from solution to solution, creating a lot of useless "uncertainty" and way more failures. 

This model still uses a monodimensional array for tour of n elements (one for each item), but
tour[j] strictly gives information about the delivery of item j. To do so, we still use x the same as
the previous models, so we already know which couriers have to deliver which packages. Then if courier
i has to deliver item j, tour[j] is the step of the path at which courier i deliver item j. 
For example, if courier 2 delivers items [2, 6, 3] in this order, then tour[2]=1, tour[6]=2, tour[3]=3.*/

array[1..n] of var 1..m: x; % x[i] contains the index j of the courier assigned to item i. 
array[1..n] of var 1..n: tour; % tour[j] is defined in the comment above

var LB..UB: cost;

% CONSTRAINTS

/*
C1 - The total weight of items transported by a courier must be lower or equal than the courier's 
maximum laod. We use vaiable x to define this constraint.

C2 - items delivered by the same courier must be delivered at different steps, so if x[j1]==x[j2], then
tour[j1] != tour[j2] must hold.

C3 - if courier i must deliver k items [k1..kp], the relative values of tour tour[k1..kp] must be
constrained between 1 and k

note: if two couriers have the same load size, it might be worth adding some specific symmetry 
breaking constraints
*/

% C1
constraint forall(i in 1..m) (
  sum(j in 1..n where x[j] == i) (s[j]) <= l[i]
);

% C2
constraint forall(i in 1..m) (
  alldifferent([tour[j] | j in 1..n where x[j] == i])
);

% C3
constraint forall(i in 1..m) (
  forall(j in 1..n where x[j] == i) (
    count_leq(x, i, tour[j])
  )
)::bounds;
  
% in case two couriers have the same max load, we have a simmetry in the assignment of items
% we impose that the first item assigned to k1 has lower index than the first item assigned to k2
constraint symmetry_breaking_constraint(
  forall(k1, k2 in 1..m where l[k1] == l[k2] /\ k1 != k2)(
    min(i in 1..n where x[i] == k1)(i) < min(j in 1..n where x[j] == k2)(j)
  )
);

% this constraint performs simmetry breaking on item assignments (may have better propagation)
constraint symmetry_breaking_constraint(
  forall(k1, k2 in 1..m where k1 < k2 /\ l[k1] == l[k2]) (
    sum(j in 1..n where x[j] == k1)(s[j]) <= sum(j in 1..n where x[j] == k2)(s[j])
  )
);

% in case all the matrix is symmetrical, every path is equivalent to the inverse path
% we impose that, for a certain path, the item assigned first has smaller index than the item assigned last
constraint symmetry_breaking_constraint(
  if forall(i, j in 1..n+1)(D[i, j] == D[j, i])
  then forall(i, j in 1..n where i!=j /\ x[i]==x[j] /\ tour[i]==1 /\ tour[j]==count(x, i))(i < j)
  endif
);
  
constraint cost == max([
  sum(j1, j2 in 1..n where tour[j2]-tour[j1] == 1 /\ x[j1] == i /\ x[j2] == i)(D[j1, j2]) + 
  sum(j in 1..n where tour[j]==1 /\ x[j]==i)(D[n+1, j]) + 
  sum(j in 1..n where tour[j]==count(x, i) /\ x[j]==i)(D[j, n+1])
  |i in 1..m]);

solve minimize cost;

output ["Solution:\n"];
output ["x =    \(x)\n"];
output ["tour = \(tour)\n"];
output ["objective = \(cost)\n\n"];