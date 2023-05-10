include "globals.mzn"; % we could include the used globals individually

% Define the input data
int: m; % number of couriers
int: n; % number of items
array[1..m] of int: l; % maximum load size for each courier
array[1..n] of int: s; % size of each item
array[1..n+1, 1..n+1] of int: D; % distance matrix
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
array[1..m] of var 1..n: counter; % counter[j] contains the number of items delivered by courier j

% CONSTRAINTS

/*
C1 - The total weight of items transported by a courier must be lower or equal than the courier's 
maximum laod. We use vaiable x to define this constraint.

C2 - items delivered by the same courier must be delivered at different steps, so if x[j1]==x[j2], then
tour[j1] != tour[j2] must hold.

C3 - if courier i must deliver k items [k1..kp], the relative values of tour tour[k1..kp] must be
constrained between 1 and k
    C3.1 - channeling constraint between counter and x

C4 - IMPLIED CONSTRATINT (might be useless) - if courier i must deliver k items [k1..kp], each item kl
must occur in tour[k1..kp] at least once

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

% C3.1
constraint forall(i in 1..m) ( 
  count_eq(x, i, counter[i])
);

% C3
constraint forall(i in 1..m) (
  forall(j in 1..n where x[j] == i) (
    tour[j] <= counter[i]
  )
);

function var int: seg(var int: i) = 
  1+sum(k in 1..i-1)(counter[k]);

function var int: get_item(var int: courier, var int: step) =   
  arg_sort([tour[j]+(x[j]*m)|j in 1..n])[seg(courier)+step-1];

% loss without tour_ord and seg (gives undefined)

var int: lossf =  max([ 
  sum(step in 1..counter[i]-1)(D[get_item(i, step) , get_item(i, step+1)]) + 
  D[n+1, get_item(i, 1)] + 
  D[get_item(i, counter[i]), n+1]
  | i in 1..m]);


solve minimize lossf;

output ["Solution:\n"];
output ["x =    \(x)\n"];
output ["tour = \(tour)\n"];
output ["counter = \(counter)\n"];
output ["loss = \(lossf))))\n\n"];