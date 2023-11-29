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

% Define the decision variables
array[1..n] of var 1..m: x; % x[i] contains the index j of the courier assigned to item i. 
array[1..n+m+1] of var 1..n+1: tour; % a segment tour[seg[k]..seg[k+1]] defines the path fpr courier k, segments are separated by n+1 (which also occurs in the first and last position)
array[1..m] of var 1..n: count; % count[k] contains the number of items assigned to courier k
array[1..m+1] of var 1..n+m+1: seg; % seg[k] is the position of the k-th occurrence of n+1 in tour

var LB..UB: cost;

% CONSTRAINT DEFINITION

% C1 - The total weight of items transported by a courier must be lower or equal than the courier's maximum laod.
constraint bin_packing_capa(l, x, s);

% C2 - each path starts and ends with n+1
constraint tour[1] = n+1;
constraint tour[n+m+1] = n+1;
constraint count_eq(tour, n+1, m+1);

% C3 - seg constraints
constraint strictly_increasing(seg); % segments must be ordered (implied constraint)
constraint forall(k in 1..m+1)(tour[seg[k]] = n+1); % segment indices correspond to n+1 in tour

% C4 - count constraints
constraint forall(k in 1..m) ( 
  count_eq(x, k, count[k])
);
constraint forall(k in 1..m)(seg[k+1] = seg[k]+count[k]+1); % syncronization between count and segment

% C5 - If a courier delivers item i, then value i must appear in the correct segment of tour
constraint forall(i in 1..n, k in 1..m) (
  x[i] = k <-> exists(j in seg[k]+1..seg[k+1]-1)(tour[j] = i)
);

% C6 - Each package is delivered once (implied constraint)
constraint alldifferent_except(tour, {n+1});

constraint cost = max([sum(i in seg[k]..seg[k+1]-1)(D[tour[i], tour[i+1]])| k in 1..m]);

%solve :: int_search(tour, dom_w_deg, indomain_min) minimize cost :: restart_luby(2);

%annotations here
solve :: int_search(tour, input_order, indomain_min) minimize cost :: restart_linear(5);


% output ["Solution:\n"];
% output ["x =    \(x)\n"];
% output ["tour = \(tour)\n"];
% output ["seg = \(seg)\n"];
% output ["count = \(count)\n"];
% output ["objective = \(cost)\n\n"];