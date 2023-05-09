# Multiple Couriers Planning

The repository for our project work of Combinatorial Optimization and Decision Making course @ UniBo. 

## Project description

It has become very common recently, especially after the outbreak of the COVID19 pandemic, to send or receive items online (food, goods, clothes, documents, ...). Hence, it is more and more important for companies to efficiently schedule the dispatching of items through different couriers, in order to minimize the transportation costs.
As the combinatorial decision and optimization expert, students are asked to solve the __Multiple Couriers Planning__ (MCP) problem which is defined as follows. 
We have $m$ couriers that must distribute $n \ge m$ items at different customer locations. 
Each courier $i$ has a maximum load size $l_i$. Each item $j$ has a distribution point $j$ and a size $s_j$ (which can represent for instance a weight or a volume). 
The goal of MCP is to _decide_ for each courier _the items to be distributed_ and _plan a tour_ (i.e. a sequence of location points to visit) to perform the necessary distribution tasks. 
Each courier tour must start and end at a given origin point $o$. Moreover, the maximum load $l_i$ of the courier $i$ should be respected when items are assigned to it. To achieve a fair division among drivers, the objective is to minimize the maximum distance travelled by any courier.

# WARNING
> :warning: __NONE OF THE DRAFT MODELS WORK__.
> They are there just to provide a quick possible way of working. Obviously, these are not a way to 'cheese' the project work, rather a way to explore the use of AI Tools and how the can work. 

----
# For contributors (ovvero voi due, Davide e Nicola)
The purpose of the project work is to model and solve the MCP problem using 
1. Constraint Programming (CP), 
2. propositional SATisfiability (SAT) and/or its extension to Satisfiability Modulo Theories (SMT), and 
3. Mixed-Integer Linear Programming (MIP). 

The students will __decide themselves the decision variables__ and the problem constraints around the problem description. The project work includes building models as well as conducting an __experimental study__ to assess the performance of the solvers using different models and search strategies (where applicable). 
A suite of problem instances will be provided in the format specified in Section 1.1 for experimental purposes. No assumptions should be made based on these instances. The approach should work for any random instance.

## Beware when working...
When developing the project, students should pay attention to the following:
- Start with the instance parameters, decision variables, domains and the objective function.
- Constrain the objective function with tight lower and upper bounds.
- Though a trivial model is a good starting point, __focus on the peculiarities__ of the underlying optimization approach and try to come up with the best model so as to be able to tackle the instances in the best possible ways.
- Investigate the best way to search (where applicable).
- The _CP model_ __must be implemented in MiniZinc__ and run using at least Gecode, whereas the SAT model __must be implemented using at least Z3__. 
    - For both SMT and MIP models, students can use their favourite theories, solvers and languages. Bonus points are considered if the problem is modelled with a __solver-independent language__ (Note: the professor probably means Python), so as to try different solvers without rewriting the model. 
    - MiniZinc should be avoided here: models automatically derived from a MiniZinc model will not be considered.
    - Students are welcome to exploit different solver parameter configurations.
- __Solving processes that exceed a time limit of 5 minutes (300 secs) should be aborted__. Depending on the instances, on the solving approach, on the machine, etc., some of the instances may be too difficult to solve within the time limit. For this reason, it is not strictly necessary to succeed in solving all instances to pass the project. However, students are encouraged to improve the solution quality obtained by the time limit by using best practices.
- If any pre-solving technique is used before invoking a solver (e.g., sorting or rearranging items) then __include the time taken__ for pre-solving in the reported total runtime.

-----
# TODOs (can be seen as Sofware Engineering Tasks)

### Important/Big Tasks
- [ ] Actually do the project
- [ ] CP model
    - [x] define a model that works
    - [ ] find optimal search method and heuristics
    - [x] write python code for handling input/output
- [ ] SAT model
- [ ] SMT model

### Trivial Tasks
- [x] Write the first draft
- [ ] Note the all MiniZinc/Z3 functions that can be used in this/that the professors wants us to use. 
- [ ] Find best practices in MiniZinc/Z3
- [x] Teach Nicola GitHub (merging, branching, issues...)


----
### Considerazioni 


##### Altre considerazioni (che sistemeremo più avanti)

DESCRIZIONE CONSTRAINT CP (4/21/2023):

m: number of couriers  
n: number of items

Decision variables:

- tour: array[1...m][1...n+1] where each row contains the path of a courier. 
A path is an ordered sequence of visited points, and zeros are for padding.

- x: array[1...n] where x[i] contains the index of the courier assigned to item i. This is an auxiliary variable which simplifies constraint definition.

- counter: array[1..m] where counter[j] contains the number of items delivered by courier j. This is an auxiliary variable which simplifies the definition of constraint C6.

Constraints:
- C1: The total weight of items transported by a courier must be lower or equal than the courier's maximum laod. We use vaiable x to define this constraint.

- C2: Each item must be assigned to one and only one courier. This constraint is implied from the definition of x.

- C3: Channeling constraints
    - C3.1: Channeling constraint between tour and x (each courier can only deliver the packages specified in x, and must deliver all the packages assigned in x)

    - C3.2: Channeling constraint between x and counter

- C4: Each courier's path must start in O and end in O (n+1 index in tour). The constraint for starting from O is implied by the definition of tour. The constraint for ending in O is satisfied bu having n+1 as the last nonzero element of each row.

- C5: In each courier's path (row of tour), each courier must deliver each package only once.

- C6: Symmetry breaking constraint. Whith the variables and constraints defined above, we ignore the placement of zeros in our path rows, so the same path can be represented with any distribution of zeros inside the path. (for example the paths 1-5-3-8-0-0 and 1-0-5-0-3-8 are equivalent). This constraint requires all zeros to be after the the end of a path, removing this kind of simmetry.