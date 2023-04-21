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
    - [ ] SAT model
    - [ ] SMT model

### Trivial Tasks
- [ ] Write the first draft
- [ ] Note the all MiniZinc/Z3 functions that can be used in this/that the professors wants us to use. 
- [ ] Find best practices in MiniZinc/Z3
- [ ] Teach Nicola GitHub (merging, branching, issues...)


----
### Considerazioni 
- Abbiamo usato la x come ci ha proposto Luca, anche se potremmo usare solo `tour`. 
    - È una variabile implicita, nel senso che anche se è ridondante in termini delle informazioni, ci aiuta coi costi computazionali in termini di tempo. 