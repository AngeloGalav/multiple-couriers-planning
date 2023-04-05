# Multiple Couriers Planning

The repository for our project work of Combinatorial Optimization and Decision Making course @ UniBo. 

## Project description

It has become very common recently, especially after the outbreak of the COVID19 pandemic, to send or receive items online (food, goods, clothes, documents, ...). Hence, it is more and more important for companies to efficiently schedule the dispatching of items through different couriers, in order to minimize the transportation costs.
As the combinatorial decision and optimization expert, students are asked to solve the __Multiple Couriers Planning__ (MCP) problem which is defined as follows. 
We have $m$ couriers that must distribute $n \ge m$ items at different customer locations. 
Each courier $i$ has a maximum load size $l_i$. Each item $j$ has a distribution point $j$ and a size $s_j$ (which can represent for instance a weight or a volume). 
The goal of MCP is to _decide_ for each courier _the items to be distributed_ and _plan a tour_ (i.e. a sequence of location points to visit) to perform the necessary distribution tasks. 
Each courier tour must start and end at a given origin point $o$. Moreover, the maximum load $l_i$ of the courier $i$ should be respected when items are assigned to it. To achieve a fair division among drivers, the objective is to minimize the maximum distance travelled by any courier.

angelo