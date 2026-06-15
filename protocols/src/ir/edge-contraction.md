**Edge Contraction**
- to handle control flow, we should contract edges while keeping the RHS node around. this will allow us to only contract on one edge at a time. 

Straight line protocols:
- a *straight line* protocol has all non exit-nodes with in degree 1 and out degree 1
- an edge is eligible for contraction if it is not a step edge. 
- a non step edge can be contracted. we take the RHS node, take all its actions and add them with the transition condition, and then stick them in the LHS node. All of the RHS nodes outgoing transitions become AND-ed with the ingoing transition and go to the next edge.
- just because I feel like it, we contract right to left (the rightmost edge we can find is the most eligible for contraction)
