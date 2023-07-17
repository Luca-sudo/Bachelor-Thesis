# Literature
Dissertation: https://edoc.ub.uni-muenchen.de/13955/1/Hoffmann_Jan.pdf


# Questions and Meeting Notes

## Questions
- Sum types
	- How are they implemented on a low level?
	- What would be a good notion of cost?
	- Annotate sum type with costs or not? 
		- If yes, how to determine that cost? How do they even do it in the paper?
		- I dont think it makes sense
	- Without variables, matching on sum types is not sensical (?)

## 14.06.23

### Agenda
- As for the questions/agenda for the next time we discuss:
- Resource-annotated sum type: Why tag left and right with costs?
	- Not tagging makes more sense, no variant cost for sum type? If anything the cost would be constant?
	- W.r.t. resources, the sum type would simply cost the max of either of its nested types? That's how unions are implemented?
- Two-decades paper, page 737: Function type has no potential? Wouldn't that make the cost of 'map' invariant under the cost of the function f passed to map?
	- More generally: Does it make sense for a function to carry a potential? How do functions with different potentials compare? Since function have no before and after state, what should the meaning of the potential be?
- Typing rules, to what extend talk about them? Talk about every one vs. talk about select, illustrative examples and provide complete list in appendix?
- Subtyping relation, hofmann didnt define it for sum types and function types. Present my idea of definition and get feedback.
	- Missing subtyping for function type produces a lack of 'general typing' for functions. How to determine that then?
- Separation between evaluation judgement and resource-annotated types, try to explain my understanding of open questions from last meeting.
- Then talk about next goal(s). Maybe target AARA for quantum?
- Registering my bachelor thesis: second supervisor and TA? Anurudh for both? Conflict? 
- !!!! Submit bachelor registration very soon to adhere to deadlines !!!!!

### Notes
- Sum type example: Cost of raising errors vs producing values.
- Annotate the type of resource used.
- Define/introduce stuff like lists and trees etc.
- What is the definition of the potential of f(a)? doesnt seem to make sense. Nothing said in dissertation...
- Provide a type derivation for some example function, calculating the resource bound such as addL.
- Inconsistencies/question w.r.t. linear type system? Why do we not get reimbursed for the cost of consumed inputs?
- Michael remarks/future:
	- Simple language with only ley and tick. Define operational semantics, type rules and proof soundness, potential. To get the hang of it. Then grow from there.
