# Questions and Meeting Notes

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

