import Mathlib.Tactic.Linarith

@[simp, reducible]
abbrev ResourceDemand := Nat × Nat

namespace ResourceDemand

--Concrete Resource consumption, definition ... in thesis
@[simp]
def consumption (p : ResourceDemand) : Int := p.1 - p.2 

--Resource disparity, definition ... in thesis
@[simp]
def disparity (p q : ResourceDemand) : Nat := max p.2 q.1 


--Multiplication of resource pairs
@[simp, reducible]
def sequence (p q : ResourceDemand) : ResourceDemand := 
  (p.1 - p.2 + max p.2 q.1, q.2 - q.1 + max p.2 q.1) 

infixl:50 "▹" => sequence

--Neutral element in Resource Demands
def unit : ResourceDemand := (0, 0)

@[simp]
-- Relaxation relation
def relaxation_of (p q : ResourceDemand) : Prop
  := p.1 ≥ q.1 ∧ (p.1 - p.2) ≥ (q.1 - q.2)

infix:50 "≽" => relaxation_of

--Example 2.5
#eval (4, 2) ▹ (5, 0) -- (7, 0)

--Example 2.7
-- #eval ((4, 2) ≽ (3, 2)) --true

--Example 2.8
-- #eval ((4, 2) ≽ (5, 4)) --false

--Example 2.9
-- #eval ((5, 4) ≽ (2, 0)) --false

--Example 2.10
-- #eval ((4, 2) ≽ (5, 4)) ∧ ((5, 4) ≽ (4, 2)) --false

-- Example 2.14
#eval (4, 2) = (4, 3) -- false


end ResourceDemand