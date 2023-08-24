import Mathlib.Tactic.Linarith


@[simp, reducible]
notation "Resource" => Nat

@[simp, reducible]
abbrev ResourceDemand := Resource × Resource

namespace ResourceDemand

@[simp, reducible]
--Initial resources
def init : ResourceDemand → Resource := Prod.fst

@[simp, reducible]
--Residual resources
def resid : ResourceDemand → Resource := Prod.snd 

--Concrete Resource consumption, definition ... in thesis
@[simp, reducible]
def consumption (p : ResourceDemand) : Int := p.init - p.resid 

--Resource disparity, definition ... in thesis
@[simp, reducible]
def disparity (p q : ResourceDemand) : Resource := max p.resid q.init 

--Multiplication of resource pairs
@[simp, reducible]
def sequence (p q : ResourceDemand) : ResourceDemand := 
  (p.init + p.disparity q - p.resid, q.resid + p.disparity q - q.init)

infix:50 "▹" => sequence

--Neutral element in Resource Demands
def unit : ResourceDemand := (0, 0)

@[simp, reducible]
-- Relaxation relation
def relaxation_of (p q : ResourceDemand) : Bool 
  := (p.init ≥ q.init) ∧ (p.consumption ≥ q.consumption) 

@[simp]
infix:50 "≽" => relaxation_of

--Example 2.5
#eval (4, 2) ▹ (5, 0) -- (7, 0)

--Example 2.7
#eval ((4, 2) ≽ (3, 2)) --true

--Example 2.8
#eval ((4, 2) ≽ (5, 4)) --false

--Example 2.9
#eval ((5, 4) ≽ (2, 0)) --false

--Example 2.10
#eval ((4, 2) ≽ (5, 4)) ∧ ((5, 4) ≽ (4, 2)) --false

-- Example 2.14
#eval (4, 2) = (4, 3) -- false


end ResourceDemand