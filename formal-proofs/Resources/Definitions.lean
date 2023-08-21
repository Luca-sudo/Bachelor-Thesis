import Mathlib.Tactic.Linarith


notation "Resource" => Nat

abbrev ResourceDemand := Resource × Resource

namespace ResourceDemand

--Initial resources
def init : ResourceDemand → Resource := Prod.fst

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
  let r := p.init + p.disparity q - p.resid 
  let r':= q.resid + p.disparity q - q.init 
  (r, r')

infix:50 "▹" => sequence

--Neutral element in Resource Demands
def unit : ResourceDemand := (0, 0)

-- Relaxation relation
def relaxation_of (p q : ResourceDemand) : Bool 
  := (p.init ≥ q.init) ∧ (p.consumption ≥ q.consumption) 

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