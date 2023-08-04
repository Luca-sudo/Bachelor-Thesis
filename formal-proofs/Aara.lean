import Mathlib.Tactic.Linarith

@[simp, reducible]
abbrev Resource := {r: Int // r ≥ 0}

--Needed to instantiate ResourcePairs
instance : OfNat Resource n where
  ofNat := { val := n, property := by linarith}

structure ResourcePair :=
  --Initial and Residual Resources
  rp :: (init: Resource) (resid: Resource) 

open ResourcePair

--Concrete Resource consumption, definition ... in thesis
@[simp, reducible]
def ResourcePair.consumption (p : ResourcePair) : Int := p.resid - p.init 

--Resource disparity, definition ... in thesis
@[simp, reducible]
def ResourcePair.disparity (p q : ResourcePair) := max p.resid q.init 

--Equality of resource pairs
@[simp, reducible]
def ResourcePair.equal (p q: ResourcePair) := p.init = q.init ∧ p.consumption = q.consumption

--Multiplication of resource pairs
@[simp, reducible]
def ResourcePair.mult (p q : ResourcePair) := 
  let r   := (p.init.val - p.resid + p.disparity q, by sorry)
  let r'  := (q.resid.val - q.init + p.disparity q, by sorry)
  rp r r'

-- Relaxation relation
def ResourcePair.relaxation_of (p q : ResourcePair) : Prop 
  := p.init ≥ q.init ∧ p.consumption ≥ q.consumption 

infix:50 "≽" => ResourcePair.relaxation_of

--Relaxation is partial ordering
theorem relaxation_reflexive (p : ResourcePair) : p ≽ p := by
  simp [relaxation_of]

theorem relaxation_transitive (p q r: ResourcePair) : p ≽ q → q ≽ r → p ≽ r := by
  simp [relaxation_of]
  intros H_p H_p' H_q H_q'
  apply And.intro
  apply le_trans H_q H_p
  linarith
  
theorem relaxation_antisymmetric (p q :ResourcePair) : p ≽ q → q ≽ p → p.equal q := by
  simp [relaxation_of]
  intros H_p H_p' H_q H_q'
  apply And.intro
  apply le_antisymm H_q H_p
  linarith

--Example 2.7
#eval true = (rp 4 2 ≽ rp 3 2)

--Example 2.8
#eval false = (rp 4 2 ≽ 5 4)

--Example 2.9
#eval false = (rp 5 4 ≽ rp 2 0)

--Example 2.10
#eval false = (rp 4 2 ≽ rp 5 4) ∧ false = (rp 5 4 ≽ rp 4 2)

