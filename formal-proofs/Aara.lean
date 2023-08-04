import Mathlib.Tactic.Linarith

@[simp, reducible]
abbrev Resource := {r: Int // r ≥ 0}

--Needed to instantiate ResourcePairs
instance : OfNat Resource n where
  ofNat := { val := n, property := by linarith}

structure ResourcePair where
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
  let r : Resource   := {val := p.init.val - p.resid + p.disparity q, property := by sorry}
  let r': Resource   := {val := q.resid.val - q.init + p.disparity q, property := by sorry}
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


namespace LetTick

inductive Prog :=
  | tick (k : Int)
  | let (e_1 e_2 : Prog)

inductive BaseType :=
  | Unit

def RAType := BaseType × ResourcePair

--Evaluation judgement
inductive Evaluation : Prog → ResourcePair → Prop :=
  | e_tick_pos (k : Int) (pos : k ≥ 0):
    Evaluation (.tick k) (rp ⟨k, pos⟩ 0) 
  | e_tick_neg (k : Int) (neg: k < 0):
    Evaluation (.tick (abs k)) (rp ⟨(abs k), abs_nonneg k⟩ 0)
  | e_let {e_1 e_2 : Prog} {r_1 r_2 : ResourcePair} (eval_e_1 : Evaluation e_1 r_1) (eval_e_2 : Evaluation e_2 r_2)
    : Evaluation (.let e_1 e_2) (r_1.mult r_2)

--Typing judgement
inductive Typing : Prog → BaseType → ResourcePair → Prop :=
  | t_tick (k : Int) (t : BaseType) (r : ResourcePair) (suff_res : r.init ≥ k + r.resid) :
    Typing (.tick k) t r
  | t_let {e_1 e_2 : Prog} {r_1 r_2 : ResourcePair} {t_1 t_2 : BaseType} (e_1types : Typing e_1 t_1 r_1) (e_2Types : Typing e_2 t_2 r_2) (suff_res : r_1.resid = r_2.init) :
    Typing (.let e_1 e_2) t_2 (rp r_1.init r_2.resid)

--Proof of soundness. Theorem 3.5
theorem soundness (p : Prog) (r_1 r_2 : ResourcePair) (t : BaseType) 
  : Evaluation p r_1 → Typing p t r_2 → r_2 ≽ r_1 := by
    sorry
  
end LetTick

