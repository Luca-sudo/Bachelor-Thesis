import Mathlib.Tactic.Linarith

@[simp, reducible]
abbrev Resource := {r: Int // r ≥ 0}


--Needed to instantiate ResourceDemands
instance : OfNat Resource n where
  ofNat := { val := n, property := by linarith}

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

--Equality of resource pairs
@[simp, reducible]
def equal (p q: ResourceDemand) := p.init = q.init ∧ p.consumption = q.consumption

--Neutral element in Resource Pairs
def unit : ResourceDemand := (0, 0)

--Multiplication of resource pairs
@[simp, reducible]
def sequence (p q : ResourceDemand) : ResourcePair := 
  let r := {val := p.init.val - p.resid + p.disparity q, property := by sorry}
  let r':= {val := q.resid.val - q.init + p.disparity q, property := by sorry}
  (r, r')

-- Relaxation relation
def relaxation_of (p q : ResourceDemand) : Bool 
  := (p.init ≥ q.init) ∧ (p.consumption ≥ q.consumption) 

infix:50 "≽" => relaxation_of

infix:50 "⬝" => mult

--Relaxation is reflexive
theorem relaxation_reflexive (p : ResourceDemand) : p ≽ p := by
  simp [relaxation_of]

--Relaxation is transitive
theorem relaxation_transitive (p q r: ResourceDemand) : p ≽ q → q ≽ r → p ≽ r := by
  simp [relaxation_of]
  intros H_p H_p' H_q H_q'
  apply And.intro
  apply le_trans H_q H_p
  linarith
  
  --Relaxation is antisymmetric
theorem relaxation_antisymmetric (p q :ResourceDemand) : p ≽ q → q ≽ p → p.equal q := by
  simp [relaxation_of]
  intros H_p H_p' H_q H_q'
  apply And.intro
  apply le_antisymm H_q H_p
  linarith

--Example 2.5
#eval (4, 2) ⬝ (5, 0) -- (7, 0)

--Example 2.7
#eval ((4, 2) ≽ (3, 2)) --true

--Example 2.8
#eval ((4, 2) ≽ (5, 4)) --false

--Example 2.9
#eval ((5, 4) ≽ (2, 0)) --false

--Example 2.10
#eval ((4, 2) ≽ (5, 4)) ∧ ((5, 4) ≽ (4, 2)) --false

-- Example 2.14
#eval equal (4, 2) (4, 3) -- false

--(0, 0) is left unit under resource multiplication
theorem left_unit (p : ResourceDemand) : equal (unit ⬝ p)  p := by
   sorry

--(0, 0) is right unit under resource multiplication
theorem right_unit (p: ResourceDemand) : equal (p ⬝ unit) p := by
  sorry

--ResourceDemand multiplication is associative
theorem associative (p q r : ResourceDemand) : equal (p ⬝ (q ⬝ r)) ((p ⬝ q) ⬝ r) := by
  sorry
   

end ResourceDemand

namespace LetTick

inductive Prog :=
  | tick (k : Int)
  | letexp (e_1 e_2 : Prog)

inductive BaseType :=
  | Unit

def RAType := BaseType × ResourceDemand

--Evaluation judgement
inductive Evaluation : Prog → ResourceDemand → Prop :=
  | e_tick_pos (k : Int) (pos : k ≥ 0):
    Evaluation (.tick k) (⟨k, pos⟩, 0) 
  | e_tick_neg (k : Int) (neg: k < 0):
    Evaluation (.tick (abs k)) (⟨(abs k), abs_nonneg k⟩, 0)
  | e_let {e_1 e_2 : Prog} {r_1 r_2 : ResourceDemand} (eval_e_1 : Evaluation e_1 r_1) (eval_e_2 : Evaluation e_2 r_2)
    : Evaluation (.letexp e_1 e_2) (r_1.mult r_2)

--Typing judgement
inductive Typing : Prog → BaseType → ResourceDemand → Prop :=
  | t_tick (k : Int) (t : BaseType) (r : ResourceDemand) (suff_res : r.init ≥ k + r.resid) :
    Typing (.tick k) t r
  | t_let {e_1 e_2 : Prog} {r_1 r_2 : ResourceDemand} {t_1 t_2 : BaseType} (e_1types : Typing e_1 t_1 r_1) (e_2Types : Typing e_2 t_2 r_2) (suff_res : r_1.resid = r_2.init) :
    Typing (.letexp e_1 e_2) t_2 (r_1.init, r_2.resid)

--Proof of soundness. Theorem 3.5
theorem soundness (p : Prog) (r_1 r_2 : ResourceDemand) (t : BaseType) 
  : Evaluation p r_1 → Typing p t r_2 → r_2 ≽ r_1 := by sorry
  
end LetTick

