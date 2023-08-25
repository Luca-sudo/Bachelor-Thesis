import Resources.Definitions
import LetTick.Language
import LetTick.Typing
import LetTick.Evaluation


open ResourceDemand
--Proof of soundness. Theorem 3.5
theorem soundness (p : Prog) (r_1 r_2 : ResourceDemand) (t : BaseType) 
  : Evaluation p r_1 → Typing p t r_2 → r_2 ≽ r_1 := by 
  intros e_H t_H
  simp[relaxation_of];
  cases e_H 
  cases t_H
  rename_i k suff_res
  case _ => {
    apply And.intro
    . linarith
    . simp 
      have h (c: Nat) (a b: Nat) : a ≤ b ↔ a + c ≤ b + c
      {
        apply Iff.intro
        . intros H_n; linarith
        . intros H_n; linarith
      }
      rw[h r_2.snd]
      rw[Nat.sub_add_eq_max]
      rw[Nat.max_eq_left]
      
  }
  case _ => {
    cases t_H
    rename_i k suff_res
    apply And.intro
    . simp
    . simp 
  }
  case _ => {
    cases t_H 
    . rename_i r_1 r_2 t H_r t_1 t_2
      simp; apply And.intro
      . rw[← H_r]

  }


