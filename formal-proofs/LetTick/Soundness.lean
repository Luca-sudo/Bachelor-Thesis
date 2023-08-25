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
    . simp; linarith
    . simp[suff_res]
  }
  case _ => {
    cases t_H
    rename_i k suff_res
    apply And.intro
    . simp
    . simp 
  }
  case _ => {
    rename_i e_1 e_2 r_1 r_3 e_1H e_2H 
    apply And.intro
    . simp; 
    . apply [And.intro]

  }


