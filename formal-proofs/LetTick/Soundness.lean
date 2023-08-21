import Resources.Definitions
import LetTick.Language
import LetTick.Typing
import LetTick.Evaluation

open ResourceDemand
--Proof of soundness. Theorem 3.5
theorem soundness (p : Prog) (r_1 r_2 : ResourceDemand) (t : BaseType) 
  : Evaluation p r_1 → Typing p t r_2 → r_2 ≽ r_1 := by 
  intros e_H t_H
  cases p 
  cases e_H
  cases t_H
  rename_i k rel
  simp[relaxation_of]; simp[init]; simp[resid]