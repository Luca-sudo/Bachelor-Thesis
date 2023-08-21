--Proof of soundness. Theorem 3.5
theorem soundness (p : Prog) (r_1 r_2 : ResourceDemand) (t : BaseType) 
  : Evaluation p r_1 → Typing p t r_2 → r_2 ≽ r_1 := by sorry