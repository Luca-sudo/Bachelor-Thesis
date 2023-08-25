import Resources.Definitions

open ResourceDemand

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
theorem relaxation_antisymmetric (p q :ResourceDemand) 
  : p ≽ q → q ≽ p → p.1 = q.1 ∧ p.2 = q.2 := by
  simp [relaxation_of]
  intros H_p H_p' H_q H_q'
  apply And.intro
  linarith
  linarith