import Resources.Definitions

open ResourceDemand

--(0, 0) is left unit under sequencing
theorem ResourceDemand.one_mul (p : ResourceDemand) : ((0,0) ▹ p) = p := by
  simp

--(0, 0) is right unit under sequencing
theorem ResourceDemand.mul_one (p: ResourceDemand) : (p ▹ (0, 0)) = p := by
  simp

instance : Mul ResourceDemand where
  mul       := ResourceDemand.sequence

--sequencing is associative
theorem ResourceDemand.associative (p q r : ResourceDemand) : (p ▹ q ▹ r) = (p ▹ (q ▹ r)) := by
  
-- ResourceDemand forms monoid
instance : Monoid ResourceDemand where
  one_mul   := ResourceDemand.one_mul
  mul_one   := ResourceDemand.mul_one
  mul_assoc := ResourceDemand.associative
