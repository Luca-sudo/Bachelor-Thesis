import Resources.Definitions

open ResourceDemand

--(0, 0) is left unit under sequencing
theorem left_unit (p : ResourceDemand) : ((0, 0) ▹ p) = (p.init, p.resid) := by
  simp[init]; simp[resid]


--(0, 0) is right unit under sequencing
theorem right_unit (p: ResourceDemand) : (p ▹ (0, 0)) = p := by
  simp[init]; simp[resid]

--sequencing is associative
theorem associative (p q r : ResourceDemand) : (p ▹ (q ▹ r)) = ((p ▹ q) ▹ r) := by
  simp[init]; simp[resid];