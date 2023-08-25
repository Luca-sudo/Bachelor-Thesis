import Resources.Definitions

open ResourceDemand

--(0, 0) is left unit under sequencing
theorem left_unit (p : ResourceDemand) : ((0, 0) ▹ (p.1, p.2)) = (p.1, p.2) := by
  simp


--(0, 0) is right unit under sequencing
theorem right_unit (p: ResourceDemand) : ((p.1, p.2) ▹ (0, 0)) = (p.1, p.2) := by
  simp

--sequencing is associative
theorem associative (p q r : ResourceDemand) : (p ▹ (q ▹ r)) = ((p ▹ q) ▹ r) := by
  simp
  . cases p.snd
    . cases q.fst
      . cases q.snd
        . cases r.fst
          . simp
          . simp
        . cases r.fst
          . simp
          . sorry
      . cases q.snd
        . cases r.fst
          .simp
          .simp[Nat.add_assoc]
        . cases r.fst
          . simp
          . sorry
    . cases q.fst
      . cases q.snd
        . cases r.fst
          .simp
          .simp
        . cases r.fst
          . simp[Nat.add_assoc]
          . sorry
      . cases q.snd
        . cases r.fst
          . sorry
          . sorry
        . cases r.fst
          . sorry
          . sorry
  