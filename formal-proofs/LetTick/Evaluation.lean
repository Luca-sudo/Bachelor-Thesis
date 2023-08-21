--Evaluation judgement
inductive Evaluation : Prog → ResourceDemand → Prop :=
  | e_tick_pos (k : Int) (pos : k ≥ 0):
    Evaluation (.tick k) (⟨k, pos⟩, 0) 
  | e_tick_neg (k : Int) (neg: k < 0):
    Evaluation (.tick (abs k)) (⟨(abs k), abs_nonneg k⟩, 0)
  | e_let {e_1 e_2 : Prog} {r_1 r_2 : ResourceDemand} (eval_e_1 : Evaluation e_1 r_1) (eval_e_2 : Evaluation e_2 r_2)
    : Evaluation (.letexp e_1 e_2) (r_1 ▹ r_2)