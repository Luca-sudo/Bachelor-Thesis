import Resources.Definitions
import LetTick.Language

--Evaluation judgement
inductive Evaluation : Prog → ResourceDemand → Prop :=
  | e_tick_pos (k : Nat): --tick with positive resources
    Evaluation (.tick k) (k, 0) 
  | e_tick_neg (k : Int): --tick with negative resources
    Evaluation (.tick (abs k)) (0, Int.natAbs k)
  | e_let {e_1 e_2 : Prog} {r_1 r_2 : ResourceDemand} (eval_e_1 : Evaluation e_1 r_1) (eval_e_2 : Evaluation e_2 r_2)
    : Evaluation (.letexp e_1 e_2) (r_1 ▹ r_2)