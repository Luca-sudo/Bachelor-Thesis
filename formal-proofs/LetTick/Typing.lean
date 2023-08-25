import Resources.Definitions
import LetTick.Language

--Typing judgement
inductive Typing : Prog → BaseType → ResourceDemand → Prop :=
  | t_tick (k : Int) (t : BaseType) (r : ResourceDemand) (suff_res : k + r.snd ≤ r.fst) :
    Typing (.tick k) t r
  | t_let {e_1 e_2 : Prog} {r_1 r_2 : ResourceDemand} {t_1 t_2 : BaseType} (e_1types : Typing e_1 t_1 r_1) (e_2Types : Typing e_2 t_2 r_2) (suff_res : r_1.snd = r_2.fst) :
    Typing (.letexp e_1 e_2) t_2 (r_1.fst, r_2.snd)
