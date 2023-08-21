import Resources.Definitions

inductive BaseType :=
  | Unit

def RAType := BaseType × ResourceDemand

inductive Prog :=
  | tick (k : Int) -- tick k
  | letexp (e_1 e_2 : Prog) -- let _ = e_1 in e_2