import Resources.Definitions

inductive BaseType :=
  | Unit

def RAType := BaseType × ResourceDemand

inductive Prog :=
  | tick (k : Int)
  | letexp (e_1 e_2 : Prog)