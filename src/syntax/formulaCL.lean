import syntax.axiomsCL syntax.formula
variables {agents : Type}

instance formulaCL: formula (formCL agents) :=

{ bot := formCL.bot,
  and := λ φ ψ, φ & ψ,
  imp := formCL.imp,
  not := λ φ, ¬ φ,
  iff := λ φ ψ, φ ↔ ψ,
  top := ⊤,
  notdef := by simp,
  iffdef := by simp,
  topdef := by simp,

  ax  := axCL,
  p1 := @axCL.Prop1 agents,
  p2 := @axCL.Prop2 agents,
  p3 := @axCL.Prop3 agents,
  p4 := @axCL.Prop4 agents,
  p5 := @axCL.Prop5 agents,
  p6 := @axCL.Prop6 agents,
  p7 := @axCL.Prop7 agents,
  mp := @axCL.MP agents, }


instance CLformulaCL: CLformula agents (formCL agents) :=
{ 
  eff:= λ G φ, [G] φ,
  Bot:= @axCL.Bot agents,
  Top:= @axCL.Top agents,
  N  := @axCL.N agents,
  M  := @axCL.M agents,
  S  := @axCL.S agents,
  Eq := @axCL.Eq agents, }