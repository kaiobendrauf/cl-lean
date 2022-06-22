import syntax.propLemmas
open axCL

def ef_and_switch {agents: Type} {φ ψ: formCL agents} {G: set agents}:
   axCL (([G]' φ & ψ) ~> [G]' ψ & φ) :=
   begin
    have hiff: axCL ((φ & ψ) ↔ (ψ & φ)), from @and_switch (formCL agents) formulaCL φ ψ,
    have hGiff: axCL (([G]' φ & ψ) ↔ ([G]' ψ & φ)), from Eq hiff,
    apply MP Prop5,
    exact hGiff,
   end

def ax_M' (agents: Type) (φ ψ: formCL agents) (G: set agents):
   axCL (([G]' (φ & ψ)) ~> [G]' ψ) :=
begin
   have hab: axCL (([G]' φ & ψ) ~> [G]' ψ & φ), from ef_and_switch,
   have hbc: axCL (([G]' ψ & φ) ~> [G]' ψ), from M,
   have habc: axCL (([G]' φ & ψ) ~> (([G]' ψ & φ) ~> [G]' ψ)), from @imp_switch (formCL agents) formulaCL _ _ _ (@imp_if_imp_imp (formCL agents) formulaCL _ _ _ (hbc)),
   exact MP (MP Prop2 habc) hab,
end


def derived_monoticity_rule (agents: Type) {φ ψ: formCL agents} {G: set agents}:
   axCL (φ ~> ψ) → axCL (([G]' φ) ~> ([G]' ψ)) :=
begin
   intro h,
   have h2: axCL (φ ~> (φ & ψ)), from @imp_and (formCL agents) formulaCL φ ψ h,
   have hp5: axCL ((φ & ψ) ~> φ), from Prop5,
   have hiff: axCL ((φ & ψ) ↔ φ), from
   begin
        apply @MP' (formCL agents) formulaCL,
        exact h2,
        apply MP',
        exact hp5,
        exact Prop4,
   end,
   have heq: axCL (([G]'(φ & ψ)) ↔ ([G]' φ)), from Eq hiff,
   have hif: axCL (([G]' φ) ~> [G]'(φ & ψ)), from MP Prop6 heq,
   have hM:  axCL (([G]'(φ & ψ)) ~> [G]' ψ), from ax_M' agents φ ψ G,
   apply @cut (formCL agents) formulaCL, 
   exact hif, 
   exact hM,
end