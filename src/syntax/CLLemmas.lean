import syntax.propLemmas
open axCL

def ef_and_switch {agents: Type} {φ ψ: formCL agents} {G: set agents}:
-- ⊢ [G] (φ ∧ ψ) → [G] (ψ ∧ φ)
   axCL (([G] (φ & ψ)) ~> [G] (ψ & φ)) :=
   begin
    have hiff: axCL ((φ & ψ) ↔ (ψ & φ)), from @and_switch (formCL agents) formulaCL φ ψ,
    have hGiff: axCL (([G] φ & ψ) ↔ ([G] ψ & φ)), from Eq hiff,
    apply MP Prop5,
    exact hGiff,
   end

def ax_M' (agents: Type) (φ ψ: formCL agents) (G: set agents):
-- ⊢ [G] (φ ∧ ψ) → [G] ψ
   axCL (([G] (φ & ψ)) ~> [G] ψ) :=
begin
   have hab: axCL (([G] φ & ψ) ~> [G] ψ & φ), from ef_and_switch,
   have hbc: axCL (([G] ψ & φ) ~> [G] ψ), from M,
   have habc: axCL (([G] φ & ψ) ~> (([G] ψ & φ) ~> [G] ψ)), from @imp_switch (formCL agents) formulaCL _ _ _ (@imp_if_imp_imp (formCL agents) formulaCL _ _ _ (hbc)),
   exact MP (MP Prop2 habc) hab,
end


def derived_monoticity_rule (agents: Type) {φ ψ: formCL agents} {G: set agents}:
-- ⊢ φ → ψ ⇒ ⊢ [G]φ → [G]ψ
   axCL (φ ~> ψ) → axCL (([G] φ) ~> ([G] ψ)) :=
begin
   -- Let ⊢ φ → ψ
   intro h,
   -- ⊢ φ → (φ ∧ ψ), from h, by propositional logic
   have h2: axCL (φ ~> (φ & ψ)), from @imp_and_iden (formCL agents) formulaCL φ ψ h,
   -- ⊢ ((φ ∧ ψ) → φ), from ⊤ by propositional logic
   have hp5: axCL ((φ & ψ) ~> φ), from Prop5,
   -- ⊢ (φ ∧ ψ) ↔ φ, from h2 & hp5, by propositional logic
   have hiff: axCL ((φ & ψ) ↔ φ), from
   begin
        apply @MP' (formCL agents) formulaCL,
        exact h2,
        apply MP',
        exact hp5,
        exact Prop4,
   end,
   -- ⊢ [G](φ ∧ ψ) ↔ [G]φ, from hiff, by axiom (Eq)
   have heq: axCL (([G](φ & ψ)) ↔ ([G] φ)), from Eq hiff,
   -- ⊢ [G]φ → [G](φ ∧ ψ), from heq, by propositional logic
   have hif: axCL (([G] φ) ~> [G](φ & ψ)), from MP Prop6 heq,
   -- ⊢ [G](φ ∧ ψ) → [G](ψ), by axiom (M)
   have hM:  axCL (([G](φ & ψ)) ~> [G] ψ), from ax_M' agents φ ψ G,
   -- ⊢ [G]φ → [G]ψ, from hif & hM, by propositional logic
   apply @cut (formCL agents) formulaCL, 
   exact hif, 
   exact hM,
end