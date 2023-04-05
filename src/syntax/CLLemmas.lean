import syntax.propLemmas

open set

-- ⊢ [G] (φ ∧ ψ) → [G] (ψ ∧ φ)
def ef_and_switch {agents form : Type} [pf : Pformula_ax form] [clf : CLformula agents form]
  {φ ψ : form} {G : set agents} : ⊢' ((['G] (φ ∧' ψ)) →' (['G] (ψ ∧' φ))) :=
iff_l ((Eq _ _ _) and_switch)

-- ⊢ φ → ψ ⇒ ⊢ [G]φ → [G]ψ
def derived_monoticity_rule {agents form : Type} 
  [pf : Pformula_ax form] [clf : CLformula agents form] {φ ψ : form} {G : set agents} :
  ⊢' (φ →' ψ) → ⊢' ((['G] φ) →' (['G] ψ)) :=
begin
  -- Let ⊢ φ → ψ
  intro h,
  -- ⊢ φ → (φ ∧ ψ), from h, by propositional logic
  have h2 : ⊢' (φ →' (φ ∧' ψ)), from imp_and_iden h,
  -- ⊢ ((φ ∧ ψ) → φ), from ⊤ by propositional logic
  have hp5 : ⊢' ((φ ∧' ψ) →' φ), from (p5 _  _),
  -- ⊢ (φ ∧ ψ) ↔ φ, from h2 & hp5, by propositional logic
  have hiff : ⊢' ((φ ∧' ψ) ↔' φ), from MP' h2 (MP' hp5 (p4 _  _)),
  -- ⊢ [G](φ ∧ ψ) ↔ [G]φ, from hiff, by axiom (Eq)
  have heq : ⊢' ((['G](φ ∧' ψ)) ↔' ['G] φ), from (Eq _ _ _) hiff,
  -- ⊢ [G]φ → [G](φ ∧ ψ), from heq, by propositional logic
  have hif : ⊢' ((['G] φ) →' (['G] (φ ∧' ψ))), from iff_r heq,
  -- ⊢ [G](φ ∧ ψ) → [G](ψ), by axiom (M)
  have hM :  ⊢' ((['G](φ ∧' ψ)) →' ['G] ψ), from cut ef_and_switch (M _ _ _),
  -- ⊢ [G]φ → [G]ψ, from hif & hM, by propositional logic
  exact cut hif hM, 
end

-- ⊢ [N] φ ↔ ⊢ ¬ [∅] ¬φ
def univ_iff_empty {agents form : Type} [pf : Pformula_ax form] [clf : CLformula agents form] 
  {φ : form} : ⊢' ((['(univ : set agents)] φ) ↔' (¬' (['(∅ : set agents)] (¬' φ)))) :=
  -- ⇒
begin
  refine ax_and.mpr _, 
  split,
  -- ⇒ 
  { -- Assume [N] φ
    -- Assume by contradiction [∅] ¬φ
    apply by_contra_ax,
    rw ←and_right_imp,
    apply cut (mp _ _  (p5 _  _) (and_switch)),
    apply cut,
    --  [N] (φ ∧ ¬φ), from above by axiom (S) : ([N] φ ∧ [∅] ¬φ) → [N]  ∪ ∅(φ ∧ ¬φ)
    apply (S _ _ _ _),
    simp,
    apply cut,
    simp at *,
    --  [N] (⊥), from above by axiom (Eq)
    have hGiff : ⊢' ((['(univ : set agents)] (φ ∧' (¬' φ))) ↔' (['(univ : set agents)] ⊥')), from
      begin
        apply Eq,
        exact contra_equiv_false,
      end,
    exact iff_l hGiff,
    apply mp,
    --Contradiction from axiom (⊥) : ¬[N] ⊥ and above.
    exact contra_imp_imp_false,
    exact Bot _,
  },
  -- ⇒ 
  { exact N _, },
end

