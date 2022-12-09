import syntax.propLemmas

open set

-- ⊢ [G] (φ ∧ ψ) → [G] (ψ ∧ φ)
def ef_and_switch {agents : Type} {form : Type} [ft : formula form] [fax : formula_ax form] [clf : CLformula agents form]
  {φ ψ : form} {G : set agents} : ax (([G]' (φ ∧' ψ)) →' ([G]' (ψ ∧' φ))) :=
begin
  have hiff : ax ((φ ∧' ψ) ↔' (ψ ∧' φ)), from and_switch,
  have hGiff : ax (([G]' (φ ∧' ψ)) ↔' ([G]' (ψ ∧' φ))), from (Eq _ _ _) hiff,
  exact iff_l hGiff,
end

-- ⊢ φ → ψ ⇒ ⊢ [G]φ → [G]ψ
def derived_monoticity_rule {agents : Type} {form : Type} 
  [ft : formula form] [fax : formula_ax form] [clf : CLformula agents form] {φ ψ : form} {G : set agents} : 
  ax (φ →' ψ) → ax (([G]' φ) →' ([G]' ψ)) :=
begin
  -- Let ⊢ φ → ψ
  intro h,
  -- ⊢ φ → (φ ∧ ψ), from h, by propositional logic
  have h2 : ax (φ →' (φ ∧' ψ)), from imp_and_iden h,
  -- ⊢ ((φ ∧ ψ) → φ), from ⊤ by propositional logic
  have hp5 : ax ((φ ∧' ψ) →' φ), from (p5 _  _),
  -- ⊢ (φ ∧ ψ) ↔ φ, from h2 & hp5, by propositional logic
  have hiff : ax ((φ ∧' ψ) ↔' φ), from
    begin
      rw formula.iffdef,
      exact MP' h2 (MP' hp5 (p4 _  _)),
    end,
  -- ⊢ [G](φ ∧ ψ) ↔ [G]φ, from hiff, by axiom (Eq)
  have heq : ax (([G]'(φ ∧' ψ)) ↔' ([G]' φ)), from (Eq _ _ _) hiff,
  -- ⊢ [G]φ → [G](φ ∧ ψ), from heq, by propositional logic
  have hif : ax (([G]' φ) →' ([G]' (φ ∧' ψ))), from iff_r heq,
  -- ⊢ [G](φ ∧ ψ) → [G](ψ), by axiom (M)
  have hM :  ax (([G]'(φ ∧' ψ)) →' ([G]' ψ)), from cut ef_and_switch (M _ _ _),
  -- ⊢ [G]φ → [G]ψ, from hif & hM, by propositional logic
  exact cut hif hM, 
end

-- ⊢ [N] φ ↔ ⊢ ¬ [∅] ¬φ
def univ_iff_empty {agents : Type} {form : Type} 
  [ft : formula form] [fax : formula_ax form] [clf : CLformula agents form] {φ : form} : 
  ax (([(univ : set agents)]' φ) ↔' (¬' ([(∅ : set agents)]' (¬' φ)))) :=
  -- ⇒
begin
   rw formula.iffdef,
  have hl : ax (([(univ : set agents)]' φ) →' (¬' ([(∅ : set agents)]' (¬' φ)))), from
    begin
      -- Assume [N] φ
      -- Assume by contradiction [∅] ¬φ
      apply by_contra_ax,
      rw ←and_right_imp,
      apply cut (mp _ _  (p5 _  _) (and_switch')),
      -- exact mp _ _  (p5 _  _) (and_switch'),
      apply cut,
      --  [N] (φ ∧ ¬φ), from above by axiom (S) : ([N] φ ∧ [∅] ¬φ) → [N]  ∪ ∅(φ ∧ ¬φ)
      apply (S _ _ _ _),
      simp,
      apply cut,
      simp at *,
      --  [N] (⊥), from above by axiom (Eq)
      have hGiff : ax (([(univ : set agents)]' (φ ∧' (¬' φ))) ↔' ([(univ : set agents)]' ft.bot)), from
        begin
          apply Eq,
          exact contra_equiv_false,
        end,
      exact iff_l hGiff,
      apply mp,
      --Contradiction from axiom (⊥) : ¬[N] ⊥ and above.
      exact contra_imp_imp_false,
      exact Bot _,
    end,
   -- ⇐ by the N axiom
  have hr : ax ((¬' ([(∅ : set agents)]' (¬' φ))) →' ([(univ : set agents)]' φ)), from N _,
  exact MP' hr (MP' hl (p4 _ _)),
end

