/-
Authors: Kai Obendrauf

This file contains proofs for a variety of lemmas for CL.
-/

import CLLean.Syntax.propLemmas

open Set Logic

-- ⊢ [G] (φ ∧ ψ) → [G] (ψ ∧ φ)
lemma ef_and_switch {agents form : Type} [Pformula_ax form] [CLformula agents form]
  {φ ψ : form} {G : Set agents} : ⊢' ((['G] (φ ∧' ψ)) →' (['G] (ψ ∧' φ))) :=
iff_l ((Eq _ _ _) and_switch)

-- ⊢ φ → ψ ⇒ ⊢ [G]φ → [G]ψ
lemma derived_monoticity_rule {agents form : Type}
  [pf : Pformula_ax form] [clf : CLformula agents form] {φ ψ : form} {G : Set agents} :
  ⊢' (φ →' ψ) → ⊢' ((['G] φ) →' (['G] ψ)) := by
  -- Let ⊢ φ → ψ
  intro h
  -- ⊢ φ → (φ ∧ ψ):= h, by propositional logic
  have h2 : ⊢' (φ →' (φ ∧' ψ)):= imp_and_iden h
  -- ⊢ ((φ ∧ ψ) → φ):= ⊤ by propositional logic
  have hp5 : ⊢' ((φ ∧' ψ) →' φ):= (p5 _  _)
  -- ⊢ (φ ∧ ψ) ↔ φ:= h2 & hp5, by propositional logic
  have hiff : ⊢' ((φ ∧' ψ) ↔' φ):= MP' h2 (MP' hp5 (p4 _  _))
  -- ⊢ [G](φ ∧ ψ) ↔ [G]φ:= hiff, by axiom (Eq)
  have heq : ⊢' ((['G](φ ∧' ψ)) ↔' ['G] φ):= (Eq _ _ _) hiff
  -- ⊢ [G]φ → [G](φ ∧ ψ):= heq, by propositional logic
  have hif : ⊢' ((['G] φ) →' (['G] (φ ∧' ψ))):= iff_r heq
  -- ⊢ [G](φ ∧ ψ) → [G](ψ), by axiom (M)
  have hM :  ⊢' ((['G](φ ∧' ψ)) →' ['G] ψ):= cut ef_and_switch (M _ _ _)
  -- ⊢ [G]φ → [G]ψ:= hif & hM, by propositional logic
  exact cut hif hM

-- ⊢ [N] φ ↔ ⊢ ¬ [∅] ¬φ
lemma univ_iff_empty {agents form : Type} [pf : Pformula_ax form] [clf : CLformula agents form]
  {φ : form} : ⊢' ((['(univ : Set agents)] φ) ↔' (¬' (['(∅ : Set agents)] (¬' φ)))) := by
  -- ⇒ by
  apply ax_and.mpr
  apply And.intro
  -- ⇒
  · -- Assume [N] φ
    -- Assume by contradiction [∅] ¬φ
    apply by_contra_ax
    rw [←and_right_imp]
    apply cut (mp _ _  (p5 _  _) (and_switch))
    apply cut
    --  [N] (φ ∧ ¬φ):= above by axiom (S) : ([N] φ ∧ [∅] ¬φ) → [N]  ∪ ∅(φ ∧ ¬φ)
    apply (S _ _ _ _)
    simp
    apply cut
    simp at *
    --  [N] (⊥):= above by axiom (Eq)
    have hGiff : ⊢' ((['(univ : Set agents)] (φ ∧' (¬' φ))) ↔' (['(univ : Set agents)] ⊥')):= by
        apply clf.Eq
        exact contra_equiv_false
    exact iff_l hGiff
    apply mp
    --Contradiction from axiom (⊥) : ¬[N] ⊥ and above.
    exact contra_imp_imp_false
    exact Bot _
  -- ⇒
  · exact N _
