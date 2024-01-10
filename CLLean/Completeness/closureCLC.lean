/-
Authors: Kai Obendrauf
Following the paper "Coalition Logic with Individual, Distributed and Common Knowledge
by Thomas Ågotnes and Natasha Alechina

This file contains the filtration closure for CLC, and related lemmas
as well as defining subformulas for CLC and related lemmas, including the fact that
if ψ ∈ cl φ and subformula χ ψ, then we must have χ ∈ cl φ .
-/

import CLLean.Syntax.syntaxCLC
import CLLean.Syntax.propLemmas

open Classical Set axCLC

----------------------------------------------------------
-- Filtration closure cl
----------------------------------------------------------
noncomputable def cl_C {agents : Type} [hN : Fintype agents] (G : Set (agents))
  (φ : formCLC agents) : Finset (formCLC agents) :=
Finset.image (λ i => _K (i) (_C G φ)) (toFinset G) ∪
  Finset.image (λ i => (_¬ _K (i) (_C G φ))) (toFinset G)

noncomputable def cl {agents : Type} [hN : Fintype agents] :
  formCLC agents → Finset (formCLC agents)
|  _⊥              => {_⊥, _¬ _⊥}
| (formCLC.var n)  => {formCLC.var n, _¬ (formCLC.var n), _⊥, _¬ _⊥}
| (φ _→ ψ)         => cl φ ∪ cl ψ ∪ (ite (ψ = _⊥) {(φ _→ _⊥)} {(φ _→ ψ), _¬ (φ _→ ψ)})
| (φ _∧ ψ)         => cl φ ∪ cl ψ ∪ {(φ _∧ ψ), _¬ (φ _∧ ψ)}
| (_[G] φ)         => cl φ ∪ {(_[G] φ), _¬ _[G] φ} ∪
                        {(_C (G) (_[G] φ)), _¬ (_C (G) (_[G] φ))} ∪ cl_C G (_[G] φ)
| (formCLC.K i φ) => cl φ ∪ {(_K i φ), _¬ (_K i φ)}
| (_C G φ)        => cl φ ∪ {(_C G φ), _¬ (_C G φ)} ∪ cl_C G φ

----------------------------------------------------------
-- Lemmas about cl
----------------------------------------------------------
@[simp] lemma cl_contains_phi {agents : Type} [hN : Fintype agents] (φ : formCLC agents) :
  φ ∈ cl φ := by
  cases' φ
  any_goals
    simp_all only [cl, Finset.union_insert, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_false,
    eq_self_iff_true, and_self, or_true, true_or, Finset.mem_union, Finset.union_assoc]
  · unfold cl
    simp only [Finset.mem_singleton, formCLC.imp.injEq, Finset.union_assoc, Finset.mem_union]
    split_ifs with h
    simp only [Finset.mem_singleton, formCLC.imp.injEq, h, and_false, Finset.mem_insert,
      or_false, or_true]
    simp only [Finset.mem_singleton, formCLC.imp.injEq, Finset.mem_insert, true_or, or_true]



@[simp] lemma cl_contains_bot {agents : Type} [hN : Fintype agents] (φ : formCLC agents) :
  _⊥ ∈ cl φ := by
  induction' φ with _ _ _ ih_φ ih_ψ _ _ ih_φ ih_ψ _ _ ih _ _ ih _ _ ih
  any_goals simp [cl]
  any_goals simp [ih]
  any_goals simp [ih_φ, ih_ψ]

lemma cl_C_contains_KC {agents : Type} [hN : Fintype agents] {φ ψ : formCLC agents}
  {G : Set agents} {i : agents} (hi : i ∈ G) (h : _C G ψ ∈ cl φ) : _K i (_C G ψ) ∈ cl φ := by
  induction' φ with _ _ _ ih_φ ih_ψ _ _ ih_φ ih_ψ _ _ ih _ _ ih _ _ ih
  any_goals
    simp only [cl, Finset.mem_insert, Finset.mem_singleton, or_self] at *
  · simp only [cl, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, or_false] at *
    cases' h with h h
    · exact Or.inl (ih_φ h)
    · exact Or.inr (ih_ψ h)
  · simp only [cl, Finset.union_assoc, Finset.mem_union] at *
    cases' h with h h
    · exact Or.inl (ih_φ h)
    cases' h with h h
    · simp only [ih_ψ h, true_or, or_true]
    split_ifs at h
    · simp only [Finset.mem_singleton] at h
    · simp only [Finset.mem_insert, Finset.mem_singleton, or_self] at h
  · simp only [Finset.mem_singleton, Finset.union_insert, Finset.mem_union, or_false,
    Finset.insert_union, Finset.union_assoc, or_self, Finset.mem_insert, false_or,
    formCLC.C.injEq] at *
    cases' h with h h
    · rw [h.1] at hi
      simp [h.1, h.2, cl_C, hi, Finset.mem_union, Finset.mem_image, mem_toFinset, eq_self_iff_true,
                and_true, exists_prop, exists_eq_right, exists_false, or_false, or_true]
    cases' h with h h
    · exact Or.inl (ih h)
    simp only [cl_C, Finset.mem_union, Finset.mem_image, mem_toFinset, and_false, exists_false,
      or_self] at h
  · simp only [Finset.mem_singleton, Finset.union_insert, Finset.mem_union, or_false,
      Finset.mem_insert, false_or, formCLC.K.injEq] at *
    exact Or.inr (ih h)
  · simp only [Finset.mem_singleton, Finset.union_insert, Finset.mem_union, or_false, cl_C,
      Finset.insert_union, Finset.union_assoc, Finset.mem_image, mem_toFinset, and_false,
      exists_false, or_self, Finset.mem_insert, formCLC.C.injEq, formCLC.K.injEq, false_or] at *
    cases' h with h h
    · rw [h.1] at hi
      simp only [h.1, h.2, and_true, exists_eq_right, hi, or_true]
    · exact Or.inl (ih h)

lemma cl_closed_single_neg {agents : Type} [hN : Fintype agents]
  (φ x : formCLC agents) (hx : x ∈ cl φ) :
  ∃ ψ, (ψ ∈ cl φ ∧ _⊢ (ψ _↔ (_¬ x))) := by
  induction' φ with _ _ _ ih_φ ih_ψ _ _ ih_φ ih_ψ _ _ ih _ _ ih _ _ ih
  repeat'
    · unfold cl at *
      simp only [Finset.union_insert, Finset.insert_union, Finset.union_assoc, Finset.mem_insert,
                  Finset.mem_union, Finset.mem_singleton] at hx
      cases' hx with hx hx
      · apply Exists.intro (_¬ x)
        simp only [hx, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, eq_self_iff_true
                    false_or, true_or, or_true, true_and] at *
        exact iff_iden --apply @iff_iden (formCLC agents) _ _
  · apply Exists.intro (_⊥)
    -- simp only [hx, Finset.mem_insert, eq_self_iff_true, Finset.mem_singleton, or_false, true_and]
    apply MP
    apply MP
    apply Prop4
    exact @dni (formCLC agents) _ _
    exact @nnn_bot (formCLC agents) _
  · cases hx
   · apply Exists.intro (var φ)
      simp only [hx, Finset.mem_insert, eq_self_iff_true, Finset.mem_singleton
                  or_false, true_and] at *
      exact @iff_dni (formCLC agents) _ _
    cases hx
    · apply Exists.intro ('⊤)
      simp only [hx, Finset.mem_insert, eq_self_iff_true, false_and, Finset.mem_singleton
                  false_or, true_and]
      apply @iff_iden (formCLC agents) _ _
    · apply Exists.intro (_⊥)
      simp only [hx, Finset.mem_insert, eq_self_iff_true, Finset.mem_singleton, or_false
                  false_or, true_and]
      apply MP
    apply MP
    apply Prop4
    exact @dni (formCLC agents) _ _
    exact @nnn_bot (formCLC agents) _
  · cases hx
    · specialize φ_ih_φ hx
      cases φ_ih_φ with ψ hψ
      apply Exists.intro ψ
      split
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact hψ.1
      exact hψ.2
    cases hx
    · specialize φ_ih_ψ hx
      cases φ_ih_ψ with ψ hψ
      apply Exists.intro ψ
      split
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact hψ.1
      exact hψ.2
      · apply Exists.intro (φ_φ _∧ φ_ψ)
        simp only [hx, Finset.union_insert, Finset.mem_insert, eq_self_iff_true
                    true_or, true_and]
        exact @iff_dni (formCLC agents) _ _
  · unfold cl at *
    simp only [Finset.union_assoc, Finset.mem_union] at hx
    cases hx
    · specialize φ_ih_φ hx
      cases φ_ih_φ with ψ hψ
      apply Exists.intro ψ
      split
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact hψ.1
      exact hψ.2
    cases hx
    · specialize φ_ih_ψ hx
      cases φ_ih_ψ with ψ hψ
      apply Exists.intro ψ
      split
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact hψ.1
      exact hψ.2
    · split_ifs at hx
      · simp only [h, eq_self_iff_true, if_true, Finset.union_assoc, Finset.mem_union
                    Finset.mem_singleton] at *
        simp only [hx]
        apply Exists.intro (φ_φ)
        split
        apply or.intro_left
        exact cl_contains_phi φ_φ
        exact @iff_dni (formCLC agents) _ _
      · simp only [h, if_false, Finset.union_insert, Finset.union_assoc, Finset.mem_insert
                    Finset.mem_union, Finset.mem_singleton, not_false_iff] at *
        cases hx
        · apply Exists.intro (_¬ (φ_φ _→ φ_ψ))
          simp only [hx, eq_self_iff_true, or_true, true_and]
          exact @iff_iden (formCLC agents) _ _
        · apply Exists.intro (φ_φ _→ φ_ψ)
          simp only [hx, eq_self_iff_true, true_or, true_and]
          exact @iff_dni (formCLC agents) _ _
  · cases hx
    · apply Exists.intro (_¬ (_C φ_G '[φ_G] φ_φ))
      simp only [hx, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, eq_self_iff_true
                  true_or, or_true, true_and]
      exact @iff_iden (formCLC agents) _ _
    cases hx
    · specialize φ_ih hx
      cases φ_ih with ψ hψ
      apply Exists.intro ψ
      split
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact hψ.1
      exact hψ.2
    cases hx
    · apply Exists.intro ('[φ_G] φ_φ)
      simp only [hx, Finset.union_insert, Finset.mem_insert, eq_self_iff_true, Finset.mem_union
                  false_or, true_or, true_and]
      exact @iff_dni (formCLC agents) _ _
    cases hx
    · apply Exists.intro (_C φ_G '[φ_G] φ_φ)
        simp only [hx, Finset.union_insert, Finset.mem_insert, eq_self_iff_true, Finset.mem_union
                    false_or, true_or, true_and]
        exact @iff_dni (formCLC agents) _ _
    · unfold cl_C at *
      simp only [Finset.mem_union, Finset.mem_image, mem_to_finset, exists_prop] at hx
      cases hx
      · cases hx with i hi
        apply Exists.intro (_¬ _K i (_C φ_G ('[φ_G]φ_φ)))
        simp only [hi.left, ←hi.right, Finset.mem_union, eq_self_iff_true, Finset.mem_image
                    mem_to_finset, and_true, exists_prop, exists_eq_right, or_true, true_and]
        exact @iff_iden (formCLC agents) _ _
      · cases hx with i hi
        apply Exists.intro (_K i (_C φ_G ('[φ_G]φ_φ)))
        simp only [hi.left, ←hi.right, Finset.mem_union, Finset.mem_image, mem_to_finset
                    eq_self_iff_true, and_true, exists_prop, exists_eq_right, exists_false
                    or_false, or_true, true_and]
        exact @iff_dni (formCLC agents) _ _
  · cases hx
    · specialize φ_ih hx
      cases φ_ih with ψ hψ
      apply Exists.intro ψ
      split
      apply Finset.mem_union_left
      exact hψ.1
      exact hψ.2
    · apply Exists.intro (_K φ_a φ_φ)
      simp only [hx, Finset.union_insert, Finset.mem_insert, eq_self_iff_true, true_or, true_and]
      exact @iff_dni (formCLC agents) _ _
  · cases hx
    · specialize φ_ih hx
      cases φ_ih with ψ hψ
      apply Exists.intro ψ
      split
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact hψ.1
      exact hψ.2
    cases hx
    · apply Exists.intro ((_C φ_G (φ_φ)))
      simp only [hx, Finset.union_insert, Finset.mem_insert, eq_self_iff_true, Finset.mem_union
                  true_or, true_and]
      exact @iff_dni (formCLC agents) _ _
    · unfold cl_C at *
      simp only [Finset.mem_union, Finset.mem_image, mem_to_finset, exists_prop] at hx
      cases hx
      · cases hx with i hi
        apply Exists.intro (_¬ _K i (_C φ_G φ_φ))
        simp only [hi.left, ←hi.right, Finset.mem_union, eq_self_iff_true, Finset.mem_image
                    mem_to_finset, and_true, exists_prop, exists_eq_right, or_true, true_and]
        exact @iff_iden (formCLC agents) _ _
      · cases hx with i hi
        apply Exists.intro (_K i (_C φ_G φ_φ))
        simp only [hi.left, ←hi.right, Finset.mem_union, Finset.mem_image, mem_to_finset
                    eq_self_iff_true, and_true, exists_prop, exists_eq_right, exists_false
                    or_false, or_true, true_and]
        exact @iff_dni (formCLC agents) _ _

----------------------------------------------------------
-- Subformulas in CLC
----------------------------------------------------------
inductive subformula {agents : Type} : formCLC agents → formCLC agents → Prop
| refl            {φ}     : subformula φ φ
| trans           {φ ψ χ} : subformula φ ψ → subformula ψ χ → subformula φ χ
| and_left        {φ ψ}   : subformula φ (φ _∧ ψ)
| and_right       {φ ψ}   : subformula ψ (φ _∧ ψ)
| imp_left        {φ ψ}   : subformula φ (φ _→ ψ)
| imp_right       {φ ψ}   : subformula ψ (φ _→ ψ)
| effectivity {G} {φ}     : subformula φ ('[G] φ)
| knows       {i} {φ}     : subformula φ (_K i φ)
| common_know {G} {φ}     : subformula φ (_C G φ)

----------------------------------------------------------
-- if φ is a subformula of ψ, then cl φ ⊆ cl ψ
----------------------------------------------------------
lemma subformula.cl_subset_and_left {agents : Type} [hN : Fintype agents]
  {φ ψ : formCLC agents} : cl φ ⊆ cl (φ _∧ ψ) := by
  intro x h
  induction φ
  repeat
  { simp only [cl, Finset.insert_union, Finset.union_insert, Finset.union_assoc, Finset.mem_insert
                Finset.mem_union, Finset.mem_singleton] at *
    repeat {cases h, simp only [h, eq_self_iff_true, and_self, false_or, true_or, or_true],}
    {simp only [h, eq_self_iff_true, and_self, true_or, false_or, or_true]

lemma subformula.cl_subset_and_right {agents : Type} [hN : Fintype agents]
  {φ ψ : formCLC agents} : cl ψ ⊆ cl (φ _∧ ψ) := by
  intro x h
  induction φ
  repeat
  { simp [cl] at *
    repeat {cases h, simp [h],}
    {simp [h]

lemma subformula.cl_subset_imp_left {agents : Type} [hN : Fintype agents]
  {φ ψ : formCLC agents} : cl φ ⊆ cl (φ _→ ψ) := by
  intro x h
  induction φ
  repeat
  { simp [cl] at *
    repeat {cases h, simp [h],}
    {simp [h]

lemma subformula.cl_subset_imp_right {agents : Type} [hN : Fintype agents]
  {φ ψ : formCLC agents} : cl ψ ⊆ cl (φ _→ ψ) := by
  intro x h
  induction φ
  repeat
  { simp [cl] at *
    repeat {cases h, simp [h],}
    {simp [h]

lemma subformula.cl_subset_effectivity {agents : Type} [hN : Fintype agents]
  {φ : formCLC agents} {G : Set (agents)} : cl φ ⊆ cl ('[G] φ) := by
  intro x h
  induction φ
  repeat
  { simp [cl] at *
    repeat {cases h, simp [h],}
    {simp [h]

lemma subformula.cl_subset_knows {agents : Type} [hN : Fintype agents]
  {φ : formCLC agents} {i : agents}  : cl φ ⊆ cl (_K i φ) := by
  intro x h
  induction φ
  repeat
  { simp [cl] at *
    repeat {cases h, simp [h],}
    {simp [h]

lemma subformula.cl_subset_common_know {agents : Type} [hN : Fintype agents]
  {φ : formCLC agents} {G : Set (agents)} : cl φ ⊆ cl (_C G φ) := by
  intro x h
  induction φ
  repeat
  { simp [cl] at *
    repeat {cases h, simp [h],}
    {simp [h]

lemma subformula.cl_subset {agents : Type} [hN : Fintype agents]
  {φ ψ : formCLC agents} (h : subformula φ ψ) : cl φ ⊆ cl ψ := by
  induction h with _ _ _ _ _ h ih ih'
  { exact Finset.subset.rfl
  { exact Finset.subset.trans ih ih'
  { exact subformula.cl_subset_and_left
  { exact subformula.cl_subset_and_right
  { exact subformula.cl_subset_imp_left
  { exact subformula.cl_subset_imp_right
  { exact subformula.cl_subset_effectivity
  { exact subformula.cl_subset_knows
  { exact subformula.cl_subset_common_know

lemma subformula.mem_cl {agents : Type} [hN : Fintype agents]
  {φ ψ : formCLC agents} (h : subformula φ ψ) : φ ∈ cl ψ :=
h.cl_subset (cl_contains_phi φ)

lemma subformula.in_cl_sub {agents : Type} [hN : Fintype agents]
  {φ ψ χ : formCLC agents} (hcl : ψ ∈ cl φ) (hsub : subformula χ ψ) : χ ∈ cl φ := by
  induction hsub with _ _ _ _ hsub1 hsub2 hih1 hih2
  { exact hcl
  { exact hih1 (hih2 hcl)
  all_goals
  { induction φ
    repeat
    { simp only [cl, Finset.mem_insert, Finset.mem_singleton, or_self] at hcl
      cases hcl
  any_goals
  { simp only [cl, cl_C, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton
                Finset.mem_image, exists_false, or_false, false_or] at hcl
      cases hcl
  repeat { apply or.elim hcl, all_goals { intro hcl
  any_goals { split_ifs at hcl
  any_goals { rw hcl.1 at *, rw hcl.2 at *
  any_goals { rw h at *
  any_goals { simp only [cl, Finset.union_assoc, Finset.mem_insert, Finset.mem_union
                          Finset.mem_singleton, false_or, Finset.mem_insert, Finset.mem_singleton
                          or_self, or_false, eq_self_iff_true, and_self, or_true
                          true_or] at hcl
  any_goals { simp only [cl_C, Finset.mem_union, Finset.mem_image, exists_false, or_self
                          or_false] at hcl
  repeat { apply or.elim hcl, all_goals { intro hcl
  any_goals { rw hcl.1 at *, rw hcl.2 at *
  any_goals { rw h at *
  any_goals { solve1 { by_contra, exact hcl
  any_goals { simp only [cl, φ_ih_φ hcl, Finset.mem_union, true_or, or_true]
  any_goals { simp only [cl, φ_ih_ψ hcl, Finset.mem_union, true_or, or_true]
  any_goals { simp only [cl, Finset.mem_union, cl_contains_phi, true_or, or_true]
  any_goals { simp only [φ_ih hcl, true_or]
  any_goals { simp only [if_true, Finset.mem_insert, Finset.mem_singleton, or_false
                          eq_self_iff_true, and_self, or_true, true_or]
  any_goals { simp only [hcl.1, hcl.2, eq_self_iff_true, cl_contains_phi, and_self
                          or_false, or_true, true_or]
  any_goals { simp only [h, if_false, Finset.mem_insert, eq_self_iff_true, and_self
                          Finset.mem_singleton, and_false, or_false, or_true]
  any_goals { obtain ⟨i, ⟨hi, hcl⟩⟩ := hcl
              rw ←hcl.1 at *, rw ←hcl.2 at *
              simp only [cl_C, or_false, Finset.mem_union, Finset.mem_image, mem_to_finset
                          eq_self_iff_true, and_true, exists_prop, exists_eq_right, exists_false
                          mem_to_finset.mp hi, or_true]
  any_goals { simp only [cl_contains_bot, or_self, true_or]
