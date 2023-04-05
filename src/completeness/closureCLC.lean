/-
Authors : Kai Obendrauf
Following the paper "Coalition Logic with Individual, Distributed and Common Knowledge 
by Thomas Ågotnes and Natasha Alechina,

This file contains the filtration closure for CLC, and related lemmas, 
as well as defining subformulas for CLC and how if φ is a subformula of ψ, then cl φ ⊆ cl ψ
-/

import syntax.syntaxCLC
import syntax.propLemmas

local attribute [instance] classical.prop_decidable

open set formCLC axCLC

----------------------------------------------------------
-- Filtration closure cl
----------------------------------------------------------
noncomputable def cl_C {agents : Type} [hN : fintype agents] (G : set (agents)) (φ : formCLC agents) : 
  finset (formCLC agents) :=
finset.image (λ i, 'K (i) ('C G φ)) (to_finset G) ∪ finset.image (λ i, ('¬ 'K (i) ('C G φ))) (to_finset G)

noncomputable def cl {agents : Type} [hN : fintype agents] : 
  formCLC agents → finset (formCLC agents)
|  '⊥      := {'⊥, '¬ '⊥}
| (var n)  := {var n, '¬ var n}
| (φ '→ ψ) := cl φ ∪ cl ψ ∪ (ite (ψ = '⊥) {(imp φ '⊥)} {(imp φ ψ), '¬ (imp φ ψ)} )
| (φ '∧ ψ) := cl φ ∪ cl ψ ∪ {(and φ ψ), '¬ (and φ ψ)}
| ('[G] φ) := cl φ ∪ {('[G] φ), '¬ '[G] φ} ∪ 
              {('C (G) ('[G] φ)), '¬ ('C (G) ('[G] φ))} ∪ cl_C G ('[G] φ)
| ('K i φ) := cl φ ∪ {('K i φ), '¬ ('K i φ)}
| ('C G φ) := cl φ ∪ {('C G φ), '¬ ('C G φ)} ∪ cl_C G φ

----------------------------------------------------------
-- Lemmas about cl
----------------------------------------------------------
@[simp] lemma cl_contains_phi {agents : Type} [hN : fintype agents] (φ : formCLC agents) :
  φ ∈ cl φ :=
begin
  cases φ,
  repeat { unfold cl, simp, },
  { split_ifs,
    repeat { simp[h] at *, }, },
end

lemma cl_closed_single_neg {agents : Type} [hN : fintype agents] 
  (φ x : formCLC agents) (hx : x ∈ cl φ) :
  ∃ ψ, (ψ ∈ cl φ ∧ '⊢ (ψ '↔ ('¬ x))) :=
begin
  induction φ,
  repeat
    { unfold cl at *,
      simp only [finset.union_insert, finset.insert_union, finset.union_assoc, finset.mem_insert, 
                  finset.mem_union, finset.mem_singleton] at hx,
      cases hx,
      { apply exists.intro ('¬ x),
        simp only [hx, finset.mem_insert, finset.mem_union, finset.mem_singleton, eq_self_iff_true, false_or, true_or, or_true, true_and] at *,
        apply @iff_iden (formCLC agents) _ _, }, },
  { apply exists.intro ('⊥),
    simp only [hx, finset.mem_insert, eq_self_iff_true, finset.mem_singleton, or_false, true_and],
    apply MP,
    apply MP,
    apply Prop4,
    exact @dni (formCLC agents) _ _,
    exact @nnn_bot (formCLC agents) _, },
  { { apply exists.intro (var φ),
      simp only [hx, finset.mem_insert, eq_self_iff_true, finset.mem_singleton, 
                  or_false, true_and] at *,
      exact @iff_dni (formCLC agents) _ _, }, },
  { cases hx,
    { specialize φ_ih_φ hx,
      cases φ_ih_φ with ψ hψ,
      apply exists.intro ψ,
      split,
      apply finset.mem_union_left,
      apply finset.mem_union_left,
      exact hψ.1,
      exact hψ.2, },
    cases hx,
    { specialize φ_ih_ψ hx,
      cases φ_ih_ψ with ψ hψ,
      apply exists.intro ψ,
      split,
      apply finset.mem_union_left,
      apply finset.mem_union_right,
      exact hψ.1,
      exact hψ.2, },
      { apply exists.intro (φ_φ '∧ φ_ψ),
        simp only [hx, finset.union_insert, finset.mem_insert, eq_self_iff_true, 
                    true_or, true_and],
        exact @iff_dni (formCLC agents) _ _, }, },
  { unfold cl at *,
    simp only [finset.union_assoc, finset.mem_union] at hx,
    cases hx,
    { specialize φ_ih_φ hx,
      cases φ_ih_φ with ψ hψ,
      apply exists.intro ψ,
      split,
      apply finset.mem_union_left,
      apply finset.mem_union_left,
      exact hψ.1,
      exact hψ.2, },
    cases hx,
    { specialize φ_ih_ψ hx,
      cases φ_ih_ψ with ψ hψ,
      apply exists.intro ψ,
      split,
      apply finset.mem_union_left,
      apply finset.mem_union_right,
      exact hψ.1,
      exact hψ.2, },
    { split_ifs at hx,
      { simp only [h, eq_self_iff_true, if_true, finset.union_assoc, finset.mem_union, 
                    finset.mem_singleton] at *,
        simp only [hx],
        apply exists.intro (φ_φ),
        split,
        apply or.intro_left,
        exact cl_contains_phi φ_φ,
        exact @iff_dni (formCLC agents) _ _, },
      { simp only [h, if_false, finset.union_insert, finset.union_assoc, finset.mem_insert, 
                    finset.mem_union, finset.mem_singleton, not_false_iff] at *,
        cases hx,
        { apply exists.intro ('¬ (φ_φ '→ φ_ψ)),
          simp only [hx, eq_self_iff_true, or_true, true_and],
          exact @iff_iden (formCLC agents) _ _, },
        { apply exists.intro (φ_φ '→ φ_ψ),
          simp only [hx, eq_self_iff_true, true_or, true_and],
          exact @iff_dni (formCLC agents) _ _, }, }, }, },
  { cases hx,
    {  apply exists.intro ('¬ ('C φ_G '[φ_G] φ_φ)),
      simp only [hx, finset.mem_insert, finset.mem_union, finset.mem_singleton, eq_self_iff_true, 
                  true_or, or_true, true_and],
      exact @iff_iden (formCLC agents) _ _, },
    cases hx,
    { specialize φ_ih hx,
      cases φ_ih with ψ hψ,
      apply exists.intro ψ,
      split,
      apply finset.mem_union_left,
      apply finset.mem_union_left,
      apply finset.mem_union_left,
      exact hψ.1,
      exact hψ.2, },
    cases hx,
    { apply exists.intro ('[φ_G] φ_φ),
      simp only [hx, finset.union_insert, finset.mem_insert, eq_self_iff_true, finset.mem_union, 
                  false_or, true_or, true_and],
      exact @iff_dni (formCLC agents) _ _, },
    cases hx,
    { apply exists.intro ('C φ_G '[φ_G] φ_φ),
        simp only [hx, finset.union_insert, finset.mem_insert, eq_self_iff_true, finset.mem_union, 
                    false_or, true_or, true_and],
        exact @iff_dni (formCLC agents) _ _, },
    { unfold cl_C at *,
      simp only [finset.mem_union, finset.mem_image, mem_to_finset, exists_prop] at hx,
      cases hx, 
      { cases hx with i hi,
        apply exists.intro ('¬ 'K i ('C φ_G ('[φ_G]φ_φ))),
        simp only [hi.left, ←hi.right, finset.mem_union, eq_self_iff_true, finset.mem_image, 
                    mem_to_finset, and_true, exists_prop, exists_eq_right, or_true, true_and],
        exact @iff_iden (formCLC agents) _ _, },
      { cases hx with i hi,
        apply exists.intro ('K i ('C φ_G ('[φ_G]φ_φ))),
        simp only [hi.left, ←hi.right, finset.mem_union, finset.mem_image, mem_to_finset, 
                    eq_self_iff_true, and_true, exists_prop, exists_eq_right, exists_false, 
                    or_false, or_true, true_and],
        exact @iff_dni (formCLC agents) _ _, }, }, }, 
  { cases hx,  
    { specialize φ_ih hx,
      cases φ_ih with ψ hψ,
      apply exists.intro ψ,
      split,
      apply finset.mem_union_left,
      exact hψ.1,
      exact hψ.2, },
    { apply exists.intro ('K φ_a φ_φ),
      simp only [hx, finset.union_insert, finset.mem_insert, eq_self_iff_true, true_or, true_and],
      exact @iff_dni (formCLC agents) _ _, }, },
  { cases hx,
    { specialize φ_ih hx,
      cases φ_ih with ψ hψ,
      apply exists.intro ψ,
      split,
      apply finset.mem_union_left,
      apply finset.mem_union_left,
      exact hψ.1,
      exact hψ.2, },
    cases hx,
    { apply exists.intro (('C φ_G (φ_φ))),
      simp only [hx, finset.union_insert, finset.mem_insert, eq_self_iff_true, finset.mem_union, 
                  true_or, true_and],
      exact @iff_dni (formCLC agents) _ _, },
    { unfold cl_C at *,
      simp only [finset.mem_union, finset.mem_image, mem_to_finset, exists_prop] at hx,
      cases hx,
      { cases hx with i hi,
        apply exists.intro ('¬ 'K i ('C φ_G φ_φ)),
        simp only [hi.left, ←hi.right, finset.mem_union, eq_self_iff_true, finset.mem_image, 
                    mem_to_finset, and_true, exists_prop, exists_eq_right, or_true, true_and],
        exact @iff_iden (formCLC agents) _ _, },
      { cases hx with i hi,
        apply exists.intro ('K i ('C φ_G φ_φ)),
        simp only [hi.left, ←hi.right, finset.mem_union, finset.mem_image, mem_to_finset, 
                    eq_self_iff_true, and_true, exists_prop, exists_eq_right, exists_false, 
                    or_false, or_true, true_and],
        exact @iff_dni (formCLC agents) _ _, }, }, },
end

----------------------------------------------------------
-- Subformulas in CLC
----------------------------------------------------------
inductive subformula {agents : Type} : formCLC agents → formCLC agents → Prop
| refl            {φ}     : subformula φ φ
| trans           {φ ψ χ} : subformula φ ψ → subformula ψ χ → subformula φ χ
| and_left        {φ ψ}   : subformula φ (φ '∧ ψ)
| and_right       {φ ψ}   : subformula ψ (φ '∧ ψ)
| imp_left        {φ ψ}   : subformula φ (φ '→ ψ)
| imp_right       {φ ψ}   : subformula ψ (φ '→ ψ)
| effectivity {G} {φ}     : subformula φ ('[G] φ)
| knows       {i} {φ}     : subformula φ ('K i φ)
| common_know {G} {φ}     : subformula φ ('C G φ)

----------------------------------------------------------
-- if φ is a subformula of ψ, then cl φ ⊆ cl ψ
----------------------------------------------------------
lemma subformula.cl_subset_and_left {agents : Type} [ha : nonempty agents] [hN : fintype agents]
  {φ ψ : formCLC agents} : cl φ ⊆ cl (φ '∧ ψ) :=
begin
  intros x h,
  induction φ,
  repeat
  { simp only [cl, finset.insert_union, finset.union_insert, finset.union_assoc, finset.mem_insert,
                finset.mem_union, finset.mem_singleton] at *,
    repeat {cases h, simp only [h, eq_self_iff_true, and_self, false_or, true_or, or_true],},
    {simp only [h, eq_self_iff_true, and_self, true_or, false_or, or_true], }, },
end

lemma subformula.cl_subset_and_right {agents : Type} [ha : nonempty agents] [hN : fintype agents]
  {φ ψ : formCLC agents} : cl ψ ⊆ cl (φ '∧ ψ) :=
begin
  intros x h,
  induction φ,
  repeat
  { simp [cl] at *,
    repeat {cases h, simp [h],},
    {simp [h], }, },
end

lemma subformula.cl_subset_imp_left {agents : Type} [ha : nonempty agents] [hN : fintype agents]
  {φ ψ : formCLC agents} : cl φ ⊆ cl (φ '→ ψ) :=
begin
  intros x h,
  induction φ,
  repeat
  { simp [cl] at *,
    repeat {cases h, simp [h],},
    {simp [h], }, },
end

lemma subformula.cl_subset_imp_right {agents : Type} [ha : nonempty agents] [hN : fintype agents]
  {φ ψ : formCLC agents} : cl ψ ⊆ cl (φ '→ ψ) :=
begin
  intros x h,
  induction φ,
  repeat
  { simp [cl] at *,
    repeat {cases h, simp [h],},
    {simp [h], }, },
end

lemma subformula.cl_subset_effectivity {agents : Type} [ha : nonempty agents] [hN : fintype agents]
  {φ : formCLC agents} {G : set (agents)} : cl φ ⊆ cl ('[G] φ) :=
begin
  intros x h,
  induction φ,
  repeat
  { simp [cl] at *,
    repeat {cases h, simp [h],},
    {simp [h], }, },
end

lemma subformula.cl_subset_knows {agents : Type} [ha : nonempty agents] [hN : fintype agents]
  {φ : formCLC agents} {i : agents}  : cl φ ⊆ cl ('K i φ) :=
begin
  intros x h,
  induction φ,
  repeat
  { simp [cl] at *,
    repeat {cases h, simp [h],},
    {simp [h], }, },
end

lemma subformula.cl_subset_common_know {agents : Type} [ha : nonempty agents] [hN : fintype agents]
  {φ : formCLC agents} {G : set (agents)} : cl φ ⊆ cl ('C G φ) :=
begin
  intros x h,
  induction φ,
  repeat
  { simp [cl] at *,
    repeat {cases h, simp [h],},
    {simp [h], }, },
end

lemma subformula.cl_subset {agents : Type} [ha : nonempty agents] [hN : fintype agents]
  {φ ψ : formCLC agents} (h : subformula φ ψ) : cl φ ⊆ cl ψ :=
begin
  induction h,
  { exact finset.subset.rfl, },
  { exact finset.subset.trans h_ih_ᾰ h_ih_ᾰ_1, },
  { exact subformula.cl_subset_and_left, },
  { exact subformula.cl_subset_and_right, },
  { exact subformula.cl_subset_imp_left, },
  { exact subformula.cl_subset_imp_right, },
  { exact subformula.cl_subset_effectivity, },
  { exact subformula.cl_subset_knows, },
  { exact subformula.cl_subset_common_know, },
end

lemma subformula.mem_cl {agents : Type} [ha : nonempty agents] [hN : fintype agents]
  {φ ψ : formCLC agents} (h : subformula φ ψ) : φ ∈ cl ψ :=
h.cl_subset (cl_contains_phi φ)


