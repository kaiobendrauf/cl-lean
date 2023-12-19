/-
Authors: Kai Obendrauf
Following the paper "Coalition Logic with Individual, Distributed and Common Knowledge 
by Thomas Ågotnes and Natasha Alechina,

This file contains the filtration closure for CLK, and related lemmas, 
as well as defining subformulas for CLK and related lemmas, including the fact that
if ψ ∈ cl φ and subformula χ ψ, then we must have χ ∈ cl φ .
-/

import syntax.syntaxCLK
import syntax.propLemmas

local attribute [instance] classical.prop_decidable

open set formCLK axCLK

----------------------------------------------------------
-- Filtration closure cl
----------------------------------------------------------
noncomputable def cl {agents : Type} : 
  formCLK agents → finset (formCLK agents)
|  '⊥      := {'⊥, '¬ '⊥}
| (var n)  := {var n, '¬ (var n), '⊥, '¬ '⊥}
| (φ '→ ψ) := cl φ ∪ cl ψ ∪ (ite (ψ = '⊥) {(imp φ '⊥)} {(imp φ ψ), '¬ (imp φ ψ)} )
| (φ '∧ ψ) := cl φ ∪ cl ψ ∪ {(and φ ψ), '¬ (and φ ψ)}
| ('[G] φ) := cl φ ∪ {('[G] φ), '¬ '[G] φ} 
| ('K i φ) := cl φ ∪ {('K i φ), '¬ ('K i φ)}

----------------------------------------------------------
-- Lemmas about cl
----------------------------------------------------------
@[simp] lemma cl_contains_phi {agents : Type} (φ : formCLK agents) :
  φ ∈ cl φ :=
begin
  cases φ,
  repeat { unfold cl, simp, },
  { split_ifs,
    repeat { simp[h] at *, }, },
end

@[simp] lemma cl_contains_bot {agents : Type} (φ : formCLK agents) :
  '⊥ ∈ cl φ :=
begin
  induction φ,
  repeat { unfold cl, simp, },
  repeat { simp [φ_ih], },
  repeat { simp [φ_ih_φ, φ_ih_ψ], },
end

lemma cl_closed_single_neg {agents : Type} (φ x : formCLK agents) (hx : x ∈ cl φ) :
  ∃ ψ, (ψ ∈ cl φ ∧ '⊢ (ψ '↔ ('¬ x))) :=
begin
  induction φ,
  repeat
    { unfold cl at *,
      simp only [finset.union_insert, finset.insert_union, finset.union_assoc, finset.mem_insert, 
                  finset.mem_union, finset.mem_singleton] at hx,
      cases hx,
      { apply exists.intro ('¬ x),
        simp only [hx, finset.mem_insert, finset.mem_union, finset.mem_singleton, eq_self_iff_true,
                    false_or, true_or, or_true, true_and] at *,
        apply @iff_iden (formCLK agents) _ _, }, },
  { apply exists.intro ('⊥),
    simp only [hx, finset.mem_insert, eq_self_iff_true, finset.mem_singleton, or_false, true_and],
    apply MP,
    apply MP,
    apply Prop4,
    exact @dni (formCLK agents) _ _,
    exact @nnn_bot (formCLK agents) _, },
  { cases hx,
   { apply exists.intro (var φ),
      simp only [hx, finset.mem_insert, eq_self_iff_true, finset.mem_singleton, 
                  or_false, true_and] at *,
      exact @iff_dni (formCLK agents) _ _, }, 
    cases hx,
    { apply exists.intro ('⊤),
      simp only [hx, finset.mem_insert, eq_self_iff_true, false_and, 
                 finset.mem_singleton, false_or, true_and],
      apply @iff_iden (formCLK agents) _ _, },
    { apply exists.intro ('⊥),
      simp only [hx, finset.mem_insert, eq_self_iff_true, finset.mem_singleton, or_false, 
                 false_or, true_and],
      apply MP,
    apply MP,
    apply Prop4,
    exact @dni (formCLK agents) _ _,
    exact @nnn_bot (formCLK agents) _, }, },
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
        exact @iff_dni (formCLK agents) _ _, }, },
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
        exact @iff_dni (formCLK agents) _ _, },
      { simp only [h, if_false, finset.union_insert, finset.union_assoc, finset.mem_insert, 
                    finset.mem_union, finset.mem_singleton, not_false_iff] at *,
        cases hx,
        { apply exists.intro ('¬ (φ_φ '→ φ_ψ)),
          simp only [hx, eq_self_iff_true, or_true, true_and],
          exact @iff_iden (formCLK agents) _ _, },
        { apply exists.intro (φ_φ '→ φ_ψ),
          simp only [hx, eq_self_iff_true, true_or, true_and],
          exact @iff_dni (formCLK agents) _ _, }, }, }, },
  { cases hx,
    { specialize φ_ih hx,
      cases φ_ih with ψ hψ,
      apply exists.intro ψ,
      split,
      { apply finset.mem_union_left,
        exact hψ.1, },
      { exact hψ.2, }, },
    { apply exists.intro ('[φ_G] φ_φ),
      simp only [hx, finset.union_insert, finset.mem_insert, eq_self_iff_true, finset.mem_union,
                  false_or, true_or, true_and],
      exact @iff_dni (formCLK agents) _ _, }, },
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
      exact @iff_dni (formCLK agents) _ _, }, },
end

----------------------------------------------------------
-- Subformulas in CLK
----------------------------------------------------------
inductive subformula {agents : Type} : formCLK agents → formCLK agents → Prop
| refl            {φ}     : subformula φ φ
| trans           {φ ψ χ} : subformula φ ψ → subformula ψ χ → subformula φ χ
| and_left        {φ ψ}   : subformula φ (φ '∧ ψ)
| and_right       {φ ψ}   : subformula ψ (φ '∧ ψ)
| imp_left        {φ ψ}   : subformula φ (φ '→ ψ)
| imp_right       {φ ψ}   : subformula ψ (φ '→ ψ)
| effectivity {G} {φ}     : subformula φ ('[G] φ)
| knows       {i} {φ}     : subformula φ ('K i φ)

----------------------------------------------------------
-- if φ is a subformula of ψ, then cl φ ⊆ cl ψ
----------------------------------------------------------
lemma subformula.cl_subset_and_left {agents : Type}
  {φ ψ : formCLK agents} : cl φ ⊆ cl (φ '∧ ψ) :=
begin
  intros x h,
  induction φ,
  repeat
  { simp only [cl, finset.insert_union, finset.union_insert, finset.union_assoc, finset.mem_insert,
                finset.mem_union, finset.mem_singleton] at *,
    repeat {cases h, simp only [h, eq_self_iff_true, and_self, false_or, true_or, or_true],},
    {simp only [h, eq_self_iff_true, and_self, true_or, false_or, or_true], }, },
end

lemma subformula.cl_subset_and_right {agents : Type}
  {φ ψ : formCLK agents} : cl ψ ⊆ cl (φ '∧ ψ) :=
begin
  intros x h,
  induction φ,
  repeat
  { simp [cl] at *,
    repeat {cases h, simp [h],},
    {simp [h], }, },
end

lemma subformula.cl_subset_imp_left {agents : Type}
  {φ ψ : formCLK agents} : cl φ ⊆ cl (φ '→ ψ) :=
begin
  intros x h,
  induction φ,
  repeat
  { simp [cl] at *,
    repeat {cases h, simp [h],},
    {simp [h], }, },
end

lemma subformula.cl_subset_imp_right {agents : Type}
  {φ ψ : formCLK agents} : cl ψ ⊆ cl (φ '→ ψ) :=
begin
  intros x h,
  induction φ,
  repeat
  { simp [cl] at *,
    repeat {cases h, simp [h],},
    {simp [h], }, },
end

lemma subformula.cl_subset_effectivity {agents : Type}
  {φ : formCLK agents} {G : set (agents)} : cl φ ⊆ cl ('[G] φ) :=
begin
  intros x h,
  induction φ,
  repeat
  { simp [cl] at *,
    repeat {cases h, simp [h],},
    {simp [h], }, },
end

lemma subformula.cl_subset_knows {agents : Type}
  {φ : formCLK agents} {i : agents}  : cl φ ⊆ cl ('K i φ) :=
begin
  intros x h,
  induction φ,
  repeat
  { simp [cl] at *,
    repeat {cases h, simp [h],},
    {simp [h], }, },
end

lemma subformula.cl_subset {agents : Type}
  {φ ψ : formCLK agents} (h : subformula φ ψ) : cl φ ⊆ cl ψ :=
begin
  induction h with _ _ _ _ _ h ih ih',
  { exact finset.subset.rfl, },
  { exact finset.subset.trans ih ih', },
  { exact subformula.cl_subset_and_left, },
  { exact subformula.cl_subset_and_right, },
  { exact subformula.cl_subset_imp_left, },
  { exact subformula.cl_subset_imp_right, },
  { exact subformula.cl_subset_effectivity, },
  { exact subformula.cl_subset_knows, },
end

lemma subformula.mem_cl {agents : Type}
  {φ ψ : formCLK agents} (h : subformula φ ψ) : φ ∈ cl ψ :=
h.cl_subset (cl_contains_phi φ)

lemma subformula.in_cl_sub {agents : Type}
  {φ ψ χ : formCLK agents} (hcl : ψ ∈ cl φ) (hsub : subformula χ ψ) : χ ∈ cl φ :=
begin
  induction hsub with _ _ _ _ hsub1 hsub2 hih1 hih2,
  { exact hcl, },
  { exact hih1 (hih2 hcl), },
  all_goals
  { induction φ,
    repeat 
    { simp only [cl, finset.mem_insert, finset.mem_singleton, or_self] at hcl,
      cases hcl, }, },
  any_goals
  { simp only [cl, finset.mem_insert, finset.mem_union, finset.mem_singleton, finset.mem_image, 
                  exists_false, or_false, false_or] at hcl,
      cases hcl, },
  repeat { apply or.elim hcl, all_goals { intro hcl, }, }, 
  any_goals { split_ifs at hcl, }, 
  any_goals { rw hcl.1 at *, rw hcl.2 at *, },
  any_goals { rw h at *, },
  any_goals { simp only [cl, finset.union_assoc, finset.mem_insert, finset.mem_union, 
                          finset.mem_singleton, false_or, finset.mem_insert, finset.mem_singleton,
                          or_self, or_false, eq_self_iff_true, and_self, or_true, true_or] 
              at hcl, },
  repeat { apply or.elim hcl, all_goals { intro hcl, }, },
  any_goals { rw hcl.1 at *, rw hcl.2 at *, },
  any_goals { rw h at *, },
  any_goals { solve1 { by_contradiction, exact hcl, }, },
  any_goals { simp only [cl, φ_ih_φ hcl, finset.mem_union, true_or, or_true], },
  any_goals { simp only [cl, φ_ih_ψ hcl, finset.mem_union, true_or, or_true], },
  any_goals { simp only [cl, finset.mem_union, cl_contains_phi, true_or, or_true], },
  any_goals { simp only [φ_ih hcl, true_or], },
  any_goals { simp only [if_true, finset.mem_insert, finset.mem_singleton, or_false, 
                          eq_self_iff_true, and_self, or_true, true_or], }, 
  any_goals { simp only [hcl.1, hcl.2, eq_self_iff_true, cl_contains_phi, and_self, 
                          or_false, or_true, true_or], },
  any_goals { simp only [h, if_false, finset.mem_insert, eq_self_iff_true, and_self, 
                          finset.mem_singleton, and_false, or_false, or_true], },
  any_goals { simp only [cl_contains_bot, or_self, true_or], },
end
