/-
Authors: Kai Obendrauf
Adapted from the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley, 
who's work followed the textbook "Dynamic Epistemic Logic" by 
Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

This file defines proofs from a set, consistency and maximal consistency.
It proves sever lemmas related to the above definitions, including Lindenbaums Lemma.
-/

import CLLean.Syntax.formula 
import CLLean.Syntax.propLemmas

import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Order.Zorn

open set 

----------------------------------------------------------
-- Set Proofs
----------------------------------------------------------

def set_proves {form : Type} [pf : Pformula_ax form] (Γ : set (form)) (φ : form) :=
∃ (φs : list (form)), (∀ ψ ∈ φs, ψ ∈ Γ) ∧ ⊢' ((finite_conjunction φs) →' φ)

-- φ ∈ Γ ⇒ Γ proves ⊥
lemma proves_of_mem {form : Type} [pf : Pformula_ax form] 
  (Γ : set (form)) {φ : form} (h : φ ∈ Γ) : 
  set_proves Γ φ :=
begin
  apply exists.intro [φ],
  split,
  { simp, exact h, },
  { simp[finite_conjunction],
    apply imp_and_l iden, },
end

-- we always have a set proof of a tautology
lemma always_true_of_true {form : Type} [pf : Pformula_ax form] (φ : form) (h :  ⊢' φ)
  (Γ : set (form)) : set_proves Γ φ :=
⟨[], by rintro x ⟨⟩, mp _ _ (p1 _ _) h⟩


----------------------------------------------------------
-- Consistency Definitions
----------------------------------------------------------

-- Consistency for an arbitrary set of formulas Γ
def ax_consistent {form : Type} [pf : Pformula_ax form] (Γ : set form) : Prop :=
¬ set_proves Γ ⊥'

-- Γ is maximally ax-consistent
def max_ax_consistent {form : Type} [pf : Pformula_ax form] (Γ : set form) : Prop := 
(ax_consistent Γ) ∧ (∀ Γ', Γ ⊂ Γ' → ¬ (ax_consistent Γ'))

----------------------------------------------------------
-- Lemmas about (Maximal) Consistency 
----------------------------------------------------------

-- If Γ proves ⊥ it must be inconsistent
lemma not_ax_consistent_of_proves_bot {form : Type} [pf : Pformula_ax form] 
  {Γ : set form} (h : set_proves Γ ⊥') : ¬ (ax_consistent Γ) :=
begin
  simp only [ax_consistent, not_not],
  exact h,
end

-- consistent Γ ⇒ ⊥ ∉ Γ
lemma bot_not_mem_of_ax_consistent {form : Type} [pf : Pformula_ax form] 
 (Γ : set form) (hΓ : ax_consistent Γ) : (⊥') ∉ Γ :=
λ h, not_ax_consistent_of_proves_bot (proves_of_mem Γ h) hΓ

-- Γ ∪ {φ} proves ψ ⇒  Γ proves φ → ψ 
lemma set_proof_imp {form : Type} [pf : Pformula_ax form] 
  {Γ : set form} {φ ψ : form} (h : set_proves (Γ ∪ {φ}) (ψ)) :
  set_proves Γ (φ →' ψ) := 
begin
  cases h with φs h,
  cases h with hΓ h, 
  revert ψ, 
  induction φs with χ φs ih,
  { intros ψ hψ,
    apply exists.intro [],
    split,
    { intros χ hχ,
      by_contradiction,
      apply list.not_mem_nil _ hχ, },
    { apply imp_if_imp_imp,
      exact hψ, }, },
  { intros ψ hψ,
    simp [set_proves] at *,
    cases ih hΓ.right (and_right_imp.mp hψ) with φs' ih,
    cases ih with ihl ihr,
    cases hΓ.left,
    { rw h at *,
      apply exists.intro (φs'),
      split,
      { exact ihl, },
      { exact imp_imp_iff_imp.mp ihr, }, }, 
    { apply exists.intro (χ :: φs'),
      split,
      { intros θ hθ,
        cases hθ,
        { rw hθ,
          exact h, },
        { exact ihl θ hθ, }, },
      { apply imp_conj_imp_imp.mpr,
        exact imp_shift.mp ihr, }, },},
end

-- if Γ ∪ {φ} is inconsistent then Γ must prove ¬ φ
lemma inconsistent_prove_neg {form : Type} [pf : Pformula_ax form] 
  {Γ : set form} {φ : form} (hnax : ¬ ax_consistent (Γ ∪ {φ})) :
  set_proves Γ (¬' φ) :=
begin
  simp only [ax_consistent, not_not] at hnax, 
  exact set_proof_imp hnax,
end

-- maximally consistent Γ ⇒ φ ∈ Γ ∨ (¬ φ) ∈ Γ
lemma max_ax_contains_phi_or_neg  {form : Type} [pf : Pformula_ax form] 
  {Γ : set form} (hΓ : max_ax_consistent Γ) (φ : form) :
  φ ∈ Γ ∨ (¬' φ) ∈ Γ :=
begin
  rw or_iff_not_and_not,
  by_contradiction hf,
  have h1 : set_proves Γ (¬' φ), from
    begin
      apply inconsistent_prove_neg, 
      apply hΓ.right (Γ ∪ {φ}),
      rw union_singleton,
      exact (ssubset_insert hf.left),
    end,
  have h2 : set_proves Γ (¬' (¬' φ)), from
    begin
      apply inconsistent_prove_neg, 
      apply hΓ.right (Γ ∪ {¬' φ}),
      rw union_singleton,
      exact (ssubset_insert hf.right),
    end,
  cases h1 with φs h1,
  cases h2 with φs' h2,
  apply hΓ.left,
  apply exists.intro (φs ++ φs'),
  split,
  { intros ψ hψ,
    rw list.mem_append at hψ, 
    cases hψ,
    {exact h1.left ψ hψ, },
    {exact h2.left ψ hψ, }, },
  { apply cut (mp _ _ (p6 _ _) fin_conj_append),
    apply cut (imp_and_and_imp (mp _ _ (mp _ _ (p4 _ _) h1.right) h2.right)),
    exact mp _ _ (p5 _ _) (contra_equiv_false), },
end

-- maximally consistent Γ ⇔ φ ∈ Γ xor (¬ φ) ∈ Γ
lemma max_ax_contains_phi_xor_neg {form : Type} [pf : Pformula_ax form] 
  {Γ : set form} (hax : ax_consistent Γ) :
  max_ax_consistent Γ ↔ ∀ φ, (φ ∈ Γ ∨ (¬' φ) ∈ Γ) ∧ ¬(φ ∈ Γ ∧ (¬' φ) ∈ Γ) :=
begin 
  split,
  { intros hΓ φ,
    split,
    { exact max_ax_contains_phi_or_neg hΓ φ, },
    { intro hf,
      apply hΓ.left,
      apply exists.intro [φ, ¬' φ],
      split,
      { intros ψ hψ,
        simp at hψ,
        cases hψ,
        { rw hψ,
         exact hf.left, },
        { rw hψ,
         exact hf.right, }, },
      { exact fin_conj_simp φ, }, }, },
  { intros h,
    split,
    { exact hax, },
    { intros Γ' hΓ hax,
      have hΓ : Γ ⊆ Γ' ∧ ¬ Γ' ⊆ Γ, from hΓ,
      rw set.not_subset at hΓ,
      cases hΓ.right with φ hφ,
      cases hφ with hφΓ' hφnΓ,
      specialize h φ,
      cases h.left with hφΓ hnφΓ,
      { exact hφnΓ hφΓ, },
      { apply hax,
        apply exists.intro [φ, ¬'φ],
        split,
        { simp only [list.mem_cons_iff, list.mem_singleton, forall_eq_or_imp, forall_eq],
          split,
          { exact hφΓ' },
          { exact mem_of_subset_of_mem hΓ.left hnφΓ, }, },
        { apply fin_conj_simp, }, }, }, }, 
end

-- Motivation: a lot of places assume `¬ ⊢' ⊥'` so it's worth trying to reduce these assumptions.
lemma ax_consistent.not_ax_bot {form : Type} [pf : Pformula_ax form] 
  {s : set form} (h : ax_consistent s) : 
  ¬ ⊢' (⊥' : form) :=
begin
  intro hf,
  unfold ax_consistent set_proves at h,
  apply h,
  apply exists.intro [],
  split,
  { simp only [list.not_mem_nil, forall_false_left, implies_true_iff], },
  { simp only [finite_conjunction_nil, ax_not_bot_imp],
    exact hf, },
end

/-- An empty set of formulas is consistent iff the theory is consistent. -/
@[simp] lemma ax_consistent_empty {form : Type} [pf : Pformula_ax form] :
  ax_consistent (∅ : set form) ↔ ¬ ⊢' (⊥' : form) :=
begin
  split; intro h,
  { exact h.not_ax_bot },
  { intro hf,
    apply not_ax_consistent_of_proves_bot hf,
    simp [ax_consistent, set_proves],
    intro φs,
    cases φs with φ φs,
    { simp only [list.not_mem_nil, forall_false_left, implies_true_iff, finite_conjunction_nil, 
                  ax_not_bot_imp, forall_true_left],
      exact h, },
    { simp only [list.mem_cons_iff, forall_eq_or_imp, false_and, forall_false_left], }, },
end

/-- A singleton set is consistent iff the theory is consistent and the formula is not disprovable.
-/
-- Motivation: `comphelper` seemed to be slightly too specific, this is a more general form I found
@[simp] lemma ax_consistent_singleton {form : Type} [pf : Pformula_ax form] {φ : form} :
  ax_consistent ({φ} : set form) ↔ ¬ ⊢' (¬' φ) :=
begin
  split,
  { intros h,
    simp only [ax_consistent, set_proves, mem_singleton_iff, not_exists, not_and] at h,
    have := h [φ] (by simp),
    simp only [finite_conjunction_cons, finite_conjunction_nil]
      at ⊢ this,
    exact mt (ax_iff_mp (ax_imp_congr_left ax_and_top_iff)).2 this },
  { intros hφ hφs,
    cases hφs with φs hφs,
    apply hφ,
    apply cut (fin_conj_repeat hφs.left),
    exact hφs.right, },
end

----------------------------------------------------------
-- Lindenbaum 
----------------------------------------------------------

/-- Let `c` be a nonempty chain of sets and `s` a finite set, such that each
element of `s` is in some set of `c`. Then there is a `t ∈ c` that contains the
entirety of `s`.

In other words, finitary properties are preserved under unions.

This is useful in combination with Zorn's lemma, if you take `⋃₀ c` as the
upper bound of a chain of sets.
-/
lemma exists_subset_of_finite_of_subset_sUnion_of_chain {α : Type*}
  (c : set (set α)) (hc : is_chain (⊆) c)
  (t : set α) (ht : t ∈ c)
  (s : set α) (hs : s.finite) (hsc : s ⊆ ⋃₀ c) : ∃ t ∈ c, s ⊆ t :=
begin
  revert hsc,
  refine hs.induction_on _ _,
  { exact λ _, ⟨t, ht, set.empty_subset _⟩ },
  rintros x s hxs hs ih hsc,
  obtain ⟨⟨u, huc, hxu⟩, hsc⟩ := set.insert_subset.mp hsc,
  obtain ⟨t, htc, hst⟩ := ih hsc,
  cases hc.total huc htc with h h,
  { exact ⟨t, htc, insert_subset.mpr ⟨h hxu, hst⟩⟩ },
  { exact ⟨u, huc, insert_subset.mpr ⟨hxu, hst.trans h⟩⟩ }
end

/-- The union of a chain of consistent sets is consistent. -/
lemma ax_consistent_sUnion_chain {form : Type} [pf : Pformula_ax form]
  {c : set (set form)} (c_cons : ∀ Γ ∈ c, ax_consistent Γ) (c_chain : is_chain (⊆) c)
  (Γ : set form) (hΓ : Γ ∈ c) :
  ax_consistent (⋃₀ c) :=
begin
  -- For consistency, we have to show any finite subset of axioms L does not imply falsum.
  unfold ax_consistent set_proves at ⊢ c_cons,
  simp,
  intros L L_subset,
  simp at *,
  -- Since L is finite, it is completely contained in some element of the chain,
  -- and each element of the chain is consistent, therefore L does not imply falsum.
  obtain ⟨Γ, hΓc, hΓ⟩ := exists_subset_of_finite_of_subset_sUnion_of_chain c c_chain
    Γ hΓ { x | x ∈ L } _ _,
  { exact c_cons Γ hΓc L hΓ },
  { letI := classical.dec_eq form,
    convert set.finite_mem_finset L.to_finset,
    ext; simp, },
  { simp,
    apply L_subset, }
end

lemma lindenbaum {form : Type} [pf : Pformula_ax form] 
  {Γ : set form} (hax : ax_consistent Γ) :
  ∃ Γ', max_ax_consistent Γ' ∧ Γ ⊆ Γ' :=
begin
  -- By Zorn's lemma, it suffices to show that the union of a chain of consistent sets of formulas
  -- is itself consistent.
  obtain ⟨Γ', consistent, subset, max⟩ := zorn_nonempty_preorder₀ (ax_consistent) _ Γ hax,
  { refine ⟨Γ', ⟨consistent, _⟩, subset⟩,
    intros Δ hΓΔ hconsΔ,
    rw ← set.lt_eq_ssubset at hΓΔ,
    exact hΓΔ.not_le (max Δ hconsΔ hΓΔ.le) },
  { intros c c_cons c_chain Γ hΓ,
    exact ⟨⋃₀ c, ax_consistent_sUnion_chain c_cons c_chain Γ hΓ, λ _, set.subset_sUnion_of_mem⟩, },
end

lemma listempty {form : Type} {φs : list form} {Γ : set form} : 
  (∀ φ ∈ φs, φ ∈ Γ) → Γ = ∅ → φs = [] := 
begin
  intros h1 h2,
  by_contradiction h3,
  have h4 := list.length_pos_of_ne_nil,
  have h5 := list.exists_mem_of_length_pos,
  cases h5 (h4 h3) with φ h5,
  exact absurd (h1 φ h5) (set.eq_empty_iff_forall_not_mem.mp h2 φ)
end

lemma max_ax_exists {form : Type} [pf : Pformula_ax form] 
 (hnprfalseCL : ¬  ⊢' (⊥' : form)) : ∃ Γ : set form, max_ax_consistent Γ :=
begin
  have h1 : ax_consistent ∅, from
  begin
    intro h1, 
    unfold set_proves at h1,
    cases h1 with L h1,
    have h2 := listempty h1.left, 
    simp at h2,
    by_contradiction h4, 
    apply hnprfalseCL, 
    apply mp,
    exact h1.right,
    exact set.has_emptyc,
    simp only [h2, finite_conjunction_nil, explosion],
  end,
  have h2 := lindenbaum h1, 
  cases h2 with Γ h2, cases h2 with h2 h3, existsi (Γ : set form), apply h2
end

lemma comphelper {form : Type} [pf : Pformula_ax form] {φ : form} (h : ¬ ⊢' φ) :
  ax_consistent ({¬' φ} : set form) :=
ax_consistent_singleton.mpr (mt (mp _ _ dne) h)

/-- If `φ` cannot be proved, there is a maximal consistent set containing `¬ φ` -/
-- Motivation: `lindenbaum` is applied in a few places to `comphelper`,
-- and `simp` can simplify the conditions slightly.
lemma exists_max_ax_consistent_neg_mem {form : Type} [pf : Pformula_ax form]
  {φ : form} (hφ : ¬ ⊢' φ) :
  ∃ (Γ : set form), max_ax_consistent Γ ∧ ¬' φ ∈ Γ :=
by simpa using lindenbaum (comphelper hφ)


----------------------------------------------------------
-- Lemmas about the contents of Maximally Consistent Sets
----------------------------------------------------------

-- set_proves Γ φ ↔ φ ∈ Γ 
lemma mem_max_consistent_iff_proves {form : Type} [pf : Pformula_ax form] 
  {Γ : set (form)} (φ : form) (hΓ : max_ax_consistent Γ) : set_proves Γ φ ↔ φ ∈ Γ :=
⟨begin
  intro h,
  cases max_ax_contains_phi_or_neg hΓ φ,
  { exact h_1, },
  { by_contradiction hf,
    apply not_ax_consistent_of_proves_bot _ (hΓ.1),
    cases h with φs hφs,
    apply exists.intro (¬' φ :: φs),
    split,
    { intros x hx,
      cases hx,
      rw ←hx at h_1, exact h_1,
      apply hφs.left x hx, },
    { have hφ :  ⊢' ((finite_conjunction (¬' φ :: φs)) →' (φ)), from 
        cut (imp_and_r hφs.right) (iden),
      have hnφ :  ⊢' ((finite_conjunction (¬' φ :: φs)) →' (¬' φ)), from 
        imp_and_l iden,
      apply cut,
      { exact imp_imp_and hφ hnφ, },
      { exact not_contra, }, }, },
 end,
 proves_of_mem Γ⟩


-- If no maximally consistent set contains φ ⇒ ⊢ (¬ φ)
lemma false_of_always_false {form : Type} [pf : Pformula_ax form] (φ : form)
  (h : ∀ Γ (hΓ : max_ax_consistent Γ), ¬ set_proves Γ φ) :
  ⊢' (¬' φ) :=
begin
  let Γ := {φ},
  by_cases hφ : ax_consistent Γ,
  { obtain ⟨Γ', hΓ', sub⟩ := lindenbaum hφ,
    have := h Γ' hΓ',
    rw mem_max_consistent_iff_proves φ hΓ' at this,
    have := sub (set.mem_singleton φ),
    contradiction },
  { simp [ax_consistent] at hφ,
    rcases hφ with ⟨(list.nil | ⟨x, xs⟩), sub, pf⟩,
    { unfold finite_conjunction at pf,
      -- we have ⊥, so (φ → ⊥) should also follow
      exact ax_bot_imp pf, },
    { -- we have (φ ∧ φ ... ∧ φ) → ⊥, so (φ → ⊥) should also follow
      induction xs, 

      { simp [finite_conjunction] at *,
        simp [sub] at *,
        exact iff_and_top.mp pf, },

      { simp [finite_conjunction] at *,
        apply xs_ih,
        { exact sub.left, },
        { exact sub.right.right, },

        { simp [sub.right.left, sub.left] at *,
          apply remove_and_imp pf, } }, }, },
end

-- If no maximally consistent set contains φ ⇒ ⊢ (φ ↔ ⊥)
lemma false_of_always_false' {form : Type} [pf : Pformula_ax form] (φ : form)
  (h : ∀ (Γ : set (form)) (hΓ : max_ax_consistent Γ), φ ∉ Γ) :
  ⊢' (φ ↔' ⊥') :=
begin
  apply ax_and.mpr, split,
  { apply (false_of_always_false φ),
    intros Γ hΓ hf,
    apply h,
    { exact hΓ, },
    { apply iff.elim_left (mem_max_consistent_iff_proves φ hΓ),
      exact hf, }, },
  { exact explosion, },
end

-- If set maximally consistent containing φ ⊆ ∅ ⇒ ⊢ (φ ↔ ⊥)
lemma set_empty_iff_false {form : Type} [pf : Pformula_ax form] {φ : form} 
  (hempty : {Γ : {Γ : set form | max_ax_consistent Γ} | φ ∈ Γ.val} ⊆ ∅) :  ⊢' (φ ↔' ⊥') :=
begin
  refine false_of_always_false' φ (λ Γ hΓ h, hempty _),
    { exact ⟨Γ, hΓ⟩ },
    { exact h },
end

-- For maximall consistent Γ, φ ∈ Γ and ⊢ (φ → ψ) ⇒ ψ ∈ Γ
lemma max_ax_contains_by_set_proof {form : Type} [pf : Pformula_ax form] {φ ψ : form} 
  {Γ : set form} (hΓ : max_ax_consistent Γ) (hin : φ ∈ Γ) (hproves :  ⊢' (φ →' ψ)) : ψ ∈ Γ :=
begin
  rw ←(mem_max_consistent_iff_proves ψ hΓ),
  simp[set_proves],
  apply exists.intro [φ],
  split,
  { simp, exact hin, },

  { simp[finite_conjunction],
    rw iff_and_top,
    exact hproves, },
end 

-- For maximall consistent Γ, φ ∈ Γ and ψ ∈ Γ and ⊢ (φ → ψ → χ) ⇒ χ ∈ Γ
lemma max_ax_contains_by_set_proof_2h {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} 
  {Γ : set form} (hΓ : max_ax_consistent Γ) (hinφ : φ ∈ Γ) (hinψ : ψ ∈ Γ) 
  (hproves :  ⊢' (φ →' (ψ →' χ))) : χ ∈ Γ :=
begin
  rw ←(mem_max_consistent_iff_proves χ hΓ),
  simp only [set_proves],
  apply exists.intro [ψ, φ],
  split,
  { simp only [list.mem_cons_iff, list.mem_singleton, forall_eq_or_imp, forall_eq], 
    split, repeat {assumption}},

  { simp[finite_conjunction],
    apply cut,
    apply mp _ _ (p6 _ _) and_commute,
    rw iff_and_top,
    rw and_right_imp,
    exact hproves, },
end 

-- For maximall consistent Γ, ⊢ φ ⇒ φ ∈ Γ
lemma max_ax_contains_taut {form : Type} [pf : Pformula_ax form] {φ : form} {Γ : set form}
  (hΓ : max_ax_consistent Γ) (hproves :  ⊢' (φ)) : φ ∈ Γ :=
begin
  rw ←(mem_max_consistent_iff_proves φ hΓ),
  exact always_true_of_true φ hproves Γ,
end 

-- For maximall consistent Γ,  φ ∈ Γ → ψ ∈ Γ ⇒ φ → ψ ∈ Γ
lemma max_ax_contains_imp_by_proof {form : Type} [pf : Pformula_ax form] {φ ψ : form} 
  {Γ : set form} (hΓ : max_ax_consistent Γ) (himp : φ ∈ Γ → ψ ∈ Γ) : (φ →' ψ) ∈ Γ :=
begin
  cases (max_ax_contains_phi_or_neg hΓ φ),

  { apply max_ax_contains_by_set_proof hΓ (himp h),
    apply p1, },

  { apply max_ax_contains_by_set_proof hΓ (h),
    rw ←and_right_imp,
    apply cut,
    exact not_contra,
    exact explosion, },
end 

-- For maximall consistent Γ, φ ∈ Γ and ⊢ ¬ φ ⇒ false
lemma ax_neg_contains_pr_false {form : Type} [pf : Pformula_ax form] {φ : form} {Γ : set form}
  (hΓ : max_ax_consistent Γ) (hin : φ ∈ Γ) (hax :  ⊢' (¬' φ)) : false :=
begin
  have hbot : (⊥') ∈ Γ, from
    max_ax_contains_by_set_proof hΓ hin (contra_iff_false_ax_not.mp hax),
  apply bot_not_mem_of_ax_consistent Γ hΓ.left hbot,
end

-- For maximall consistent Γ, φ ∈ Γ and ¬ φ ∈ Γ ⇒ false
lemma contra_contains_pr_false {form : Type} [pf : Pformula_ax form] {φ : form} {Γ : set form}
  (hΓ : max_ax_consistent Γ) (hin : φ ∈ Γ) (hnin : (¬' φ) ∈ Γ) : false :=
begin
  have hbot : (⊥') ∈ Γ, from
    max_ax_contains_by_set_proof_2h hΓ hnin hin contra_imp_imp_false,
  apply bot_not_mem_of_ax_consistent Γ hΓ.left hbot,
end

lemma ex_empty_proves_false {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} {Γ : set form}
  (hΓ : max_ax_consistent Γ) (hempty : {Γ : {Γ : set form | max_ax_consistent Γ }| ψ ∈ Γ.val} ⊆ ∅)
  (hin : φ ∈ Γ) (hiff :  ⊢' (ψ ↔' ⊥') →  ⊢' (φ ↔' χ)) (hax :  ⊢' (¬' χ)) : false :=
begin
  -- ⊢ ψ ↔ ⊥, because {ψ} cannot be extended into a maximally consistent set (by hempty), 
  -- so {ψ} must be inconsistent.
  have hiffbot :  ⊢' (ψ ↔' ⊥'), from
    set_empty_iff_false hempty,

  -- ⊢ φ ↔ χ, from hiff
  have hiff' : ⊢' (φ ↔' χ), from hiff hiffbot,

  -- χ ∈ s, from hiff
  have h : χ ∈ Γ, from 
    max_ax_contains_by_set_proof hΓ hin (mp _ _ (p5 _ _) hiff'),

  -- Contradiction from hax and h
  exact ax_neg_contains_pr_false hΓ h hax,
end

lemma not_in_from_notin {form : Type} [pf : Pformula_ax form] {φ : form} {Γ : set form} 
  (hΓ : max_ax_consistent Γ) (h : φ ∉ Γ) : ¬' φ ∈ Γ :=
begin
  cases ((max_ax_contains_phi_xor_neg hΓ.1).mp hΓ φ).left,
  by_contradiction hf, exact h h_1,
  exact h_1,
end

lemma in_from_not_notin {form : Type} [pf : Pformula_ax form] {φ : form} {Γ : set form} 
  (hΓ : max_ax_consistent Γ) (h : φ ∈ Γ) : ¬' φ ∉ Γ :=
begin
  by_contradiction hf,
  exact contra_contains_pr_false hΓ h hf,
end

lemma complement_from_contra {form : Type} [pf : Pformula_ax form] {φ : form} :
  {Γ : {Γ : set form | max_ax_consistent Γ }| (¬' φ) ∈ Γ.val} = 
  {Γ : {Γ : set form | max_ax_consistent Γ }| φ ∈ Γ.val}ᶜ :=
begin
  rw (set.compl_def {Γ : {Γ : set form | max_ax_consistent Γ }| (φ) ∈ Γ.val}),
  apply set.ext,
  intro Γ, simp,
  have hxor : _, from (max_ax_contains_phi_xor_neg Γ.2.1).mp Γ.2 φ,
  split,

  { intros h hf,
    apply hxor.right,
    split, exact hf, exact h, },

  { intro h,
    apply not_in_from_notin Γ.2 h, },
end

lemma ax_imp_from_ex {form : Type} [pf : Pformula_ax form] {φ ψ : form}
  (h : ∀ (Γ : {Γ : set form | max_ax_consistent Γ }), ψ ∈ Γ.val → φ ∈ Γ.val) :
  ⊢' (ψ →' φ) :=
begin
  have himp' : ∀ (Γ : {Γ : set form | max_ax_consistent Γ }), (ψ →' φ) ∈ Γ.val, from
    λ t, max_ax_contains_imp_by_proof t.2 (h t),

  have himpneg : ∀ (Γ : {Γ : set form | max_ax_consistent Γ }), (¬' (ψ →' φ)) ∉ Γ.val, from
    λ t, in_from_not_notin t.2 (himp' t),

  have hempty : {Γ : {Γ : set form | max_ax_consistent Γ } | (¬' (ψ →' φ)) ∈ Γ.val} ⊆ ∅, from
  begin
    simp[set.subset_empty_iff, set.eq_empty_iff_forall_not_mem],
    simp at himpneg, exact himpneg,
  end,

  have hiffbot :  ⊢' ((¬' (ψ →' φ)) ↔' ⊥'), from
    set_empty_iff_false hempty,

  exact contra_not_imp_false_ax (mp _ _ (p5 _ _) hiffbot),
end

-- For maximall consistent Γ, ∀ φ ∈ φs, φ ∈ Γ and ∧ φs ∈ Γ
lemma max_ax_contains_conj {form : Type} [pf : Pformula_ax form] 
  {Γ : set form} {φs : list form} (hΓ : max_ax_consistent Γ) 
  (hin : ∀ φ ∈ φs, φ ∈ Γ) : finite_conjunction φs ∈ Γ :=
begin
  induction φs with φ φs ih,
  { simp only [finite_conjunction_nil],
    exact max_ax_contains_taut hΓ iden, },
  { unfold finite_conjunction at *,
    apply max_ax_contains_by_set_proof_2h hΓ (hin φ (list.mem_cons_self φ φs)),
    { apply ih,
      intros φ hφ,
      apply hin _ (list.mem_cons_of_mem _ hφ), },
    exact p4 _ _, },
end
