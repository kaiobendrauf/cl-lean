/-
Authors: Kai Obendrauf
Adapted from the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley
who's work followed the textbook "Dynamic Epistemic Logic" by 
Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi

This file defines proofs from a Set, consistency and maximal consistency.
It proves sever lemmas related to the above definitions, including Lindenbaums Lemma.
-/

import CLLean.Syntax.formula 
import CLLean.Syntax.propLemmas

import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Order.Zorn

open Set 

----------------------------------------------------------
-- Set Proofs
----------------------------------------------------------

def set_proves {form : Type} [pf : Pformula_ax form] (Γ : Set (form)) (φ : form) :=
∃ (φs : List (form)), (∀ ψ ∈ φs, ψ ∈ Γ) ∧ ⊢' ((finite_conjunction φs) →' φ)

-- φ ∈ Γ ⇒ Γ proves ⊥
lemma proves_of_mem {form : Type} [pf : Pformula_ax form] 
  (Γ : Set (form)) {φ : form} (h : φ ∈ Γ) : 
  set_proves Γ φ := by
  apply Exists.intro [φ]
  split
  { simp, exact h, }
  { simp[finite_conjunction]
    apply imp_and_l iden, }

-- we always have a Set proof of a tautology
lemma always_true_of_true {form : Type} [pf : Pformula_ax form] (φ : form) (h :  ⊢' φ)
  (Γ : Set (form)) : set_proves Γ φ :=
⟨[], by rintro x ⟨⟩, mp _ _ (p1 _ _) h⟩


----------------------------------------------------------
-- Consistency Definitions
----------------------------------------------------------

-- Consistency for an arbitrary Set of formulas Γ
def ax_consistent {form : Type} [pf : Pformula_ax form] (Γ : Set form) : Prop :=
¬ set_proves Γ ⊥'

-- Γ is maximally ax-consistent
def max_ax_consistent {form : Type} [pf : Pformula_ax form] (Γ : Set form) : Prop := 
(ax_consistent Γ) ∧ (∀ Γ', Γ ⊂ Γ' → ¬ (ax_consistent Γ'))

----------------------------------------------------------
-- Lemmas about (Maximal) Consistency 
----------------------------------------------------------

-- If Γ proves ⊥ it must be inconsistent
lemma not_ax_consistent_of_proves_bot {form : Type} [pf : Pformula_ax form] 
  {Γ : Set form} (h : set_proves Γ ⊥') : ¬ (ax_consistent Γ) := by
  simp only [ax_consistent, not_not]
  exact h

-- consistent Γ ⇒ ⊥ ∉ Γ
lemma bot_not_mem_of_ax_consistent {form : Type} [pf : Pformula_ax form] 
 (Γ : Set form) (hΓ : ax_consistent Γ) : (⊥') ∉ Γ :=
λ h, not_ax_consistent_of_proves_bot (proves_of_mem Γ h) hΓ

-- Γ ∪ {φ} proves ψ ⇒  Γ proves φ → ψ 
lemma set_proof_imp {form : Type} [pf : Pformula_ax form] 
  {Γ : Set form} {φ ψ : form} (h : set_proves (Γ ∪ {φ}) (ψ)) :
  set_proves Γ (φ →' ψ) :=  by
  cases h with φs h
  cases h with hΓ h
  revert ψ
  induction φs with χ φs ih
  { intro ψ hψ
    apply Exists.intro []
    split
    { intro χ hχ
      by_contra
      apply List.not_mem_nil _ hχ, }
    { apply imp_if_imp_imp
      exact hψ, }, }
  { intro ψ hψ
    simp [set_proves] at *
    cases ih hΓ.right (and_right_imp.mp hψ) with φs' ih
    cases ih with ihl ihr
    cases hΓ.left
    { rw h at *
      apply Exists.intro (φs')
      split
      { exact ihl, }
      { exact imp_imp_iff_imp.mp ihr, }, }
    { apply Exists.intro (χ :: φs')
      split
      { intro θ hθ
        cases hθ
        { rw hθ
          exact h, }
        { exact ihl θ hθ, }, }
      { apply imp_conj_imp_imp.mpr
        exact imp_shift.mp ihr, }, },}

-- if Γ ∪ {φ} is inconsistent then Γ must prove ¬ φ
lemma inconsistent_prove_neg {form : Type} [pf : Pformula_ax form] 
  {Γ : Set form} {φ : form} (hnax : ¬ ax_consistent (Γ ∪ {φ})) :
  set_proves Γ (¬' φ) := by
  simp only [ax_consistent, not_not] at hnax
  exact set_proof_imp hnax

-- maximally consistent Γ ⇒ φ ∈ Γ ∨ (¬ φ) ∈ Γ
lemma max_ax_contains_phi_or_neg  {form : Type} [pf : Pformula_ax form] 
  {Γ : Set form} (hΓ : max_ax_consistent Γ) (φ : form) :
  φ ∈ Γ ∨ (¬' φ) ∈ Γ := by
  rw or_iff_not_and_not
  by_contra hf
  have h1 : set_proves Γ (¬' φ):= by
      apply inconsistent_prove_neg
      apply hΓ.right (Γ ∪ {φ})
      rw union_singleton
      exact (ssubset_insert hf.left)
  have h2 : set_proves Γ (¬' (¬' φ)):= by
      apply inconsistent_prove_neg
      apply hΓ.right (Γ ∪ {¬' φ})
      rw union_singleton
      exact (ssubset_insert hf.right)
  cases h1 with φs h1
  cases h2 with φs' h2
  apply hΓ.left
  apply Exists.intro (φs ++ φs')
  split
  { intro ψ hψ
    cases hψ
    {exact h1.left ψ hψ, }
    {exact h2.left ψ hψ, }, }
  { apply cut (mp _ _ (p6 _ _) fin_conj_append)
    apply cut (imp_and_and_imp (mp _ _ (mp _ _ (p4 _ _) h1.right) h2.right))
    exact mp _ _ (p5 _ _) (contra_equiv_false), }
end

-- maximally consistent Γ ⇔ φ ∈ Γ xor (¬ φ) ∈ Γ
lemma max_ax_contains_phi_xor_neg {form : Type} [pf : Pformula_ax form] 
  {Γ : Set form} (hax : ax_consistent Γ) :
  max_ax_consistent Γ ↔ ∀ φ, (φ ∈ Γ ∨ (¬' φ) ∈ Γ) ∧ ¬(φ ∈ Γ ∧ (¬' φ) ∈ Γ) := by
  split
  { intro hΓ φ
    split
    { exact max_ax_contains_phi_or_neg hΓ φ, }
    { intro hf
      apply hΓ.left
      apply Exists.intro [φ, ¬' φ]
      split
      { intro ψ hψ
        simp at hψ
        cases hψ
        { rw hψ
         exact hf.left, }
        { rw hψ
         exact hf.right, }, }
      { exact fin_conj_simp φ, }, }, }
  { intro h
    split
    { exact hax, }
    { intro Γ' hΓ hax
      have hΓ : Γ ⊆ Γ' ∧ ¬ Γ' ⊆ Γ:= hΓ
      rw Set.not_subset at hΓ
      cases hΓ.right with φ hφ
      cases hφ with hφΓ' hφnΓ
      specialize h φ
      cases h.left with hφΓ hnφΓ
      { exact hφnΓ hφΓ, }
      { apply hax
        apply Exists.intro [φ, ¬'φ]
        split
        { simp only [List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq]
          split
          { exact hφΓ' }
          { exact mem_of_subset_of_mem hΓ.left hnφΓ, }, }
        { apply fin_conj_simp, }, }, }, }

-- Motivation: a lot of places assume `¬ ⊢' ⊥'` so it's worth trying to reduce these assumptions.
lemma ax_consistent.not_ax_bot {form : Type} [pf : Pformula_ax form] 
  {s : Set form} (h : ax_consistent s) : 
  ¬ ⊢' (⊥' : form) := by
  intro hf
  unfold ax_consistent set_proves at h
  apply h
  apply Exists.intro []
  split
  { simp only [List.not_mem_nil, IsEmpty.forall_iff, imp_true_iff], }
  { simp only [finite_conjunction_nil, ax_not_bot_imp]
    exact hf, }

/-- An empty Set of formulas is consistent iff the theory is consistent. -/
@[simp] lemma ax_consistent_empty {form : Type} [pf : Pformula_ax form] :
  ax_consistent (∅ : Set form) ↔ ¬ ⊢' (⊥' : form) := by
  split; intro h
  { exact h.not_ax_bot }
  { intro hf
    apply not_ax_consistent_of_proves_bot hf
    simp [ax_consistent, set_proves]
    intro φs
    cases φs with φ φs
    { simp only [List.not_mem_nil, IsEmpty.forall_iff, imp_true_iff, finite_conjunction_nil
                  ax_not_bot_imp, forall_true_left]
      exact h, }
    { simp only [List.mem_cons, forall_eq_or_imp, false_and, IsEmpty.forall_iff], }, }

/-- A singleton Set is consistent iff the theory is consistent and the formula is not disprovable.
-/
-- Motivation: `comphelper` seemed to be slightly too specific, this is a more general form I found
@[simp] lemma ax_consistent_singleton {form : Type} [pf : Pformula_ax form] {φ : form} :
  ax_consistent ({φ} : Set form) ↔ ¬ ⊢' (¬' φ) := by
  split
  { intro h
    simp only [ax_consistent, set_proves, mem_singleton_iff, not_exists, not_and] at h
    have := h [φ] (by simp)
    simp only [finite_conjunction_cons, finite_conjunction_nil]
      at ⊢ this
    exact mt (ax_iff_mp (ax_imp_congr_left ax_and_top_iff)).2 this }
  { intro hφ hφs
    cases hφs with φs hφs
    apply hφ
    apply cut (fin_conj_repeat hφs.left)
    exact hφs.right, }

----------------------------------------------------------
-- Lindenbaum 
----------------------------------------------------------

/-- Let `c` be a Nonempty chain of sets and `s` a Finite Set, such that each
element of `s` is in some Set of `c`. Then there is a `t ∈ c` that contains the
entirety of `s`.

In other words, finitary properties are preserved under unions.

This is useful in combination with Zorn's lemma, if you take `⋃₀ c` as the
upper bound of a chain of sets.
-/
lemma exists_subset_of_finite_of_subset_sUnion_of_chain {α : Type*}
  (c : Set (Set α)) (hc : is_chain (⊆) c)
  (t : Set α) (ht : t ∈ c)
  (s : Set α) (hs : s.Finite) (hsc : s ⊆ ⋃₀ c) : ∃ t ∈ c, s ⊆ t := by
  revert hsc
  refine hs.induction_on _ _
  { exact λ _, ⟨t, ht, Set.empty_subset _⟩ }
  rintros x s hxs hs ih hsc
  obtain ⟨⟨u, huc, hxu⟩, hsc⟩ := Set.insert_subset.mp hsc
  obtain ⟨t, htc, hst⟩ := ih hsc
  cases hc.total huc htc with h h
  { exact ⟨t, htc, insert_subset.mpr ⟨h hxu, hst⟩⟩ }
  { exact ⟨u, huc, insert_subset.mpr ⟨hxu, hst.trans h⟩⟩ }

/-- The union of a chain of consistent sets is consistent. -/
lemma ax_consistent_sUnion_chain {form : Type} [pf : Pformula_ax form]
  {c : Set (Set form)} (c_cons : ∀ Γ ∈ c, ax_consistent Γ) (c_chain : is_chain (⊆) c)
  (Γ : Set form) (hΓ : Γ ∈ c) :
  ax_consistent (⋃₀ c) := by
  -- For consistency, we have to show any Finite subset of axioms L does not imply falsum.
  unfold ax_consistent set_proves at ⊢ c_cons
  simp
  intro L L_subset
  simp at *
  -- Since L is Finite, it is completely contained in some element of the chain
  -- and each element of the chain is consistent, therefore L does not imply falsum.
  obtain ⟨Γ, hΓc, hΓ⟩ := exists_subset_of_finite_of_subset_sUnion_of_chain c c_chain
    Γ hΓ { x | x ∈ L } _ _
  { exact c_cons Γ hΓc L hΓ }
  { letI := classical.dec_eq form
    convert Set.finite_mem_finset L.toFinset
    ext; simp, }
  { simp
    apply L_subset, }

lemma lindenbaum {form : Type} [pf : Pformula_ax form] 
  {Γ : Set form} (hax : ax_consistent Γ) :
  ∃ Γ', max_ax_consistent Γ' ∧ Γ ⊆ Γ' := by
  -- By Zorn's lemma, it suffices to show that the union of a chain of consistent sets of formulas
  -- is itself consistent.
  obtain ⟨Γ', consistent, subset, max⟩ := zorn_nonempty_preorder₀ (ax_consistent) _ Γ hax
  { refine ⟨Γ', ⟨consistent, _⟩, subset⟩
    intro Δ hΓΔ hconsΔ
    rw ← Set.lt_eq_ssubset at hΓΔ
    exact hΓΔ.not_le (max Δ hconsΔ hΓΔ.le) }
  { intro c c_cons c_chain Γ hΓ
    exact ⟨⋃₀ c, ax_consistent_sUnion_chain c_cons c_chain Γ hΓ, λ _, Set.subset_sUnion_of_mem⟩, }

lemma listempty {form : Type} {φs : List form} {Γ : Set form} : 
  (∀ φ ∈ φs, φ ∈ Γ) → Γ = ∅ → φs = [] :=  by
  intro h1 h2
  by_contra h3
  have h4 := List.length_pos_of_ne_nil
  have h5 := List.exists_mem_of_length_pos
  cases h5 (h4 h3) with φ h5
  exact absurd (h1 φ h5) (Set.eq_empty_iff_forall_not_mem.mp h2 φ)

lemma max_ax_exists {form : Type} [pf : Pformula_ax form] 
 (hnprfalseCL : ¬  ⊢' (⊥' : form)) : ∃ Γ : Set form, max_ax_consistent Γ := by
  have h1 : ax_consistent ∅:= by
    intro h1
    unfold set_proves at h1
    cases h1 with L h1
    have h2 := listempty h1.left
    simp at h2
    by_contra h4
    apply hnprfalseCL
    apply mp
    exact h1.right
    exact Set.has_emptyc
    simp only [h2, finite_conjunction_nil, explosion]
  have h2 := lindenbaum h1
  cases h2 with Γ h2, cases h2 with h2 h3, existsi (Γ : Set form), apply h2

lemma comphelper {form : Type} [pf : Pformula_ax form] {φ : form} (h : ¬ ⊢' φ) :
  ax_consistent ({¬' φ} : Set form) :=
ax_consistent_singleton.mpr (mt (mp _ _ dne) h)

/-- If `φ` cannot be proved, there is a maximal consistent Set containing `¬ φ` -/
-- Motivation: `lindenbaum` is applied in a few places to `comphelper`
-- and `simp` can simplify the conditions slightly.
lemma exists_max_ax_consistent_neg_mem {form : Type} [pf : Pformula_ax form]
  {φ : form} (hφ : ¬ ⊢' φ) :
  ∃ (Γ : Set form), max_ax_consistent Γ ∧ ¬' φ ∈ Γ :=
by simpa using lindenbaum (comphelper hφ)


----------------------------------------------------------
-- Lemmas about the contents of Maximally Consistent Sets
----------------------------------------------------------

-- set_proves Γ φ ↔ φ ∈ Γ 
lemma mem_max_consistent_iff_proves {form : Type} [pf : Pformula_ax form] 
  {Γ : Set (form)} (φ : form) (hΓ : max_ax_consistent Γ) : set_proves Γ φ ↔ φ ∈ Γ := by
  intro h
  cases max_ax_contains_phi_or_neg hΓ φ
  { exact h_1, }
  { by_contra hf
    apply not_ax_consistent_of_proves_bot _ (hΓ.1)
    cases h with φs hφs
    apply Exists.intro (¬' φ :: φs)
    split
    { intro x hx
      cases hx
      rw ←hx at h_1, exact h_1
      apply hφs.left x hx, }
    { have hφ :  ⊢' ((finite_conjunction (¬' φ :: φs)) →' (φ)):= 
        cut (imp_and_r hφs.right) (iden)
      have hnφ :  ⊢' ((finite_conjunction (¬' φ :: φs)) →' (¬' φ)):= 
        imp_and_l iden
      apply cut
      { exact imp_imp_and hφ hnφ, }
      { exact not_contra, }, }, }
 proves_of_mem Γ⟩


-- If no maximally consistent Set contains φ ⇒ ⊢ (¬ φ)
lemma false_of_always_false {form : Type} [pf : Pformula_ax form] (φ : form)
  (h : ∀ Γ (hΓ : max_ax_consistent Γ), ¬ set_proves Γ φ) :
  ⊢' (¬' φ) := by
  let Γ := {φ}
  by_cases hφ : ax_consistent Γ
  { obtain ⟨Γ', hΓ', sub⟩ := lindenbaum hφ
    have := h Γ' hΓ'
    rw mem_max_consistent_iff_proves φ hΓ' at this
    have := sub (Set.mem_singleton φ)
    contradiction }
  { simp [ax_consistent] at hφ
    rcases hφ with ⟨(List.nil | ⟨x, xs⟩), sub, pf⟩
    { unfold finite_conjunction at pf
      -- we have ⊥, so (φ → ⊥) should also follow
      exact ax_bot_imp pf, }
    { -- we have (φ ∧ φ ... ∧ φ) → ⊥, so (φ → ⊥) should also follow
      induction xs

      { simp [finite_conjunction] at *
        simp [sub] at *
        exact iff_and_top.mp pf, }

      { simp [finite_conjunction] at *
        apply xs_ih
        { exact sub.left, }
        { exact sub.right.right, }

        { simp [sub.right.left, sub.left] at *
          apply remove_and_imp pf, } }, }, }

-- If no maximally consistent Set contains φ ⇒ ⊢ (φ ↔ ⊥)
lemma false_of_always_false' {form : Type} [pf : Pformula_ax form] (φ : form)
  (h : ∀ (Γ : Set (form)) (hΓ : max_ax_consistent Γ), φ ∉ Γ) :
  ⊢' (φ ↔' ⊥') := by
  apply ax_and.mpr, split
  { apply (false_of_always_false φ)
    intro Γ hΓ hf
    apply h
    { exact hΓ, }
    { apply iff.elim_left (mem_max_consistent_iff_proves φ hΓ)
      exact hf, }, }
  { exact explosion, }

-- If Set maximally consistent containing φ ⊆ ∅ ⇒ ⊢ (φ ↔ ⊥)
lemma set_empty_iff_false {form : Type} [pf : Pformula_ax form] {φ : form} 
  (hempty : {Γ : {Γ : Set form | max_ax_consistent Γ} | φ ∈ Γ.val} ⊆ ∅) :  ⊢' (φ ↔' ⊥') := by
  refine false_of_always_false' φ (λ Γ hΓ h, hempty _)
    { exact ⟨Γ, hΓ⟩ }
    { exact h }

-- For maximall consistent Γ, φ ∈ Γ and ⊢ (φ → ψ) ⇒ ψ ∈ Γ
lemma max_ax_contains_by_set_proof {form : Type} [pf : Pformula_ax form] {φ ψ : form} 
  {Γ : Set form} (hΓ : max_ax_consistent Γ) (hin : φ ∈ Γ) (hproves :  ⊢' (φ →' ψ)) : ψ ∈ Γ := by
  rw ←(mem_max_consistent_iff_proves ψ hΓ)
  simp[set_proves]
  apply Exists.intro [φ]
  split
  { simp, exact hin, }

  { simp[finite_conjunction]
    rw iff_and_top
    exact hproves, }

-- For maximall consistent Γ, φ ∈ Γ and ψ ∈ Γ and ⊢ (φ → ψ → χ) ⇒ χ ∈ Γ
lemma max_ax_contains_by_set_proof_2h {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} 
  {Γ : Set form} (hΓ : max_ax_consistent Γ) (hinφ : φ ∈ Γ) (hinψ : ψ ∈ Γ) 
  (hproves :  ⊢' (φ →' (ψ →' χ))) : χ ∈ Γ := by
  rw ←(mem_max_consistent_iff_proves χ hΓ)
  simp only [set_proves]
  apply Exists.intro [ψ, φ]
  split
  { simp only [List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq]
    split, repeat {assumption}}

  { simp[finite_conjunction]
    apply cut
    apply mp _ _ (p6 _ _) and_commute
    rw iff_and_top
    rw and_right_imp
    exact hproves, }

-- For maximall consistent Γ, ⊢ φ ⇒ φ ∈ Γ
lemma max_ax_contains_taut {form : Type} [pf : Pformula_ax form] {φ : form} {Γ : Set form}
  (hΓ : max_ax_consistent Γ) (hproves :  ⊢' (φ)) : φ ∈ Γ := by
  rw ←(mem_max_consistent_iff_proves φ hΓ)
  exact always_true_of_true φ hproves Γ

-- For maximall consistent Γ,  φ ∈ Γ → ψ ∈ Γ ⇒ φ → ψ ∈ Γ
lemma max_ax_contains_imp_by_proof {form : Type} [pf : Pformula_ax form] {φ ψ : form} 
  {Γ : Set form} (hΓ : max_ax_consistent Γ) (himp : φ ∈ Γ → ψ ∈ Γ) : (φ →' ψ) ∈ Γ := by
  cases (max_ax_contains_phi_or_neg hΓ φ)

  { apply max_ax_contains_by_set_proof hΓ (himp h)
    apply p1, }

  { apply max_ax_contains_by_set_proof hΓ (h)
    rw ←and_right_imp
    apply cut
    exact not_contra
    exact explosion, }

-- For maximall consistent Γ, φ ∈ Γ and ⊢ ¬ φ ⇒ false
lemma ax_neg_contains_pr_false {form : Type} [pf : Pformula_ax form] {φ : form} {Γ : Set form}
  (hΓ : max_ax_consistent Γ) (hin : φ ∈ Γ) (hax :  ⊢' (¬' φ)) : false := by
  have hbot : (⊥') ∈ Γ:=
    max_ax_contains_by_set_proof hΓ hin (contra_iff_false_ax_not.mp hax)
  apply bot_not_mem_of_ax_consistent Γ hΓ.left hbot

-- For maximall consistent Γ, φ ∈ Γ and ¬ φ ∈ Γ ⇒ false
lemma contra_contains_pr_false {form : Type} [pf : Pformula_ax form] {φ : form} {Γ : Set form}
  (hΓ : max_ax_consistent Γ) (hin : φ ∈ Γ) (hnin : (¬' φ) ∈ Γ) : false := by
  have hbot : (⊥') ∈ Γ:=
    max_ax_contains_by_set_proof_2h hΓ hnin hin contra_imp_imp_false
  apply bot_not_mem_of_ax_consistent Γ hΓ.left hbot

lemma ex_empty_proves_false {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} {Γ : Set form}
  (hΓ : max_ax_consistent Γ) (hempty : {Γ : {Γ : Set form | max_ax_consistent Γ }| ψ ∈ Γ.val} ⊆ ∅)
  (hin : φ ∈ Γ) (hiff :  ⊢' (ψ ↔' ⊥') →  ⊢' (φ ↔' χ)) (hax :  ⊢' (¬' χ)) : false := by
  -- so {ψ} must be inconsistent.
  have hiffbot :  ⊢' (ψ ↔' ⊥'):=
    set_empty_iff_false hempty

  -- ⊢ φ ↔ χ:= hiff
  have hiff' : ⊢' (φ ↔' χ):= hiff hiffbot

  -- χ ∈ s:= hiff
  have h : χ ∈ Γ:= 
    max_ax_contains_by_set_proof hΓ hin (mp _ _ (p5 _ _) hiff')

  -- Contradiction from hax and h
  exact ax_neg_contains_pr_false hΓ h hax

lemma not_in_from_notin {form : Type} [pf : Pformula_ax form] {φ : form} {Γ : Set form} 
  (hΓ : max_ax_consistent Γ) (h : φ ∉ Γ) : ¬' φ ∈ Γ := by
  cases ((max_ax_contains_phi_xor_neg hΓ.1).mp hΓ φ).left
  by_contra hf, exact h h_1
  exact h_1

lemma in_from_not_notin {form : Type} [pf : Pformula_ax form] {φ : form} {Γ : Set form} 
  (hΓ : max_ax_consistent Γ) (h : φ ∈ Γ) : ¬' φ ∉ Γ := by
  by_contra hf
  exact contra_contains_pr_false hΓ h hf

lemma complement_from_contra {form : Type} [pf : Pformula_ax form] {φ : form} :
  {Γ : {Γ : Set form | max_ax_consistent Γ }| (¬' φ) ∈ Γ.val} = 
  {Γ : {Γ : Set form | max_ax_consistent Γ }| φ ∈ Γ.val}ᶜ := by
  rw (Set.compl_def {Γ : {Γ : Set form | max_ax_consistent Γ }| (φ) ∈ Γ.val})
  apply Set.ext
  intro Γ, simp
  have hxor : _:= (max_ax_contains_phi_xor_neg Γ.2.1).mp Γ.2 φ
  split

  { intro h hf
    apply hxor.right
    split, exact hf, exact h, }

  { intro h
    apply not_in_from_notin Γ.2 h, }

lemma ax_imp_from_ex {form : Type} [pf : Pformula_ax form] {φ ψ : form}
  (h : ∀ (Γ : {Γ : Set form | max_ax_consistent Γ }), ψ ∈ Γ.val → φ ∈ Γ.val) :
  ⊢' (ψ →' φ) := by
  have himp' : ∀ (Γ : {Γ : Set form | max_ax_consistent Γ }), (ψ →' φ) ∈ Γ.val:=
    λ t, max_ax_contains_imp_by_proof t.2 (h t)

  have himpneg : ∀ (Γ : {Γ : Set form | max_ax_consistent Γ }), (¬' (ψ →' φ)) ∉ Γ.val:=
    λ t, in_from_not_notin t.2 (himp' t)

  have hempty : {Γ : {Γ : Set form | max_ax_consistent Γ } | (¬' (ψ →' φ)) ∈ Γ.val} ⊆ ∅:= by
    simp[Set.subset_empty_iff, Set.eq_empty_iff_forall_not_mem]
    simp at himpneg, exact himpneg

  have hiffbot :  ⊢' ((¬' (ψ →' φ)) ↔' ⊥'):=
    set_empty_iff_false hempty

  exact contra_not_imp_false_ax (mp _ _ (p5 _ _) hiffbot)

-- For maximall consistent Γ, ∀ φ ∈ φs, φ ∈ Γ and ∧ φs ∈ Γ
lemma max_ax_contains_conj {form : Type} [pf : Pformula_ax form] 
  {Γ : Set form} {φs : List form} (hΓ : max_ax_consistent Γ) 
  (hin : ∀ φ ∈ φs, φ ∈ Γ) : finite_conjunction φs ∈ Γ := by
  induction φs with φ φs ih
  { simp only [finite_conjunction_nil]
    exact max_ax_contains_taut hΓ iden, }
  { unfold finite_conjunction at *
    apply max_ax_contains_by_set_proof_2h hΓ (hin φ (List.mem_cons_self φ φs))
    { apply ih
      intro φ hφ
      apply hin _ (List.mem_cons_of_mem _ hφ), }
    exact p4 _ _, }
