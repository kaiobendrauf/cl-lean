------------------------------
/-
Copyright (c) 2021 Paula Neeley. All rights reserved.
Author : Paula Neeley
Following the textbook "Dynamic Epistemic Logic" by 
Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi
-/

import syntax.formula syntax.propLemmas
import data.set.basic data.set.finite order.zorn data.list.basic

open set 

variables {agents : Type}


---------------------- Consistency ----------------------

-- finite conjunction of formulas
-- def finite_conjunction {form : Type} [ft : formula form] [fax : formula_ax form] : (list form) → form
--   | list.nil   := ft.top
--   | (f :: fs)  := f ∧' (finite_conjunction fs)  

@[simp] lemma finite_conjunction_nil {form : Type} [ft : formula form] [fax : formula_ax form] :
  finite_conjunction (list.nil : list form) = ft.top := rfl

@[simp] lemma finite_conjunction_cons {form : Type} [ft : formula form] [fax : formula_ax form] (f) (fs : list form) :
  finite_conjunction (f :: fs) = f ∧' finite_conjunction fs := rfl

-- a few helper lemmas about finite conjunctions
lemma fin_conj_simp {form : Type} [ft : formula form] [fax : formula_ax form] : 
  ∀ ψ : form,  ax (¬' (finite_conjunction ((ψ :: (¬' ψ :: list.nil))))) :=
begin
  intro ψ,
  simp [finite_conjunction],
  rw not_and_subst,
  exact not_contra,
  simp[topnotbot],
  exact phi_and_true,
end

lemma imp_conj_imp_imp {form : Type} [ft : formula form] [fax : formula_ax form] 
  {Γ : set form} {φ ψ χ : form} {L : list (form)}
  (h_and_right_imp : (∀ φ ψ χ : form,  ax ((φ ∧' ψ) →' χ) ↔  ax (ψ →' (φ →' χ)))) : 
  ax ((finite_conjunction (φ ::L)) →' ψ) ↔  ax ((finite_conjunction L) →' (φ →' ψ)) :=
begin
  split, 
  intro h, dsimp [finite_conjunction] at h, rw h_and_right_imp at h, exact h,
  intro h, dsimp [finite_conjunction], rw h_and_right_imp, exact h
end

lemma fin_conj_s_imp {form : Type} [ft : formula form] [fax : formula_ax form] 
  {Γ : set form} {φ b : form } {L : list form} :
  ax ((finite_conjunction (φ :: L)) →'  (φ →' b)) →  ax ((finite_conjunction L) →' (φ →' b)) :=
begin
  intro h, rw imp_conj_imp_imp at h, 
  rw imp_imp_iff_imp at h, 
  exact h, exact Γ, 
  exact φ,
  intros _ _ _,
  exact and_right_imp,
end

lemma fin_conj_append {form : Type} [ft : formula form] [fax : formula_ax form] {Γ : set form} {L L' : list (form)} :
  ax (((finite_conjunction L') ∧' (finite_conjunction L)) ↔' (finite_conjunction (L' ++ L))) :=
begin
  induction L', rw finite_conjunction,
  rw ft.iffdef,
  rw topnotbot,
  exact (mp _ _ (mp _ _ (p4 _ _) (cut (mp _ _ (p6 _ _) and_switch') (mp _ _ (p5 _ _) phi_and_true'))) 
    (cut (mp _ _ (p6 _ _) phi_and_true') (mp _ _ (p5 _ _) and_switch'))),
  rw ft.iffdef at *,
  exact mp _ _ (mp _ _ (p4 _ _) (cut (mp _ _ (p5 _ _) and_commute') 
    (imp_and_imp (mp _ _ (p5 _ _) L'_ih))))
    (cut iden (cut (imp_and_imp (mp _ _ (p6 _ _) L'_ih)) (mp _ _ (p6 _ _) and_commute')))
end 

lemma fin_conj_append' {form : Type} [ft : formula form] [fax : formula_ax form] {Γ : set form} {L L' : list (form)} :
  ax ((((finite_conjunction L') ∧' (finite_conjunction L)) →' (finite_conjunction (L' ++ L))) ∧'
  ((finite_conjunction (L' ++ L)) →' ((finite_conjunction L') ∧' (finite_conjunction L)))) :=
begin
  induction L', rw finite_conjunction,
  rw topnotbot,
  exact (mp _ _ (mp _ _ (p4 _ _) (cut (mp _ _ (p6 _ _) and_switch') (mp _ _ (p5 _ _) phi_and_true')))
    (cut (mp _ _ (p6 _ _) phi_and_true') (mp _ _ (p5 _ _) and_switch'))),
  rw ft.iffdef at *,
  exact mp _ _ (mp _ _ (p4 _ _) (cut (mp _ _ (p5 _ _) and_commute') 
    (imp_and_imp (mp _ _ (p5 _ _) L'_ih))))
    (cut iden (cut (imp_and_imp (mp _ _ (p6 _ _) L'_ih)) (mp _ _ (p6 _ _) and_commute')))
end 

lemma fin_conj_repeat_helper {form : Type} [ft : formula form] [fax : formula_ax form] 
  {φ : form} {fs : list form} :
  (∀ ψ ∈ fs, ψ = φ) →  ax (φ →'  (finite_conjunction fs)) :=
begin
  intros h1, induction fs,
  simp[finite_conjunction],
  exact mp _ _ (p1 _ _) prtrue,
  rw finite_conjunction, simp at *,
  cases h1 with h1 h2,
  subst h1,
  exact cut (mp _ _ double_imp (p4 _ _)) (imp_and_and_imp (mp _ _ (mp _ _ (p4 _ _) iden) (fs_ih h2))),
end

lemma fin_conj_repeat {form : Type} [ft : formula form] [fax : formula_ax form] 
  {φ : form} {fs : list form} (hnpr : ¬ ( ax ft.bot)) :
  (∀ ψ ∈ fs, ψ = ¬' φ) →  ax (¬' (finite_conjunction fs)) →  ax φ :=
begin
  intros h1 h2, induction fs,
  simp[finite_conjunction] at h2,
  have hbot :  ax ft.bot,
  { apply mp _ _ dne,
    simp [formula.notdef, ft.topdef] at *,
    exact h2, },
  exact absurd hbot (hnpr),
  repeat {rw fin_conj at *}, simp at *,
  cases h1 with h1 h3, 
  have h5 := contrapos.mpr (fin_conj_repeat_helper h3),
  subst h1,
  apply mp _ _ (mp _ _ (p3 _ _) (contrapos.mpr (cut h5 dne))),
  have h6 := iff_not and_switch,
  rw ft.iffdef at h6,
  apply contrapos.mpr (cut ((demorgans.mp) (mp _ _ (mp _ _ (p6 _ _) (h6)) h2)) dne),
end

lemma listempty {form : Type} [ft : formula form] [fax : formula_ax form] {fs : list form} {Γ : set form} :
  (∀ φ ∈ fs, φ ∈ Γ) → Γ = ∅ → fs = list.nil := 
begin
  intros h1 h2,
  by_contradiction h3,
  have h4 := list.length_pos_of_ne_nil,
  have h5 := list.exists_mem_of_length_pos,
  cases h5 (h4 h3) with φ h5,
  exact absurd (h1 φ h5) (set.eq_empty_iff_forall_not_mem.mp h2 φ)
end

lemma finite_conj_forall_iff {form : Type} [ft : formula form] [fax : formula_ax form] {fs : list form} : 
  (∀ x ∈ fs, ax x) ↔ ax (finite_conjunction fs) :=
begin
  induction fs,
  { simp [finite_conjunction],
    exact prtrue, },
  { unfold finite_conjunction,
    split,
    { intro h,
      rw ax_and,
      split,
      { apply h, 
        simp },
      { apply fs_ih.mp,
        intros x hx,
        apply h, 
        simp [hx], }, },
    { intros h x hx,
      cases hx,
      { simp [hx] at *,
        exact h.left, },
      { rw ax_and at h,
        apply fs_ih.mpr h.right,
        exact hx, }, }, },
end

lemma finite_conj_forall_imp {form : Type} [ft : formula form] [fax : formula_ax form] {fs : list form} : 
  (∀ x ∈ fs, ax ((finite_conjunction fs) →' x)) :=
begin
  induction fs,
  { simp only [list.not_mem_nil, forall_false_left, implies_true_iff], },
  { intros x hx,
    unfold finite_conjunction, 
    cases hx,
    { simp [hx] at *,
      exact p5 _ _, },
    { apply cut,
      { apply iff_l,
        exact and_switch, },
      { refine imp_and_l _,
        exact fs_ih x hx, }, }, },
end

lemma finite_conj_imp {form : Type} [ft : formula form] [fax : formula_ax form] {fs : list form} 
  {φ : form} (h : φ ∈ fs) : 
  ax ((finite_conjunction fs) →' φ) := finite_conj_forall_imp φ h

lemma noin_imp_nfin_con {form : Type} [ft : formula form] [fax : formula_ax form] {fs : list form} 
  {φ : form} (h : φ ∈ fs) : 
  ax ((¬' φ) →' ¬' (finite_conjunction fs)) := contrapos.mpr (finite_conj_imp h)

-- Consistency for a finite set of formulas L
def finite_ax_consistent {form : Type} [ft : formula form] [fax : formula_ax form] (fs : list (form)) : Prop := 
¬  ax ((finite_conjunction fs) →' ft.bot)


-- Consistency for an arbitrary set of formulas Γ
def ax_consistent {form : Type} [ft : formula form] [fax : formula_ax form] (Γ : set form) : Prop :=
∀ fs : list (form), (∀ ψ ∈ fs, ψ ∈ Γ) → (finite_ax_consistent fs)


-- Γ is maximally ax-consistent
def max_ax_consistent {form : Type} [ft : formula form] [fax : formula_ax form] (Γ : set form) : Prop := 
(ax_consistent Γ) ∧ (∀ Γ', Γ ⊂ Γ' → ¬ (ax_consistent Γ'))


lemma max_imp_ax {form : Type} [ft : formula form] [fax : formula_ax form] {Γ : set form} : 
  max_ax_consistent Γ → ax_consistent Γ :=
λ h1, h1.left

-- -- Lemma 5 from class notes
lemma five_helper {form : Type} [ft : formula form] [fax : formula_ax form] :
  ∀ Γ : set form, ∀ φ : form, ∀ L : list (form), ∀ b : form, 
  (∀ ψ ∈ L, ψ ∈ Γ ∨ ψ = φ) →  ax ((finite_conjunction L) →' b) → ∃ L',
  (∀ ψ ∈ L', ψ ∈ Γ) ∧  ax ((finite_conjunction L') →' (φ →' b)) :=
begin
  intros Γ φ L b h1 h2, 
  revert b, 
  induction L,
  {intros b h2, existsi (list.nil : list (form)), split, 
  intros ψ h3, exfalso, apply list.not_mem_nil ψ h3, 
  apply imp_if_imp_imp,
  exact h2,},

  { intros b h2,
    have h1a : ∀ (ψ : form), ψ ∈ L_tl → ψ ∈ Γ ∨ ψ = φ, 
      {intros ψ h2, apply h1 ψ (list.mem_cons_of_mem L_hd h2)},
    have h1b : L_hd ∈ Γ ∨ L_hd = φ, 
      {apply h1 L_hd, left, refl},
    cases h1b,

    { have h3 := and_right_imp.mp h2,
      cases L_ih h1a (L_hd →' b) h3 with L' ih, existsi (L_hd ::L' : list form),
      cases ih, split, intros ψ h4, cases h4,

      { subst h4, exact h1b, },

      { apply ih_left ψ h4, },

      { rw imp_shift at ih_right,
        rw ←imp_conj_imp_imp at ih_right,
        exact ih_right,
        have h3 :  ax ((finite_conjunction (L_hd ::L_tl)) →'  b), 
        exact h2, exact Γ, exact b,
        intros _ _ _,
        exact and_right_imp, }, },

    { have h4 := and_right_imp.mp,
      have h5 :  ax ((finite_conjunction L_tl) →' (φ →' b)),
        from eq.subst h1b (h4 h2),
      cases L_ih h1a (φ →' b) h5 with L' ih, 
      existsi (L' : list form), split, 
      exact ih.left, exact imp_imp_iff_imp.mp ih.right, }, },
end


lemma five {form : Type} [ft : formula form] [fax : formula_ax form] : 
  ∀ Γ : set form, ∀ φ : form, ¬ ax_consistent (Γ ∪ {φ}) → ∃ L' : list form,
  (∀ ψ ∈ L', ψ ∈ Γ) ∧  ax ((finite_conjunction L') →' (¬' φ)) :=
begin
  intro Γ, intro φ, intro h1, rw ax_consistent at h1, 
  push_neg at h1,
  cases h1 with L h1,
  have h2 : (∀ ψ ∈ L, ψ ∈ Γ ∨ ψ = φ) →  
            ax ((finite_conjunction L) →' ft.bot) → 
            ∃ L', (∀ ψ ∈ L', ψ ∈ Γ) ∧  ax ((finite_conjunction L') →' (φ →' ft.bot)), from
              five_helper Γ φ L ft.bot,
  cases h1,
  have h3 : (∀ (ψ : form), ψ ∈ L → ψ ∈ Γ ∨ ψ = φ), 

    { intros ψ this,
      have hor : ψ ∈ Γ ∨ ψ = φ, from h1_left ψ this, 
      have hor' : ψ = φ ∨ ψ ∈ Γ, from or.swap hor,
      exact or.swap hor', },
  rw finite_ax_consistent at h1_right, 
  rw not_not at h1_right,
  rw formula.notdef at *,
  apply h2 h3,
  exact h1_right,
end

-- Lemma 6 from class notes
lemma max_ax_contains_phi_or_neg  {form : Type} [ft : formula form] [fax : formula_ax form] (Γ : set form) :
  max_ax_consistent Γ → ∀ φ : form, φ ∈ Γ ∨ (¬' φ) ∈ Γ :=
begin
  intros h1 φ, rw or_iff_not_and_not, by_contradiction h2,
  cases h2 with h2l h2r,
  cases h1 with h1l h1r, 
  have h2 := h1r (Γ ∪ {φ}),
  have h3 : ¬ax_consistent ({¬' φ} ∪ Γ), 

    { apply h1r,
      from set.ssubset_insert h2r, },
  have h5 : ¬ax_consistent (Γ ∪ {φ}), 

    { apply h2,
      have heq : Γ ∪ {φ} = insert φ Γ, from by finish,
      rw heq,
      from set.ssubset_insert h2l,}, 
  have h6 := five Γ φ _, have h7 := five Γ (¬' φ) _, 
  cases h6 with L' h6, cases h7 with L h7, cases h6 with h6l h6r,
  cases h7 with h7l h7r,
  have h8 := imp_and_and_imp (mp _ _ (mp _ _ (p4 _ _) h6r) h7r),
  have h9 := cut (mp _ _ (p6 _ _) fin_conj_append') 
            (cut h8 (mp _ _ (p5 _ _) (contra_equiv_false'))),
  have h10 : (∀ (ψ : form), ψ ∈ L' ++ L → ψ ∈ Γ), 
  intro ψ, intro h10,
  rw list.mem_append at h10, cases h10, exact h6l ψ h10, exact h7l ψ h10,
  exact absurd h9 (h1l (L' ++ L) h10),
  exact {φ},
  rw union_comm at h3,
  exact h3,
  exact h5,
end

lemma max_ax_contains_phi_xor_neg {form : Type} [ft : formula form] [fax : formula_ax form] 
  (Γ : set form) (h : ax_consistent Γ) :
  max_ax_consistent Γ ↔ ∀ φ, (φ ∈ Γ ∨ (¬' φ) ∈ Γ) ∧ ¬(φ ∈ Γ ∧ (¬' φ) ∈ Γ) :=
begin 
  simp, split, 
  intro h1, intro φ, 
  split, exact max_ax_contains_phi_or_neg Γ h1 φ,
  {rw ←not_and, by_contradiction h2,
  cases h2 with h2 h3,
  simp [ax_consistent] at h,

  let l := (φ :: (¬' φ :: list.nil)),
  specialize h (l), simp at *,
  have h4 : (∀ (ψ : form ), ψ = φ ∨ ψ = ¬' φ → ψ ∈ Γ), 
  {intros ψ h4, cases h4, subst h4, exact h2, subst h4, exact h3},
  have h5 :  ax (¬' (finite_conjunction l)), from fin_conj_simp φ, 
  have h6 : _, from h h2 h3,
  simp [finite_ax_consistent, formula.notdef] at h6,
  simp [formula.notdef] at h5,
  exact h6 h5, },
  intro h1, split, exact h,
  intros Γ' h2,
  have h3 : Γ ⊆ Γ' ∧ ¬ Γ' ⊆ Γ, from h2,
  cases h3,
  rw set.not_subset at h3_right,
  apply (exists.elim h3_right), simp, intros ψ h4 h5,
  specialize h1 ψ, cases h1,
  cases h1_left,
  apply absurd h1_left h5,
  have h6 : (¬' ψ) ∈ Γ', from set.mem_of_subset_of_mem h3_left h1_left,
  rw ax_consistent, 
  push_neg,
  existsi ((ψ :: (¬' ψ :: list.nil))),
  simp, split, 

  { split,
    { exact h4, },
    { exact h6, }, }, 

  { have hfcs : _, from fin_conj_simp ψ,
    simp[finite_ax_consistent],
    rw formula.notdef at *,
    exact hfcs, },
end

-- Exercise 1 from class notes
lemma ex1help {form : Type} [ft : formula form] [fax : formula_ax form] {Γ : set form} {φ : form} {ψs ψs' : list (form)} :
  (∀ ψ ∈ ψs, ψ ∈ Γ) → ax (finite_conjunction ψs →' φ) → (∀ ψ ∈ ψs', ψ ∈ (insert φ Γ)) 
  → ∃ ψs'' : list (form), (∀ ψ ∈ ψs'', ψ ∈ Γ) ∧ ax (finite_conjunction ψs'' →' finite_conjunction ψs') :=
begin
intros h1 h2 h3, induction ψs',
existsi (list.nil : list (form)),
split,
intros ψ h4, exact false.elim h4,
exact iden,
simp at *, cases h3 with h3 h4,
cases ψs'_ih h4 with ψs'' ψs'_ih,
cases ψs'_ih with ih1 ih2,
cases h3, 
existsi (ψs'' ++ ψs : list (form)),
split,
simp at *, intros ψ h2,
cases h2 with h2 h5,
exact ih1 ψ h2,
exact h1 ψ h5,
subst h3, 
apply cut (mp _ _ (p6 _ _) fin_conj_append') 
  (cut (mp _ _ (p5 _ _) and_switch') (imp_and_and_imp (mp _ _ (mp _ _ (p4 _ _) h2) ih2))),
exact Γ,
existsi (ψs'_hd::ψs'' : list (form)),
split, simp at *, split, exact h3, exact ih1,
exact imp_and_imp ih2,
end


lemma exercise1 {form : Type} [ft : formula form] [fax : formula_ax form] {Γ : set form} {φ : form} {ψs : list (form)} :
  max_ax_consistent Γ → (∀ ψ ∈ ψs, ψ ∈ Γ) → ax (finite_conjunction ψs →' φ) → φ ∈ Γ :=
begin
  intros h1 h2 h3, 
  by_contradiction h4, 
  cases h1 with h1 h5, 
  specialize h5 (Γ ∪ {φ}), 
  simp at h5,
  specialize h5 (set.ssubset_insert h4), 
  unfold ax_consistent at h5,
  push_neg at h5,
  cases h5 with L' h5,
  cases h5 with h5 h6,
  rw finite_ax_consistent at h6, 
  rw not_not at h6,
  have h7 := ex1help h2 h3 h5,
  cases h7 with L'' h7,
  cases h7 with h7 h8,
  apply h1 L'' h7,
  exact cut h8 h6,
end


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
lemma ax_consistent_sUnion_chain {form : Type} [ft : formula form] [fax : formula_ax form]
  {c : set (set form)} (c_cons : ∀ Γ ∈ c, ax_consistent Γ) (c_chain : is_chain (⊆) c)
  (Γ : set form) (hΓ : Γ ∈ c) :
  ax_consistent (⋃₀ c) :=
begin
  -- For consistency, we have to show any finite subset of axioms L does not imply falsum.
  unfold ax_consistent finite_ax_consistent at ⊢ c_cons,
  intros L L_subset,
  -- Since L is finite, it is completely contained in some element of the chain,
  -- and each element of the chain is consistent, therefore L does not imply falsum.
  obtain ⟨Γ, hΓc, hΓ⟩ := exists_subset_of_finite_of_subset_sUnion_of_chain c c_chain
    Γ hΓ
    { x | x ∈ L } _ L_subset,
  { exact c_cons Γ hΓc L hΓ },
  letI := classical.dec_eq form,
  convert set.finite_mem_finset L.to_finset,
  ext; simp
end

lemma lindenbaum {form : Type} [ft : formula form] [fax : formula_ax form] {Γ : set form} (hax : ax_consistent Γ) :
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
    exact ⟨⋃₀ c, ax_consistent_sUnion_chain c_cons c_chain Γ hΓ, λ _, set.subset_sUnion_of_mem⟩, }
end


-- -- Corollary 8 from class notes
lemma max_ax_exists {form : Type} [ft : formula form] [fax : formula_ax form] (hnprfalseCL : ¬  ax ft.bot) : 
  ∃ Γ : set form, max_ax_consistent Γ :=
begin
  have h1 : ax_consistent ∅,
  {intro L, intro h2, rw finite_ax_consistent, 
  have h3 := listempty h2, have this : ∅ = ∅, refl, 
  specialize h3 this, subst h3, by_contradiction h4, 
  apply hnprfalseCL, 
  apply mp,
  exact h4,
  exact prtrue, exact ft, exact fax, },
  have h2 := lindenbaum h1, 
  cases h2 with Γ h2, cases h2 with h2 h3, existsi (Γ : set form), apply h2
end

def set_proves {form : Type} [ft : formula form] [fax : formula_ax form] (Γ : set (form)) (φ : form) :=
∃ (fs : list (form)), (∀ x ∈ fs, x ∈ Γ) ∧ ax ((finite_conjunction fs) →' φ)

lemma not_ax_consistent_of_proves_bot {form : Type} [ft : formula form] [fax : formula_ax form] (Γ : set form)
  (h : set_proves Γ ft.bot) : ¬ (ax_consistent Γ) :=
begin
  intro hf,
  cases h with l h,
  cases h,
  apply hf,
  intros ψ hψ,
  apply h_left,exact hψ,
  exact h_right,
end

lemma bot_not_mem_of_ax_consistent {form : Type} [ft : formula form] [fax : formula_ax form] (Γ : set (form))
  (hΓ : ax_consistent Γ) : (ft.bot) ∉ Γ :=
begin
  intro hf,
  have hbot_proves_bot : set_proves Γ ft.bot, from 
  begin
    let l := (ft.bot :: list.nil),
    apply exists.intro l,
    split,
    { simp, exact hf, },

    { simp[l, finite_conjunction],
      apply cut,
      { exact p5 _ _, },
      { exact iden}, },
  end,
  exact (not_ax_consistent_of_proves_bot Γ hbot_proves_bot) hΓ,
end

lemma proves_of_mem {form : Type} [ft : formula form] [fax : formula_ax form] (Γ : set (form)) (φ : form)
  (h : φ ∈ Γ) : set_proves Γ φ :=
⟨list.cons φ list.nil,
  by simpa using h,
  have  ax ((φ ∧' ft.top) →' φ), from p5 _ _,
  by simpa [finite_conjunction]⟩

lemma mem_max_consistent_iff_proves {form : Type} [ft : formula form] [fax : formula_ax form] (Γ : set (form)) (φ : form)
   (hΓ : max_ax_consistent Γ) : set_proves Γ φ ↔ φ ∈ Γ :=
⟨begin
  intro h,
  cases max_ax_contains_phi_or_neg Γ hΓ φ,
  { assumption },
  exfalso,
  refine not_ax_consistent_of_proves_bot Γ _ (hΓ.1),
  simp [set_proves, finite_conjunction] at ⊢ h,
  cases h with fs h,
  cases h,
  apply exists.intro (¬' φ :: fs),
  split,

  { intros x hx,
    cases hx,
    rw ←hx at h_1, exact h_1,
    apply h_left x hx, },

  { have hφ :  ax ((finite_conjunction (¬' φ :: fs)) →' (φ)), from 
      cut (imp_and_r h_right) (iden),
    have hnφ :  ax ((finite_conjunction (¬' φ :: fs)) →' (¬' φ)), from 
      imp_and_l iden,
    apply cut,
    { exact imp_imp_and hφ hnφ, },
    { exact contra_imp_false, }, },
 end,
 proves_of_mem Γ φ⟩

lemma always_true_of_true {form : Type} [ft : formula form] [fax : formula_ax form] (φ : form) (h :  ax φ)
  (Γ : set (form)) : set_proves Γ φ :=
⟨list.nil, by rintro x ⟨⟩, mp _ _ (p1 _ _) h⟩

lemma always_true_of_true_imp {form : Type} [ft : formula form] [fax : formula_ax form] (φ : form)
  (Γ : set (form)) : ax φ → set_proves Γ φ :=
  λ h, always_true_of_true φ h Γ

lemma false_of_always_false {form : Type} [ft : formula form] [fax : formula_ax form] (φ : form)
  (h : ∀ (Γ : set (form)) (hΓ : max_ax_consistent Γ), ¬ set_proves Γ φ) :
   ax (¬' φ) :=
begin
  let Γ := {φ},
  by_cases hφ : ax_consistent Γ,
  { obtain ⟨Γ', hΓ', sub⟩ := lindenbaum hφ,
    have := h Γ' hΓ',
    rw mem_max_consistent_iff_proves Γ' φ hΓ' at this,
    have := sub (set.mem_singleton φ),
    contradiction },
  { simp [ax_consistent, finite_ax_consistent] at hφ,
    rcases hφ with ⟨(list.nil | ⟨x, xs⟩), sub, pf⟩,
    { unfold finite_conjunction at pf,
      -- we have ⊥, so (φ → ⊥) should also follow
      rw ft.notdef,
      exact ax_bot_imp pf, },
    { -- we have (φ ∧ φ ... ∧ φ) → ⊥, so (φ → ⊥) should also follow
      induction xs, 

      { simp [finite_conjunction] at *,
        simp [sub, formula.notdef] at *,
        exact iff_and_top.mp pf, },

      { simp [finite_conjunction] at *,
        apply xs_ih,
        { exact sub.left, },
        { exact sub.right.right, },

        { simp [sub.right.left, sub.left] at *,
          apply remove_and_imp pf, } }, }, },
end

lemma false_of_always_false' {form : Type} [ft : formula form] [fax : formula_ax form] (φ : form)
  (h : ∀ (Γ : set (form)) (hΓ : max_ax_consistent Γ), φ ∉ Γ) :
   ax (φ ↔' ft.bot) :=
begin
  rw ft.iffdef,
  have hfoaf : _, from (false_of_always_false φ),
  apply mp,
  apply mp,
  apply p4,
  { rw formula.notdef at hfoaf,
    apply hfoaf,
    intros Γ hΓ hf,
    apply h,
    { exact hΓ, },
    { apply iff.elim_left (mem_max_consistent_iff_proves Γ φ hΓ),
      exact hf, }, },
  { exact explosion, },
end

lemma max_ax_contains_by_set_proof {form : Type} [ft : formula form] [fax : formula_ax form] {φ ψ : form} {Γ : set form}
  (hΓ : max_ax_consistent Γ) (hin : φ ∈ Γ) (hproves :  ax (φ →' ψ)) : ψ ∈ Γ :=
begin
  rw ←(mem_max_consistent_iff_proves Γ ψ hΓ),
  simp[set_proves],
  apply exists.intro (φ :: list.nil),
  split,
  { simp, exact hin, },

  { simp[finite_conjunction],
    rw iff_and_top,
    exact hproves, },
end 

lemma max_ax_contains_by_set_proof_2h {form : Type} [ft : formula form] [fax : formula_ax form] {φ ψ χ : form} {Γ : set form}
  (hΓ : max_ax_consistent Γ) (hinφ : φ ∈ Γ) (hinψ : ψ ∈ Γ) (hproves :  ax (φ →' (ψ →' χ))) : χ ∈ Γ :=
begin
  rw ←(mem_max_consistent_iff_proves Γ χ hΓ),
  simp[set_proves],
  apply exists.intro (ψ :: φ :: list.nil),
  split,
  { simp, split, repeat {assumption}},

  { simp[finite_conjunction],
    apply cut,
    apply mp _ _ (p6 _ _) and_commute',
    rw iff_and_top,
    rw and_right_imp,
    exact hproves, },
end 

lemma max_ax_contains_by_empty_proof {form : Type} [ft : formula form] [fax : formula_ax form] {φ : form} {Γ : set form}
  (hΓ : max_ax_consistent Γ) (hproves :  ax (φ)) : φ ∈ Γ :=
begin
  rw ←(mem_max_consistent_iff_proves Γ φ hΓ),
  simp[set_proves],
  apply exists.intro (list.nil),
  split,
  { simp, },

  { unfold finite_conjunction,
    apply mp,
    apply p1,
    exact hproves, },
end 

lemma max_ax_contains_imp_by_proof {form : Type} [ft : formula form] [fax : formula_ax form] {φ ψ : form} {Γ : set form}
  (hΓ : max_ax_consistent Γ) (himp : φ ∈ Γ → ψ ∈ Γ) : (φ →' ψ) ∈ Γ :=
begin
  cases (max_ax_contains_phi_or_neg Γ hΓ φ),

  { apply max_ax_contains_by_set_proof hΓ (himp h),
    apply p1, },

  { apply max_ax_contains_by_set_proof hΓ (h),
    rw ←and_right_imp,
    apply cut,
    exact contra_imp_false,
    exact explosion, },
end 

lemma set_empty_iff_false {form : Type} [ft : formula form] [fax : formula_ax form] {φ : form} 
  (hempty : {Γ : {Γ : set form | max_ax_consistent Γ }| φ ∈ Γ.val} ⊆ ∅) :  ax (φ ↔' ft.bot) :=
begin
  refine false_of_always_false' φ (λ Γ hΓ h, hempty _),
    { exact ⟨Γ, hΓ⟩ },
    { exact h },
end

lemma ax_neg_containts_pr_false {form : Type} [ft : formula form] [fax : formula_ax form] {φ : form} {Γ : set form}
  (hΓ : max_ax_consistent Γ) (hin : φ ∈ Γ) (hax :  ax (¬' φ)) : false :=
begin
  have hbot : (ft.bot) ∈ Γ, from
    max_ax_contains_by_set_proof hΓ hin (contra_iff_false_ax_not.mp hax),
  apply bot_not_mem_of_ax_consistent Γ hΓ.left hbot,
end

lemma contra_containts_pr_false {form : Type} [ft : formula form] [fax : formula_ax form] {φ : form} {Γ : set form}
  (hΓ : max_ax_consistent Γ) (hin : φ ∈ Γ) (hnin : (¬' φ) ∈ Γ) : false :=
begin
  have hbot : (ft.bot) ∈ Γ, from
    max_ax_contains_by_set_proof_2h hΓ hnin hin contra_imp_imp_false,
  apply bot_not_mem_of_ax_consistent Γ hΓ.left hbot,
end

lemma ex_empty_proves_false {form : Type} [ft : formula form] [fax : formula_ax form] {φ ψ χ : form} {Γ : set form}
  (hΓ : max_ax_consistent Γ) (hempty : {Γ : {Γ : set form | max_ax_consistent Γ }| ψ ∈ Γ.val} ⊆ ∅) 
  (hin : φ ∈ Γ) (hiff :  ax (ψ ↔' ft.bot) →  ax (φ ↔' χ)) (hax :  ax (¬' χ)) : false :=
begin
  -- ⊢ ψ ↔ ⊥, because {ψ} cannot be extended into a maximally consistent set (by hempty), 
  -- so {ψ} must be inconsistent.
  have hiffbot :  ax (ψ ↔' ft.bot), from
    set_empty_iff_false hempty,

  -- ⊢ φ ↔ χ, from hiff
  have hiff' : ax (φ ↔' χ), from hiff hiffbot,
  rw ft.iffdef at hiff',

  -- χ ∈ s, from hiff
  have h : χ ∈ Γ, from 
    max_ax_contains_by_set_proof hΓ hin (mp _ _ (p5 _ _) hiff'),

  -- Contradiction from hax and h
  exact ax_neg_containts_pr_false hΓ h hax,
end

lemma not_in_from_notin {form : Type} [ft : formula form] [fax : formula_ax form] {φ : form} {Γ : set form} 
  (hΓ : max_ax_consistent Γ) (h : φ ∉ Γ) : ((formula.not) φ ∈ Γ ) :=
begin
  cases ((max_ax_contains_phi_xor_neg Γ hΓ.1).mp hΓ φ).left,
  by_contradiction hf, exact h h_1,
  exact h_1,
end

lemma in_from_not_notin {form : Type} [ft : formula form] [fax : formula_ax form] {φ : form} {Γ : set form} 
  (hΓ : max_ax_consistent Γ) (h : φ ∈ Γ) : ((formula.not) φ ∉ Γ ) :=
begin
  by_contradiction hf,
  exact contra_containts_pr_false hΓ h hf,
end

lemma complement_from_contra {form : Type} [ft : formula form] [fax : formula_ax form] {φ : form} :
  {Γ : {Γ : set form | max_ax_consistent Γ }| (¬' φ) ∈ Γ.val} = 
  {Γ : {Γ : set form | max_ax_consistent Γ }| φ ∈ Γ.val}ᶜ :=
begin
  rw (set.compl_def {Γ : {Γ : set form | max_ax_consistent Γ }| (φ) ∈ Γ.val}),
  apply set.ext,
  intro Γ, simp,
  have hxor : _, from (max_ax_contains_phi_xor_neg Γ.1 Γ.2.1).mp Γ.2 φ,
  split,

  { intros h hf,
    apply hxor.right,
    split, exact hf, exact h, },

  { intro h,
    apply not_in_from_notin Γ.2 h, },
end

lemma ax_imp_from_ex {form : Type} [ft : formula form] [fax : formula_ax form] {φ ψ : form}
  (h : ∀ (Γ : {Γ : set form | max_ax_consistent Γ }), ψ ∈ Γ.val → φ ∈ Γ.val) :
  ax (ψ →' φ) :=
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

  have hiffbot :  ax ((¬' (ψ →' φ)) ↔' ft.bot), from
    set_empty_iff_false hempty,
  rw ft.iffdef at hiffbot,

  exact contra_not_imp_false_ax (mp _ _ (p5 _ _) hiffbot),
end
