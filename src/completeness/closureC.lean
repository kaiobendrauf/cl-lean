import syntax.axiomsCLC
import syntax.consistency_lemmas

local attribute [instance] classical.prop_decidable

open set formCLC

----------------------------------------------------------
-- Filtration closure cl
----------------------------------------------------------

-- Let cl(φ) be the smallest set such that:
-- cl(φ) contains all subformulas of φ.
-- For every φ in cl(φ), if φ is not of the form ¬ψ, then ¬φ ∈ cl(φ). In other words cl(φ) is closed under single negations. 
-- C G (φ) ∈ cl (φ) ⇒ K i (C G (φ)) ∈ cl(φ), ∀ i ∈ G . 
-- [G] φ ∈ cl (φ), G ≠ ∅ ⇒ C G [G] φ ∈ cl (φ).

noncomputable def cl_C {agents : Type} [hN : fintype agents] (G : set (agents)) (φ : formCLC agents) : 
  finset (formCLC agents) :=
finset.image (λ i, k (i) (c G φ)) (to_finset G) ∪ finset.image (λ i, (¬ k (i) (c G φ))) (to_finset G)

noncomputable def cl_E {agents : Type} [hN : fintype agents] (G : set (agents)) (φ : formCLC agents) : 
  finset (formCLC agents) := 
finset.image (λ i, k i φ) (to_finset G) ∪ finset.image (λ i, (¬ (k i φ))) (to_finset G)

noncomputable def cl {agents : Type} [hN : fintype agents] : 
  formCLC agents → finset (formCLC agents)
|  bot          := {bot, ¬ bot}
| (var n)       := {var n, ¬ var n}
| (imp φ ψ)     := cl φ ∪ cl ψ ∪ (ite (ψ = bot) {(imp φ bot)} {(imp φ ψ), ¬ (imp φ ψ)} )
| (and φ ψ)     := cl φ ∪ cl ψ ∪ {(and φ ψ), ¬ (and φ ψ)}
| ([G] φ)       := cl φ ∪ {([G] φ), ¬ [G] φ} ∪ 
                    (ite (G = ∅) (finset.empty : finset (formCLC agents)) 
                         ({(c (G) ([G] φ)), ¬(c (G) ([G] φ))} ∪ cl_C G ([G] φ)))
| (k i φ)       := cl φ ∪ {(k i φ), ¬ (k i φ)}
| (e G φ)       := cl φ ∪ {(e G φ), ¬ (e G φ)} ∪ (cl_E G φ)
| (c G φ)       := cl φ ∪ {(c G φ), ¬ (c G φ)} ∪ cl_C G φ

lemma cl_contains_phi {agents : Type} [hN : fintype agents] (φ : formCLC agents) :
  φ ∈ cl φ :=
begin
  cases φ,
  repeat { unfold cl, simp, },
  { split_ifs,
    repeat { simp[h] at *, }, },
end

lemma cl_closed_single_neg {agents : Type} [hN : fintype agents] 
  (φ x : formCLC agents) (hx : x ∈ cl φ) :
  ∃ ψ, (ψ ∈ cl φ ∧ axCLC (ψ <~> (¬ x))) :=
begin
  induction φ,
  repeat 
    {unfold cl at *,
    simp at hx,
    cases hx,
    { apply exists.intro (¬ x),
      simp [hx] at *,
      exact @iff_iden' (formCLC agents) _ _ _, },},
  { { apply exists.intro (bot),
      simp[hx] at *,
      apply axCLC.MP,
      apply axCLC.MP,
      apply axCLC.Prop4,
      exact @dni (formCLC agents) _ _ _,
      exact @nnn_bot (formCLC agents) _ _, }, },
  { { apply exists.intro (var φ),
      simp[hx] at *,
      exact @iff_dni (formCLC agents) _ _ _, }, },
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
      { apply exists.intro (φ_φ & φ_ψ),
        simp[hx],
        exact @iff_dni (formCLC agents) _ _ _, }, },
  { unfold cl at *,
    simp at hx,
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
      { simp[h] at *,
        simp[hx],
        apply exists.intro (φ_φ),
        split,
        apply or.intro_left,
        exact cl_contains_phi φ_φ,
        exact @iff_dni (formCLC agents) _ _ _, },
      { simp[h] at *,
        cases hx,
        { apply exists.intro (¬ (φ_φ ~> φ_ψ)),
          simp[hx],
          exact @iff_iden' (formCLC agents) _ _ _, },
        { apply exists.intro (φ_φ ~> φ_ψ),
          simp[hx],
          exact @iff_dni (formCLC agents) _ _ _, }, }, }, },
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
    { apply exists.intro (([φ_G] φ_φ)),
      simp[hx],
      exact @iff_dni (formCLC agents) _ _ _, },
    split_ifs at hx,
    { by_contradiction,
      assumption, },
    { simp[h],
      simp at hx,
      cases hx,
      { apply exists.intro (¬ (c φ_G ([φ_G]φ_φ))),
        simp[hx],
        exact @iff_iden' (formCLC agents) _ _ _, },
      cases hx,
      { apply exists.intro (c φ_G ([φ_G]φ_φ)),
        simp[hx],
        exact @iff_dni (formCLC agents) _ _ _, },
      { unfold cl_C at *,
        simp at hx,
        cases hx, 
        { cases hx with i hi,
          apply exists.intro (¬ k i (c φ_G ([φ_G]φ_φ))),
          simp[hi.left, ←hi.right],
          exact @iff_iden' (formCLC agents) _ _ _, },
        { cases hx with i hi,
          apply exists.intro (k i (c φ_G ([φ_G]φ_φ))),
          simp[hi.left, ←hi.right],
          exact @iff_dni (formCLC agents) _ _ _, }, }, }, },
  { cases hx,
    { specialize φ_ih hx,
      cases φ_ih with ψ hψ,
      apply exists.intro ψ,
      split,
      apply finset.mem_union_left,
      exact hψ.1,
      exact hψ.2, },
    { apply exists.intro (k φ_a φ_φ),
      simp[hx],
      exact @iff_dni (formCLC agents) _ _ _, }, },
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
    { apply exists.intro ((e φ_G (φ_φ))),
      simp[hx],
      exact @iff_dni (formCLC agents) _ _ _, },
    { unfold cl_E at *,
      simp at hx,
      cases hx,
      { cases hx with i hi,
        apply exists.intro (¬ k i φ_φ),
        simp[hi.left, ←hi.right],
        exact @iff_iden' (formCLC agents) _ _ _, },
      { cases hx with i hi,
        apply exists.intro (k i φ_φ),
        simp[hi.left, ←hi.right],
        exact @iff_dni (formCLC agents) _ _ _, }, }, },
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
    { apply exists.intro ((c φ_G (φ_φ))),
      simp[hx],
      exact @iff_dni (formCLC agents) _ _ _, },
    { unfold cl_C at *,
      simp at hx,
      cases hx,
      { cases hx with i hi,
        apply exists.intro (¬ k i (c φ_G φ_φ)),
        simp[hi.left, ←hi.right],
        exact @iff_iden' (formCLC agents) _ _ _, },
      { cases hx with i hi,
        apply exists.intro (k i (c φ_G φ_φ)),
        simp[hi.left, ←hi.right],
        exact @iff_dni (formCLC agents) _ _ _, }, }, },
end


inductive subformula {agents : Type} : formCLC agents → formCLC agents → Prop
| refl (φ) : subformula φ φ
| trans {φ ψ χ} : subformula φ ψ → subformula ψ χ → subformula φ χ
| and_left (φ ψ) : subformula φ (φ & ψ)
| and_right (φ ψ) : subformula ψ (φ & ψ)
| imp_left (φ ψ) : subformula φ (φ ~> ψ)
| imp_right (φ ψ) : subformula ψ (φ ~> ψ)
| effectivity (G) (φ) : subformula φ ([G] φ)
| knows (i) (φ) : subformula φ (k i φ)
| everyone_knows (G) (φ) : subformula φ (e G φ)
| common_know (G) (φ) : subformula φ (c G φ)

lemma subformula.cl_subset_and_left {agents : Type} [ha : nonempty agents] [hN : fintype agents]
  {φ ψ : formCLC agents} : cl φ ⊆ cl (φ & ψ) :=
begin
  intros x h,
  induction φ,
  repeat
  { simp [cl] at *,
    repeat {cases h, simp [h],},
    {simp [h], }, },
end

lemma subformula.cl_subset_and_right {agents : Type} [ha : nonempty agents] [hN : fintype agents]
  {φ ψ : formCLC agents} : cl ψ ⊆ cl (φ & ψ) :=
begin
  intros x h,
  induction φ,
  repeat
  { simp [cl] at *,
    repeat {cases h, simp [h],},
    {simp [h], }, },
end

lemma subformula.cl_subset_imp_left {agents : Type} [ha : nonempty agents] [hN : fintype agents]
  {φ ψ : formCLC agents} : cl φ ⊆ cl (φ ~> ψ) :=
begin
  intros x h,
  induction φ,
  repeat
  { simp [cl] at *,
    repeat {cases h, simp [h],},
    {simp [h], }, },
end

lemma subformula.cl_subset_imp_right {agents : Type} [ha : nonempty agents] [hN : fintype agents]
  {φ ψ : formCLC agents} : cl ψ ⊆ cl (φ ~> ψ) :=
begin
  intros x h,
  induction φ,
  repeat
  { simp [cl] at *,
    repeat {cases h, simp [h],},
    {simp [h], }, },
end

lemma subformula.cl_subset_effectivity {agents : Type} [ha : nonempty agents] [hN : fintype agents]
  {φ : formCLC agents} {G : set (agents)} : cl φ ⊆ cl ([G] φ) :=
begin
  intros x h,
  induction φ,
  repeat
  { simp [cl] at *,
    repeat {cases h, simp [h],},
    {simp [h], }, },
end

lemma subformula.cl_subset_knows {agents : Type} [ha : nonempty agents] [hN : fintype agents]
  {φ : formCLC agents} {i : agents}  : cl φ ⊆ cl (k i φ) :=
begin
  intros x h,
  induction φ,
  repeat
  { simp [cl] at *,
    repeat {cases h, simp [h],},
    {simp [h], }, },
end

lemma subformula.cl_subset_everyone_knows {agents : Type} [ha : nonempty agents] [hN : fintype agents]
  {φ : formCLC agents} {G : set (agents)} : cl φ ⊆ cl (e G φ) :=
begin
  intros x h,
  induction φ,
  repeat
  { simp [cl] at *,
    repeat {cases h, simp [h],},
    {simp [h], }, },
end

lemma subformula.cl_subset_common_know {agents : Type} [ha : nonempty agents] [hN : fintype agents]
  {φ : formCLC agents} {G : set (agents)} : cl φ ⊆ cl (c G φ) :=
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
  { exact subformula.cl_subset_everyone_knows, },
  { exact subformula.cl_subset_common_know, },
end

lemma subformula.mem_cl {agents : Type} [ha : nonempty agents] [hN : fintype agents]
  {φ ψ : formCLC agents} (h : subformula φ ψ) : φ ∈ cl ψ :=
h.cl_subset (cl_contains_phi φ)


