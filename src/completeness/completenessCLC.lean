import soundness.soundnessCLC
import completeness.canonicalCL
import syntax.axiomsCLC
import syntax.consistency_lemmas
import syntax.CLClemmas
import tactic.induction
import data.finset.powerset


local attribute [instance] classical.prop_decidable

open set formCLC

namespace canonical


----------------------------------------------------------
-- Canonical CL Model (not a valid CLC model)
----------------------------------------------------------
@[simps?] def canonical_model_CLC (agents : Type) [hN : fintype agents] [ha : nonempty agents] : 
  modelCLK agents :=
{ f := canonical_CLK ha (formCLC agents) (nprfalseCLC ha),
  -- V is as usual, such that s ∈ V (p) iff p ∈ s
  v := λ  n, {s | (formCLC.var n) ∈ s.1} }

/-- Allows us to write `φ ∈ s` instead of `φ ∈ s.val` -/
instance states.set_like {agents : Type} [hN : fintype agents] [ha : nonempty agents] :
  set_like (canonical_model_CLC agents).1.states (formCLC agents) :=
{ coe := λ s, s.1,
  coe_injective' := subtype.coe_injective }

@[simp] lemma states.val_eq_coe {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  (s : (canonical_model_CLC agents).1.states) : s.1 = s := rfl

  @[simp] lemma set_like.set_of_mem {S A : Type*} [h : set_like S A] (s : S) : {x | x ∈ s} = s := rfl



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

-- def E_list_to_form {agents : Type} (φ : formCLC agents) : 
--   list (agents) → formCLC agents
-- | list.nil  := ⊤
-- | (i :: is) := (k i φ) & (E_list_to_form is)

-- def cl_E_list {agents : Type} (φ : formCLC agents) : 
--   list (agents) → set (formCLC agents)
-- | list.nil  := ∅ 
-- | (i :: is) := {(k i φ), (¬ (k i φ))} ∪ (cl_E_list is)

noncomputable def cl_E {agents : Type} [hN : fintype agents] (G : set (agents)) (φ : formCLC agents) : 
  finset (formCLC agents) := 
finset.image (λ i, k i φ) (to_finset G) ∪ finset.image (λ i, (¬ (k i φ))) (to_finset G)

-- noncomputable def cl_imp {agents : Type} : 
--   formCLC agents → formCLC agents → finset (formCLC agents)
-- | φ bot  := {(imp φ bot)}
-- | φ ψ    := {(imp φ ψ), ¬ (imp φ ψ)} 

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

----------------------------------------------------------
-- Filtering S
----------------------------------------------------------
-- Definitions about Sf
----------------------------------------------------------
def S_f {agents : Type} [hN : fintype agents] [ha : nonempty agents] (φ : formCLC agents) : Type :=
finset.attach (finset.filter (λ sf, ∃ s: (canonical_model_CLC agents).f.states, (s.1 ∩ {x | x ∈ cl(φ)}) = {x | x ∈ sf}) (finset.powerset (cl(φ))))

instance {agents : Type} [hN : fintype agents] [ha : nonempty agents] (φ : formCLC agents) :
  set_like (S_f φ) (formCLC agents) :=
{ coe := λ sf, sf.1.1,
  coe_injective' := λ x y h, subtype.coe_injective (subtype.coe_injective (by simpa using h)) }

@[simp] lemma coe_eq_coe_coe_val {agents : Type} [hN : fintype agents] {ha : nonempty agents} {φ : formCLC agents}
  (sf : S_f φ) : (sf : set (formCLC agents)) = (sf.1 : finset (formCLC agents)) :=
rfl

@[simp] lemma mem_mk {agents : Type} [hN : fintype agents] [ha : nonempty agents] {φ : formCLC agents}
  {x : formCLC agents} {s} (hs₁ hs₂) : @has_mem.mem _ (S_f φ) _ x ⟨⟨s, hs₁⟩, hs₂⟩ ↔ x ∈ s :=
iff.rfl

-- get sf from s
noncomputable def s_f {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (s : (canonical_model_CLC agents).f.states) : 
  (S_f φ) :=
begin
  fconstructor,
  fconstructor,
  exact finset.filter (λ ψ, ψ ∈ s) (cl(φ)),
  simp,
  apply exists.intro s,
  exact s.1.inter_comm ↑(cl φ),
  simp,
end

def s_to_s_f {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  (φ : formCLC agents) (s : (canonical_model_CLC agents).f.states) : 
  ∃ sf : (S_f φ), ∀ {x}, x ∈ sf ↔ x ∈ s.1 ∧ x ∈ cl φ  :=
begin
  fconstructor,
  fconstructor,
  fconstructor,
  { exact finset.filter (λ ψ, ψ ∈ s) (cl(φ)), },
  { simp,
    apply exists.intro s,
    exact s.1.inter_comm ↑(cl φ), },
  { simp, },
  { intro x,
    simp,
    exact and.comm, },
end

/-
-- for each sf, there exists some s which filters to sf
def s_f_to_s {agents : Type} [ha : nonempty agents] [hN : fintype agents] (φ : formCLC agents) 
  (sf : (S_f φ)) :
  ∃ s: (canonical_model_CLC agents).f.states, (s.1 ∩ {x | x ∈ cl(φ)}) = {x | x ∈ sf.1.1} :=
begin
  cases sf.1 with sfin hsf,
  dsimp[finset.powerset, finset.filter] at *,
  simp at *,
  exact hsf.right,
end
-/

-- for each sf, there exists some s which filters to sf
def s_f_to_s {agents : Type} [ha : nonempty agents] [hN : fintype agents] (φ : formCLC agents) 
  (sf : (S_f φ)) :
  ∃ s: (canonical_model_CLC agents).f.states, ∀ {x}, x ∈ sf ↔ x ∈ s.1 ∧ x ∈ cl φ :=
begin
  rcases sf with ⟨⟨sfin, hsf₁⟩, hsf₂⟩,
  rcases finset.mem_filter.mp hsf₁ with ⟨hsf₁₁, s, hs⟩,
  use s,
  simpa [set.ext_iff, iff.comm] using hs
end

-- -- for each sf, there exists some s which filters to sf
-- def s_f_s_iff {agents : Type} [ha : nonempty agents] [hN : fintype agents] (φ : formCLC agents) 
--   (sf : (S_f φ)) (s : (canonical_model_CLC agents).f.states) (h : ∀ {x}, x ∈ sf ↔ x ∈ s.1 ∧ x ∈ cl φ):
--   ∃ s: (canonical_model_CLC agents).f.states, ∀ {x}, x ∈ sf ↔ x ∈ s.1 ∧ x ∈ cl φ :=
-- begin
--   rcases sf with ⟨⟨sfin, hsf₁⟩, hsf₂⟩,
--   rcases finset.mem_filter.mp hsf₁ with ⟨hsf₁₁, s, hs⟩,
--   use s,
--   simpa [set.ext_iff, iff.comm] using hs
-- end

-- Lemmas about Sf
----------------------------------------------------------
-- Sf is  finite
noncomputable instance fin_S_f {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) : 
  fintype (S_f φ) :=  additive.fintype

-- Sf is not empty
instance nonempty_S_f {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) :
  nonempty (S_f φ) :=
begin
  -- simp[S_f, finset.filter],
  have hs := (canonical_model_CLC agents).f.hs,
  cases hs with s,
  have sf := s_f φ s,
  exact nonempty.intro sf,
end

-- sf ⊆ s
lemma s_f_subset_s {agents : Type} [ha : nonempty agents] [hN : fintype agents] 
  (φ : formCLC agents) (s : (canonical_model_CLC agents).f.states) :
  {x | x ∈ (s_f φ s)} ⊆ s :=
begin
  simp[s_f],
  apply inter_subset_right,
end

-- sf ⊆ cl φ
lemma s_f_subset_cl {agents : Type} [ha : nonempty agents] [hN : fintype agents] 
  (φ : formCLC agents) (sf : (S_f φ)) : 
  (sf.1 : finset (formCLC agents)) ⊆ cl φ :=
begin
  cases sf,
  cases sf_val,
  dsimp at *,
  simp[finset.has_mem] at *,
  simp[←finset.val_inj] at *,
  exact sf_val_property.left,
end

-- all sf are consistent
lemma s_f_ax {agents : Type} [ha : nonempty agents] [hN : fintype agents] 
  (φ : formCLC agents) (sf : (S_f φ)) : 
  ax_consistent {x | x ∈ sf} :=
begin
  cases (s_f_to_s φ sf) with s hs,
  have hax := s.2.1,
  simp [ax_consistent] at *,
  intros fs hsfin,
  apply hax fs, 
  intros ψ hψfs,
  have hsfs : ∀ x ∈ sf, x ∈ s, from
  begin
    intros x hx,
    rw hs at hx,
    exact hx.1,
  end,
  apply hsfs,
  apply hsfin,
  exact hψfs,
end

-- sf = tf iff they have the same finset
lemma s_f_eq {agents : Type} [ha : nonempty agents] [hN : fintype agents] 
  (φ : formCLC agents) (sf tf : (S_f φ)) : 
  sf = tf ↔ sf.1.1 = tf.1.1 :=
begin
  split,
   repeat 
   { intro h,
    cases sf, cases tf,
    cases sf_val, cases tf_val,
    simp at *,
    exact h, },
end

-- ψ ∈ s → ψ ∈ cl(φ) → ψ ∈ sf
lemma s_f_contains {agents : Type} [ha : nonempty agents] [hN : fintype agents] 
  (φ ψ : formCLC agents) (sf : (S_f φ)) (s : (canonical_model_CLC agents).f.states)
  (hs : ∀ {x}, x ∈ sf ↔ x ∈ s ∧ x ∈ cl φ) :
  ψ ∈ s → ψ ∈ cl(φ) → ψ ∈ sf :=
begin
  intros h1 h2,
  exact hs.mpr ⟨h1, h2⟩
end

-- (ψ ∉ s) ∨ (ψ ∉ cl(φ)) → ψ ∉ sf
lemma s_f_n_contains {agents : Type} [ha : nonempty agents] [hN : fintype agents] 
  (φ ψ : formCLC agents) (sf : (S_f φ)) (s : (canonical_model_CLC agents).f.states)
  (hs : ∀ {x}, x ∈ sf ↔ x ∈ s ∧ x ∈ cl φ) :
  (ψ ∉ s ∨ ψ ∉ cl(φ)) → ¬ ψ ∈ sf :=
begin
  intro h1,
  rwa [hs, not_and_distrib]
end

-- ψ ∈ cl φ ⇒ ((∀ sf, ψ ∉ sf) ⇔ (⊢ ψ ↔ ⊥))
lemma S_f_empty_iff_false_sf {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  {φ ψ : formCLC agents} (hψ : ψ ∈ cl φ) (hempty : {sf : (S_f φ) | ψ ∈ sf} = ∅) : 
  axCLC (ψ ↔' ⊥) :=
begin
  apply @set_empty_iff_false (formCLC agents),
  rw subset_empty_iff,
  rw eq_empty_iff_forall_not_mem at *,
  intros s hf,
  have hsf := s_to_s_f φ s,
  cases hsf with sf hsf,
  apply hempty sf (hsf.mpr (and.intro hf hψ)),
end

-- x ∉ sf ⇒ ∃ y ∈ sf, ⊢ (y ↔ ¬ x)
lemma s_f_closed {agents : Type} [hN : fintype agents] [ha : nonempty agents]  
  {φ x : formCLC agents} {sf : (S_f φ)} (hnf : x ∉ sf) (hx : x ∈ cl φ)  :
  ∃ y, y ∈ sf ∧ axCLC (y <~> ¬ x) :=
begin
  -- χ ∉ t, from 5, by definition Sf , because χ ∈ cl(φ).
  have hs := s_f_to_s φ sf, cases hs with s hs, simp at hs,
  have hn : x ∉ s, from
  begin
      by_contradiction hf,
      apply hnf,
      exact hs.mpr ⟨hf, hx⟩,
  end,
  -- ¬χ ∈ t, from hn, because s and t are maximally consistent.
  have hnx : ((¬' x) ∈ s.1) := not_in_from_notin s.2 hn,
  -- ∃ψ, (ψ ↔ ¬χ) ∧ (ψ ∈ cl(φ)), because cl is closed under single negations.
  have hy := cl_closed_single_neg φ x hx,
  cases hy with y hy,
  -- ψ ∈ s ∨ ψ ∈ t, from hnx & hy, because s and t are maximally consistent.
  have hst : y ∈ s, from
  begin
    apply max_ax_contains_by_set_proof s.2 hnx,
    apply @iff_r (formCLC agents) _ _,
    exact hy.2,
  end,
  -- ψ ∈ sf ∨ ψ ∈ tf , from hst & hy, by definition Sf .
  have hst : y ∈ sf := hs.mpr ⟨hst, hy.1⟩,
  apply exists.intro y,
  split,
  exact hst,
  exact hy.right,
end 

@[simp] lemma set_of_S_f {agents : Type} [ha : nonempty agents] [hN : fintype agents]
  {φ ψ : formCLC agents} (sf : S_f φ) :
  sf ∈ {sf : S_f φ | ψ ∈ sf} ↔ (ψ ∈ sf) := mem_set_of

----------------------------------------------------------
-- Definitions and Lemmas needed for completness / model construction
----------------------------------------------------------
-- Tilde
----------------------------------------------------------
def tilde {agents : Type} [hN : fintype agents] [ha : nonempty agents] (ψ : formCLC agents) : 
  set ((canonical_model_CLC agents).f.states) :=
{s : (canonical_model_CLC agents).f.states | ψ ∈ s}

lemma h_tilde_compl {agents : Type} [hN : fintype agents] [ha : nonempty agents] (ψ : formCLC agents) : 
  tilde (¬ ψ) = (tilde ψ)ᶜ := 
begin
  ext,
  simp[tilde],
  split,
  { intros hx hf,
    exact contra_containts_pr_false x.2 hf hx, },
  { intros hx,
    exact not_in_from_notin x.2 hx, },
end

-- phi sf
----------------------------------------------------------
noncomputable def phi_s_f {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (sf : S_f φ) : formCLC agents :=
finite_conjunction (finset.to_list (sf.1))

-- phi sf ∈ s
lemma phi_s_f_in_s {agents : Type} [hN : fintype agents] [ha : nonempty agents] (φ : formCLC agents)
  (s : (canonical_model_CLC agents).f.states):
  phi_s_f φ ((s_f φ s)) ∈ s :=
begin
  simp[phi_s_f],
  have hinduct : ∀ fs : list (formCLC agents), 
    (fs ⊆ ((s_f φ s).1 : finset (formCLC agents)).to_list) → finite_conjunction fs ∈ s, from
  begin
    intros fs hfs,
    induction fs with f fs ih,
    { simp[finite_conjunction],
      exact @max_ax_contains_by_empty_proof (formCLC agents) _ _ _ _ s.prop prtrue, },
    { simp[finite_conjunction] at *,
      cases hfs with hf hfs,
      have hf_in_s : f ∈ s, from s_f_subset_s φ s hf,
      have hfs_in_s : finite_conjunction fs ∈ s, from ih hfs,
      apply max_ax_contains_by_set_proof_2h s.2 hf_in_s hfs_in_s,
      exact axCLC.Prop4, },
  end,
  apply hinduct,
  simp,
end

lemma phi_s_f_forall_iff {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  {φ : formCLC agents} (sf : S_f φ) : 
  (∀ x : formCLC agents, x ∈ sf → axCLC x) ↔ axCLC (phi_s_f φ sf) :=
begin
  unfold phi_s_f,
  have h_con := @finite_conj_forall_iff (formCLC agents) _ _ (sf.1.1).to_list,
  split,
  { intro h,
    apply h_con.mp,
    intros x hx,
    apply h,
    have hx : x ∈ sf.1.1, from (multiset.mem_to_list x _).mp hx,
    exact hx, },
  { intros h x hx,
    apply h_con.mpr,
    exact h,
    rw multiset.mem_to_list,
    exact hx, },
end

lemma phi_s_f_forall_imp {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  {φ : formCLC agents} (sf : S_f φ) : 
  (∀ x ∈ sf, axCLC ((phi_s_f φ sf) ~> x)) :=
begin
  unfold phi_s_f,
  intros x hx,
  have hx : x ∈ sf.1.1.to_list, from (multiset.mem_to_list x _).mpr hx,
  exact @finite_conj_forall_imp (formCLC agents) _ _ (sf.1.1).to_list x (hx),
end

lemma phi_s_f_conj_contains_ax {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  {φ ψ : formCLC agents} (sf : S_f φ) (hψ : ψ ∈ sf) : 
  axCLC (phi_s_f φ sf) ↔ axCLC (ψ & (phi_s_f φ sf)) :=
begin
  split,
  { intro h,
    apply @and_ax (formCLC agents),
    exact (phi_s_f_forall_iff sf).mpr h ψ hψ,
    exact h, },
  { intro h,
    apply and.elim_right,
    apply (@ax_and (formCLC agents) _ _ ψ (phi_s_f φ sf)).mp,
    exact h, },
end

lemma phi_s_f_conj_contains {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  {φ ψ : formCLC agents} (sf : S_f φ) (hψ : ψ ∈ sf) : 
  axCLC ((phi_s_f φ sf) <~> (ψ & (phi_s_f φ sf))) :=
begin
  apply @ax_iff_intro (formCLC agents),
  { apply imp_imp_and,
    exact phi_s_f_forall_imp _ _ hψ,
    exact iden, },
  { refine imp_and_r _,
    exact iden, },
end

-- phi X (given a list)
----------------------------------------------------------
noncomputable def phi_X_list {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) :
  list (S_f φ) → list (formCLC agents)
| list.nil   := list.nil
| (sf :: ss) := ((phi_s_f φ sf) :: phi_X_list ss)

-- if sf ∈ X, then phi sf is one of the disjuncts in phi X.
lemma phi_X_list_contains {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (sfs : list (S_f φ)) (sf : (S_f φ)) (hs : sf ∈ sfs) :
  (phi_s_f φ sf) ∈ phi_X_list φ sfs :=
begin
  induction sfs with hd sfs ih,
  {by_contradiction, simp at *, exact hs, },
  { cases hs,
    { simp[hs, phi_X_list], },
    { simp[phi_X_list] at *,
      apply or.intro_right,
      exact ih hs, }, },
end

lemma phi_X_list_subset {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (sfs : list (S_f φ)) (sfs' : list (S_f φ)) (h : sfs ⊆ sfs') :
  phi_X_list φ sfs ⊆ phi_X_list φ sfs' :=
begin
  induction sfs with hd sfs ih,
  { simp[phi_X_list], },
  { simp[phi_X_list] at *,
    split,
    { exact phi_X_list_contains φ _ _ h.left, },
    { exact ih h.right, }, },
end

lemma phi_X_list_append {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : list (S_f φ)) :
  phi_X_list φ (X ++ Y) ⊆ phi_X_list φ X ++ phi_X_list φ Y :=
begin
  induction X with hd X ih,
  { simp[phi_X_list], },
  { simp[phi_X_list] at *,
    exact list.subset_cons_of_subset (phi_s_f φ hd) ih, },
end

lemma phi_X_list_single {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (sf : (S_f φ)) :
  axCLC ((phi_s_f φ sf) ↔' finite_disjunction (phi_X_list φ (sf :: list.nil))) :=
begin
  apply @ax_iff_intro (formCLC agents),
  { unfold phi_X_list finite_disjunction,
    apply cut,
    exact dni,
    exact iden, },
  { unfold phi_X_list finite_disjunction,
    exact dne, },
end

lemma phi_X_list_conj_contains {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  {φ ψ : formCLC agents} (X : list (S_f φ)) (hψ : ∀ sf, sf ∈ X → ψ ∈ sf) : 
  axCLC (finite_disjunction (phi_X_list φ X) <~> (ψ & finite_disjunction (phi_X_list φ X))) :=
begin
  induction X with sf X ih,
  { simp [phi_X_list, finite_disjunction],
    apply @and_ax (formCLC agents),
    exact explosion,
    exact imp_and_r iden, },
  { simp [phi_X_list, finite_disjunction],
    apply @and_ax (formCLC agents),
    { apply or_cases,
      { apply imp_imp_and,
        { apply cut,
          apply iff_l,
          apply phi_s_f_conj_contains sf,
          apply hψ,
          simp,
          exact p5 _ _, },
        { exact contra_explosion, }, },
      { have hψ' : ∀ sf, sf ∈ X → ψ ∈ sf, from
        begin
          intros tf htf,
          apply hψ,
          simp [htf],
        end,
        specialize ih hψ',
        have ih := (@ax_and (formCLC agents) _ _ _ _).mp ih,
        apply imp_imp_and,
        { apply cut,
          exact ih.left,
          exact p5 _ _, },
        { exact p1 _ _, }, }, },
      { exact p6 _ _, }, },
end

-- phi X (given a finset)
----------------------------------------------------------
noncomputable def phi_X_finset {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X : finset (S_f φ)) :
  formCLC agents :=
finite_disjunction (phi_X_list φ (finset.to_list X))

lemma phi_X_subset_Y_imp {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : finset (S_f φ)) (hXY : X ⊆ Y) :
  axCLC ((phi_X_finset φ X) →' (phi_X_finset φ Y)) :=
begin
  simp[phi_X_finset],
  apply imp_finite_disjunction_subset (phi_X_list φ X.to_list) (phi_X_list φ Y.to_list),
  apply phi_X_list_subset,
  intros f hf,
  rw finset.mem_to_list at *,
  exact hXY hf,
end

lemma phi_X_list_append' {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : finset (S_f φ)) :
  phi_X_list φ X.to_list ++ phi_X_list φ Y.to_list ⊆ phi_X_list φ (X ∪ Y).to_list :=
begin
  simp at *,
  split,
  { apply phi_X_list_subset,
    intros f hf,
    rw finset.mem_to_list at *,
    exact finset.mem_union_left Y hf, },
 {  apply phi_X_list_subset,
    intros f hf,
    rw finset.mem_to_list at *,
    exact finset.mem_union_right X hf, }, 
end

lemma phi_X_list_append'' {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : finset (S_f φ)) :
  phi_X_list φ (X ∪ Y).to_list ⊆ phi_X_list φ X.to_list ++ phi_X_list φ Y.to_list :=
begin
  have h1 := phi_X_list_append φ X.to_list Y.to_list,
  have h2 : phi_X_list φ (X ∪ Y).to_list ⊆ phi_X_list φ (X.to_list ++ Y.to_list), from
  begin
    refine phi_X_list_subset φ (X ∪ Y).to_list (X.to_list ++ Y.to_list) _,
    intros f hf,
    simp at *,
    exact hf,
  end,
  exact subset.trans h2 h1,
end

lemma phi_X_finset_union {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : finset (S_f φ)) :
  axCLC ((¬' (phi_X_finset φ X) →' (phi_X_finset φ Y)) →' (phi_X_finset φ (X ∪ Y))) :=
begin
  simp[phi_X_finset],
  apply @cut (formCLC agents),
  apply disjunc_disjunct,
  apply imp_finite_disjunction_subset,
  apply phi_X_list_append',
end

lemma phi_X_finset_disjunct_of_disjuncts {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : finset (S_f φ)) :
  axCLC (¬' (phi_X_finset φ X) →' (phi_X_finset φ Y)) ↔ axCLC (phi_X_finset φ (X ∪ Y)) :=
begin
  have hax := @ax_iff_disjunc_disjunct (formCLC agents) _ _
              (phi_X_list φ X.to_list) (phi_X_list φ Y.to_list),
  simp[phi_X_finset],
  split,
  { intro h,
    apply @MP' (formCLC agents),
    apply hax.mp h,
    apply imp_finite_disjunction_subset,
    apply phi_X_list_append', },
  { intro h,
    apply hax.mpr,
    apply @MP' (formCLC agents),
    apply h,
    apply imp_finite_disjunction_subset,
    apply phi_X_list_append'',
  },
end

-- lemma phi_X_list_conj_contains {agents : Type} [hN : fintype agents] [ha : nonempty agents]
--   {φ ψ : formCLC agents} (X : finset (S_f φ)) (hψ : ∀ sf ∈ X, ψ ∈ sf) : 
--   axCLC (ψ & (phi_X_finset φ X)) :=
-- begin
--   unfold phi_X_finset,
-- end



-- phi X (given a set)
----------------------------------------------------------

/-- `phi_X_set φ X` is a finite disjunction of all elements of `X`. -/
noncomputable def phi_X_set {agents : Type} [hN : fintype agents] [ha : nonempty agents]  
  (φ : formCLC agents) (X : set (S_f φ)) :
  formCLC agents :=
begin
  simp[S_f, finset.attach] at X,
  have hX : finite X, from finite.of_fintype X,
  have X : finset (S_f φ), from finite.to_finset hX,
  exact phi_X_finset φ X,
end

lemma phi_X_set_subset_Y_imp {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X : set (S_f φ)) (Y : set (S_f φ)) (hXY : X ⊆ Y) :
  axCLC ((phi_X_set φ X) →' (phi_X_set φ Y)) :=
begin
  simp[phi_X_set],
  apply phi_X_subset_Y_imp,
  exact finite.to_finset_mono.mpr hXY,
end

lemma phi_X_set_disjunct {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : set (S_f φ)) :
  axCLC ((¬' (phi_X_set φ X) →' (phi_X_set φ Y)) →' (phi_X_set φ (X ∪ Y))) :=
begin
  unfold phi_X_set,
  apply @cut (formCLC agents),
  apply phi_X_finset_union,
  apply phi_X_subset_Y_imp,
  apply finset.union_subset,
  repeat { simp,},
end

lemma phi_X_set_disjunct_of_disjuncts {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : set (S_f φ)) :
  axCLC (¬' (phi_X_set φ X) →' (phi_X_set φ Y)) ↔ axCLC (phi_X_set φ (X ∪ Y)) :=
begin
  unfold phi_X_set,
  split,
  { intro h,
    have hax := (phi_X_finset_disjunct_of_disjuncts φ _ _).mp,
    specialize hax h,
    apply @MP' (formCLC agents),
    apply hax,
    apply phi_X_subset_Y_imp,
    apply finset.union_subset,
    repeat { simp, }, },
  { intro h,
    apply (phi_X_finset_disjunct_of_disjuncts φ _ _).mpr,
    apply @MP' (formCLC agents),
    apply h,
    apply phi_X_subset_Y_imp,
    refine finset.subset_iff.mpr _,
    intros f hf,
    simp at *,
    exact hf, },
end

-- Effectivity
----------------------------------------------------------
def E_f {agents : Type}  [hN : fintype agents] [ha : nonempty agents] {φ : formCLC agents} : 
  (S_f φ) → (set agents) → (set (set (S_f φ))) := 
λ sf G, {X | ite (G = univ) 
  -- condition G = N
  -- ∃t ∈ S, sf = tf and  ̃φX ∈ E(t)(N)
  (∃ t : (canonical_model_CLC agents).f.states, (∀ {x}, x ∈ sf ↔ x ∈ t ∧ x ∈ cl φ) ∧ 
    (tilde (phi_X_set φ X)) ∈ (canonical_model_CLC agents).f.E.E (t) (G))
  -- condition G ≠ N
  -- ∀t ∈ S, sf = tf ⇒  ̃phiX ∈ E(t)(G)
  (∀ t : (canonical_model_CLC agents).f.states, (∀ {x}, x ∈ sf ↔ x ∈ t ∧ x ∈ cl φ) → 
    (tilde (phi_X_set φ X)) ∈ (canonical_model_CLC agents).f.E.E (t) (G))}

section lemmas

-- Motivation: self-contained `have`-block
@[simp] lemma tilde_empty {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  {φ : formCLC agents} : (tilde (phi_X_set φ ∅)) = ∅ :=
begin
  -- 1.1.1. φ∅ = ⊥, because φ∅ is an empty disjunction, thus  ̃φ∅ =  ̃⊥.
  simp [phi_X_set, phi_X_finset, phi_X_list, finite_disjunction, tilde],
  -- 1.1.2.  ̃⊥ = ∅, because all s ∈ S are consistent.
  simp [eq_empty_iff_forall_not_mem],
  intro s,
  exact bot_not_mem_of_ax_consistent s.1 s.2.1
end

lemma tilde_ax_iff {agents : Type} [hN : fintype agents] [ha : nonempty agents] (φ : formCLC agents)
  {ψ χ : formCLC agents} (hax : axCLC (ψ <~> χ)) : 
  tilde ψ = tilde χ :=
begin
  unfold tilde,
  ext1 s,
  split,
  { intro hs,
    simp at *,
    apply max_ax_contains_by_set_proof s.2 hs,
    apply iff_l,
    apply hax, },
  { intro hs,
    simp at *,
    apply max_ax_contains_by_set_proof s.2 hs,
    apply iff_r,
    apply hax, },
end

-- Motivation: simple way to prove `phi_X_set`
lemma ax_phi_s_f_imp_phi_X_set_of_mem {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  {φ : formCLC agents} {t} {X : set _} (h : s_f φ t ∈ X) :
  ax (phi_s_f φ (s_f φ t) →' phi_X_set φ X) :=
begin
  simp [phi_X_set],
  apply @imp_finite_disjunction (formCLC agents) _ _ (phi_s_f φ (s_f φ t)),
  apply phi_X_list_contains φ,
  simpa,
end

lemma ax_phi_s_f_imp_phi_X_set_of_mem' {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  {φ : formCLC agents} {sf} {X : set _} (h : sf ∈ X) :
  ax (phi_s_f φ (sf) →' phi_X_set φ X) :=
begin
  simp [phi_X_set],
  apply @imp_finite_disjunction (formCLC agents) _ _ (phi_s_f φ (sf)),
  apply phi_X_list_contains φ,
  simpa,
end


-- Main Lemmas
----------------------------------------------------------
-- Lemma 4. ⊢ (∨ {sf ∈Sf } φsf)
lemma univ_disjunct_provability {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  (φ : formCLC agents) (hs : nonempty (S_f φ)):
  ax (phi_X_set φ (univ : set (S_f φ))) :=
begin
  -- 1. By contradiction, assume that ⊬ (∨ {sf ∈Sf } φsf)
  by_contradiction,
  -- 3. ¬(∨ {sf ∈Sf } φsf) ∈ t, because t is maximally consistent, from 1.
  obtain ⟨t', hexn, htn⟩ := exists_max_ax_consistent_neg_mem h,
  let t := (⟨t', hexn⟩ : (canonical_model_CLC agents).f.states),
  -- 4. ⊢ φtf → (∨ {sf ∈Sf } φsf ), by propositional logic, because t ∈ Sf.
  have himp : ax (phi_s_f φ (s_f φ t) →' phi_X_set φ univ),
    from ax_phi_s_f_imp_phi_X_set_of_mem (mem_univ _),
  -- 5. φtf∈ t, by propositional logic, because all ∀ψ ∈ tf , ψ ∈ t).
  have hphitf : phi_s_f φ (s_f φ t) ∈ t.1, from phi_s_f_in_s φ t, 
  -- 6. (∨{sf ∈Sf } φsf) ∈ t, by propositional logic, from 4 & 5.
  have ht : phi_X_set φ (univ : set (S_f φ)) ∈ t.1, 
    from max_ax_contains_by_set_proof t.2 hphitf himp,
  -- 7. Contradiction from 3 and 6.
  apply contra_containts_pr_false t.2 ht htn,
end

-- Motivation: self-contained `have`-block
-- 2.1. First we note that  ̃φSf =  ̃⊤ = S
@[simp] lemma tilde_univ {agents : Type} [hN : fintype agents] [ha : nonempty agents] {φ : formCLC agents} :
  (tilde (phi_X_set φ (univ : set (S_f φ)))) = (univ : set (canonical_model_CLC agents).f.states) :=
begin
  simp[tilde],
  ext1,
  refine iff_of_true _ trivial,
  simp,
  apply max_ax_contains_by_empty_proof x.2,
  apply univ_disjunct_provability,
  exact canonical.nonempty_S_f φ,
end

-- Lemma 5. ∀sf , tf ∈ Sf , sf ̸ = tf ⇒⊢ φsf→ ¬φtf
lemma unique_s_f_helper {agents : Type} [hN : fintype agents] [ha : nonempty agents]  
  {φ x : formCLC agents} (sf  tf : (S_f φ)) (hxf : x ∈ sf) (hnf : x ∉ tf) :
  axCLC (¬' (phi_s_f φ sf∧'phi_s_f φ tf)) := 
begin
  -- -- 6. χ /∈ t, from 5, by definition Sf , because χ ∈ cl(φ).
  -- -- 7. ¬χ ∈ t, from 6, because s and t are maximally consistent.
  -- -- 8. ∃ψ, (ψ ↔ ¬χ) ∧ (ψ ∈ cl(φ)), because cl is closed under single negations.
  -- -- 9. ψ ∈ s ∨ ψ ∈ t, from 7 & 8, because s and t are maximally consistent.
  -- -- 10. ψ ∈ sf ∨ ψ ∈ tf , from 8 & 9, by definition Sf .
  have hst := s_f_closed hnf (finset.subset_iff.mp (s_f_subset_cl φ _) hxf),
  cases hst with ψ hst,
  cases hst with hst hψ,
  -- 11. φsf ∧ φtf → ⊥, by propositional logic, from 5, 8 & 10.
  simp[phi_s_f],
  apply @contra_con_cons (formCLC agents) _ _,
  exact hψ,
  exact (sf.1.1).mem_to_list.mpr hxf,
  exact (tf.1.1).mem_to_list.mpr hst,
end

lemma unique_s_f {agents : Type} [hN : fintype agents] [ha : nonempty agents]  
  {φ : formCLC agents} (sf  tf : (S_f φ)) (hneq : sf ≠ tf) :
  ax (phi_s_f φ sf →' ¬' (phi_s_f φ tf)) :=
begin
  -- 1. Assume by contradiction ⊬ φsf → ¬φtf
  by_contradiction,
  -- 2. ∃u ∈ S, (φsf → ¬φtf) /∈ u, from 1.
  -- 3. ¬(φsf→ ¬φtf) ∈ u, from 2.
  obtain ⟨u', hexn.left, hun⟩ := exists_max_ax_consistent_neg_mem h,
  let u := (⟨u', hexn.left⟩ : (canonical_model_CLC agents).f.states),
  have hun : ¬' (phi_s_f φ sf →' ¬' (phi_s_f φ tf)) ∈ u.1, from by tauto,
  -- 4. φsf ∧ φtf ∈ u, by propositional logic, from 3.
  have hand : (phi_s_f φ sf ∧' (phi_s_f φ tf)) ∈ u.1,
    from max_ax_contains_by_set_proof u.2 hun demorgans'',
  -- 5. ∃χ ∈ sf ∪ tf , χ /∈ sf ∨ χ /∈ tf , because sf and tf are not identical.
  have : ¬(sf.1.1 ⊆ tf.1.1) ∨ ¬(tf.1.1 ⊆ sf.1.1), from
  begin
    { rw ← not_and_distrib,
      rintro ⟨hst, hts⟩,
      apply hneq,
      ext : 2,
      exact subset_antisymm hst hts },
  end,
    obtain ⟨x, hun, hneq'⟩ : ∃ f, f ∈ (sf.1.1 ∪ tf.1.1) ∧ ((f ∉ sf.1.1) ∨ (f ∉ tf.1.1)),
    { simp only [finset.not_subset] at this, -- Motivation: I recall `not_subset` had something like `x ∈ s ∧ ¬ x ∈ t` so I reworked the statement to make it come true.
      rcases this with ⟨x, hxu, hxn⟩ | ⟨x, hxu, hxn⟩;
        use x;
        simp only [finset.mem_union, hxu, hxn, not_true, not_false_iff, true_or, or_true, true_and] },
  rw finset.mem_union at hun,

  -- 11. φsf ∧ φtf → ⊥, from helper  (6-10)
  -- 12. ⊥ ∈ u, by propositional logic, from 4 & 11, which contradicts the consistency of u.
  apply ax_neg_containts_pr_false u.2 hand,
  cases hun with hxf hxf,
  { cases hneq' with hnf hnf,
    { finish, },
    { apply unique_s_f_helper _ _ hxf hnf, }, },
  { cases hneq' with hnf hnf,
    { apply cut (iff_l and_switch),
      apply unique_s_f_helper _ _ hxf hnf, },
    { finish, }, },
end

lemma phi_X_list_unique {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : list (S_f φ)) (hXY : X.disjoint Y) (hX : list.nodup X) (hY : list.nodup Y) :
  axCLC (finite_disjunction (phi_X_list φ X)→' ¬' (finite_disjunction (phi_X_list φ Y))) :=
begin
  induction' X with x X ihx,
  { simp [phi_X_list, finite_disjunction],
    apply @explosion (formCLC agents), },
  { simp [phi_X_list, finite_disjunction],
    apply @or_cases (formCLC agents),
    { induction Y with y Y ihy,
      { simp [phi_X_list, finite_disjunction],
        apply MP',
        apply not_bot,
        apply axCLC.Prop1, },
      { simp [phi_X_list, finite_disjunction] at *,
        rw ←contrapos,
        apply cut,
        apply dne,
        apply or_cases,
        apply unique_s_f, 
        by_contradiction,
        simp[h] at hXY,
        exact hXY,
        rw ←contrapos,
        apply cut,
        apply dne,
        apply ihy hY.right,
        exact hXY.2.1,
        exact hXY.2.2, }, },
    { apply ihx,
      exact hY,
      apply list.disjoint_of_disjoint_cons_left hXY,
      simp at hX,
      exact hX.2, }, },
end

lemma phi_X_finset_unique {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : finset (S_f φ)) (hXY : X ∩ Y = ∅) :
  axCLC ((phi_X_finset φ X) →' ¬' (phi_X_finset φ (Y))) :=
begin
  simp[phi_X_finset],
  apply phi_X_list_unique,
  rw list.disjoint_left,
  intros f hf,
  simp at *,
  by_contradiction,
  exact finset.eq_empty_iff_forall_not_mem.mp hXY f (finset.mem_inter_of_mem hf h),
  repeat {exact finset.nodup_to_list _, },
end

lemma phi_X_set_unique {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : set (S_f φ)) (hXY : X ∩ Y = ∅) :
  axCLC ((phi_X_set φ X) →' ¬' (phi_X_set φ (Y))) :=
begin
  simp[phi_X_set],
  apply phi_X_finset_unique,
  apply finset.eq_empty_iff_forall_not_mem.mpr,
  intros f hf,
  simp at *,
  exact eq_empty_iff_forall_not_mem.mp hXY f ((mem_inter_iff f X Y).mpr hf),  
end

lemma contra_fin_disjunct_psi_and_not {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  {φ ψ : formCLC agents} (hψ : ψ ∈ cl φ) (sfs : list (S_f φ)) 
  (hsfs : ∀ sf : (@S_f agents _ ha φ), sf ∈ sfs → ψ ∉ sf) :
  axCLC (⊥' <~> (ψ & finite_disjunction (phi_X_list φ sfs))) :=
begin
  apply @ax_iff_intro (formCLC agents),
  exact explosion,
  induction sfs with sf sfs ih,
  { unfold phi_X_list finite_disjunction,
    exact p6 _ _, },
  { unfold phi_X_list finite_disjunction at *,
    have hsfs' : ∀ sf : (@S_f agents _ ha φ), sf ∈ sfs → ψ ∉ sf, from
    begin
      intros sf hsf,
      apply hsfs,
      simp [hsf],
    end,
    specialize ih hsfs',
    refine and_right_imp.mpr _,
    apply or_cases,
    { have hχ := s_f_closed (hsfs sf (by simp)) hψ,
      cases hχ with χ hχ,
      apply cut,
      apply iff_l,
      apply phi_s_f_conj_contains sf hχ.left,
      apply imp_and_l,
      apply cut,
      apply iff_l,
      apply hχ.2,
      exact iden, },
    { refine and_right_imp.mp _,
      apply ih, }, },
end

lemma phi_X_contains_iff_psi_helper_list {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  {φ ψ : formCLC agents} (hψ : ψ ∈ cl φ)  (sfs tfs : list (S_f φ))
  (hsfs : ∀ sf : (@S_f agents _ ha φ), sf ∈ sfs → ψ ∈ sf)
  (htfs : ∀ tf : (@S_f agents _ ha φ), tf ∈ tfs → ψ ∉ tf)
  (hSf : axCLC (¬' (finite_disjunction (phi_X_list φ tfs))→'finite_disjunction (phi_X_list φ sfs))) :
  -- (hSf : axCLC (finite_disjunction (phi_X_list φ tfs ++ phi_X_list φ sfs))) :
  -- (hempty : (sfs = list.nil → axCLC (⊥' <~> ψ)) ∨ (sfs ≠ list.nil)) :
  axCLC ((finite_disjunction (phi_X_list φ sfs)) <~> ψ) :=
begin
  -- ↔ ∨ {sf |ψ∈sf }(ψ ∧ φsf), by propositional logic.
  apply @iff_cut (formCLC agents),
  exact (phi_X_list_conj_contains sfs hsfs),
  -- ↔ ⊥ ∨ (∨{sf |ψ∈sf }(ψ ∧ φsf)), by propositional logic.
  apply iff_cut,
  exact iff_switch_ax.mp (ax_not_bot_imp_iff _),
  -- ↔ (∨ {tf |¬ψ∈tf }(ψ ∧ φtf)) ∨ (∨ {sf |ψ∈sf }(ψ ∧ φsf)), by propositional logic.
  apply iff_cut,
  apply or_cut_l,
  apply contra_fin_disjunct_psi_and_not hψ tfs htfs,
   -- ↔ ψ ∧ ((∨ {tf |¬ψ∈tf } φtf ) ∨ (∨ {sf |ψ∈sf } φsf )), by propositional logic.
  apply @iff_cut _ _ _ _
    (ψ & (¬' (finite_disjunction (phi_X_list φ tfs)) →' finite_disjunction (phi_X_list φ sfs))),
  apply distr_or_and,
  -- ↔ ψ ∧ (∨ {sf ∈Sf } φsf ), because {tf | ¬ψ ∈ tf } ∪ {sf | ψ ∈ sf } = Sf .
  -- ↔ ψ ∧ ⊤, from Lemma 4.
  -- ↔ ψ, by propositional logic.
  apply ax_iff_intro,
  exact p5 _ _,
  apply cut,
  apply MP',
  exact hSf,
  exact p4 _ _,
  apply iff_l,
  exact and_switch,
end

lemma phi_X_contains_iff_psi_helper_finset {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  {φ ψ : formCLC agents} (hψ : ψ ∈ cl φ)  (sfs: finset (S_f φ)) 
  (hsfs : ∀ sf : (@S_f agents _ ha φ), sf ∈ sfs → ψ ∈ sf)
  (htfs : ∀ tf : (@S_f agents _ ha φ), tf ∉ sfs → ψ ∉ tf)
  (hSf : axCLC ((¬ phi_X_finset φ sfsᶜ) ~> phi_X_finset φ sfs)) :
  axCLC ( (phi_X_finset φ sfs) <~> ψ) :=
begin
  unfold phi_X_finset,
  apply phi_X_contains_iff_psi_helper_list hψ _ sfsᶜ.to_list,
  simp [finset.to_list], exact hsfs,
  simp [finset.to_list], exact htfs,
  exact hSf,
end

-- Lemma 6. ∀ ψ ∈ cl(φ), φ{sf |ψ∈sf } ↔ ψ
lemma phi_X_contains_iff_psi {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  (φ ψ : formCLC agents) (hψ : ψ ∈ cl φ) :
  axCLC (phi_X_set φ {sf | ψ ∈ sf} <~> ψ) :=
begin
  apply phi_X_contains_iff_psi_helper_finset hψ, simp, simp,
  apply (phi_X_finset_disjunct_of_disjuncts φ _ _).mpr,
  apply @MP' (formCLC agents),
  exact univ_disjunct_provability φ (canonical.nonempty_S_f φ),
  apply phi_X_subset_Y_imp,
  intros sf hsf,
  simp [to_finset] at *,
  rw or.comm,
  exact (em (ψ ∈ sf)),
end

lemma imp_ax_imp {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  {φ ψ : formCLC agents} (h : ∀ (a : (canonical_model_CLC agents).f.to_frameCL.states), φ ∈ a → ψ ∈ a) :
  axCLC (φ ~> ψ) :=
begin
  apply @ax_imp_from_ex (formCLC agents),
  apply h,
end

-- Lemma 7.  ̃ψ ∈ E(s)(G) iff [G]ψ ∈ s
lemma E_s_contains_tilde_iff_E_in_s {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  (φ ψ : formCLC agents) (s : (canonical_model_CLC agents).f.states) (G : set agents) :
  ((tilde ψ) ∈ ((canonical_model_CLC agents).f.E.E s G)) ↔ (([G] ψ) ∈ s) :=
begin
  let hE : (canonical_model_CLC agents).f.to_frameCL.E.E = λ s G, {X | ite (G = univ) 
          -- condition G = N
          (∀ φ, ({t | φ ∈ t} ⊆ Xᶜ) → ([∅]' φ) ∉ s.val)
          -- condition G ≠ N
          (∃ φ, {t | φ ∈ t} ⊆ X ∧ ([G]' φ) ∈ s.val)},
        from rfl,
  let hs : (canonical_model_CLC agents).f.to_frameCL.states = {Γ : (set (formCLC agents)) // (max_ax_consistent Γ)}, 
    from rfl,
  -- Proof. We consider the case when G ̸ = N and G = N separately.
  cases (em (G = univ)) with hG hG,
  { -- 2. case G = N
    rw hG,
    split,
    { -- 2.1. ⇒
      -- 2.1.1. Assume  ̃ψ ∈ E(s)(N ).
      intro h,
      -- 2.1.2. ∀ ̃χ ⊆  ̃ψᶜ : [∅]χ /∈ s, from 2.1.1, by definition E.
      simp [hE] at h {eta := ff}, clear hE,
      -- 2.1.3. ∀ ̃χ ⊆  ̃¬ψ : [∅]χ /∈ s, from 2.1.2, because  ̃ψᶜ =  ̃¬ψ.
      have h_subeq : {t : (canonical_model_CLC agents).f.to_frameCL.states | (¬ ψ) ∈ t} ⊆ (tilde ψ)ᶜ, from
      begin
        intros t ht hf,
        simp[tilde] at *,
        exact contra_containts_pr_false t.2 hf ht,
      end,
      -- 2.1.4. [N ]ψ ∈ s, from 2.1.3, by axiom N.
      specialize h (¬ ψ) h_subeq,
      have hin := not_in_from_notin s.2 h,
      apply max_ax_contains_by_set_proof s.2 hin axCLC.N, },
    { -- 2.2. ⇐
      -- 2.2.1. Assume [N ]ψ ∈ s.
      intro h,
      -- 2.2.2. ¬[∅]¬ψ ∈ s, from 2.2.1
      have hin : (¬ ([∅] (¬ ψ))) ∈ s, from
      begin
        apply max_ax_contains_by_set_proof s.2 h,
        exact iff_l (@univ_iff_empty agents (formCLC agents) _ _ _ ψ),
      end,
      -- 2.2.3. ¬∃χ,  ̃χ ⊆  ̃¬ψ : [∅]χ ∈ s, from proof by contradiction, 
        -- else by definition E we would have [∅]¬ψ ∈ s, which contradicts with 2.2.2.
      have hne : ¬ ∃ (χ : formCLC agents), (tilde χ) ⊆ (tilde ¬ ψ) ∧ ([∅]' χ) ∈ s, from 
      begin
        intro hf,
        cases hf with χ hf,
        cases hf with himp hf,
        simp [tilde] at himp,
        have hax : axCLC (χ ~>(¬ ψ)), from imp_ax_imp himp,
        have hf : ([∅]' (¬' ψ)) ∈ s, from
        begin
          apply max_ax_contains_by_set_proof s.2 hf,
          apply @derived_monoticity_rule agents (formCLC agents),
          exact hax,
        end,
        apply contra_containts_pr_false s.2 hf hin,
      end,
      -- 2.2.4. ∀χ,  ̃χ ⊆  ̃¬ψ : [∅]χ /∈ s, from 2.2.3, by first order logic.
      simp at hne,
      -- 2.2.5. ∀χ,  ̃χ ⊆  ̃ψ : [∅]χ /∈ s, because all s ∈ S are maximally consistent.
      rw h_tilde_compl at hne,
      -- 2.2.6.  ̃ψ ∈ E(s)(N ), from 2.2.5, by definition E.
      simp [hE] {eta := ff},
      exact hne, }, },
  { -- 1. case G ̸ = N
    split,
    { -- 1.1. ⇒
      -- 1.1.1. Assume  ̃ψ ∈ E(s)(G).
      intro h,
      -- 1.1.2. ∃ ̃χ ⊆  ̃ψ : [G]χ ∈ s, from 1.1.1, by definition E.
      simp [hE, hG] at h {eta := ff},
      -- 1.1.3. ⊢ χ → ψ, from 1.1.2.
      cases h with χ h,
      cases h with himp h,
      simp [tilde] at himp,
      have hax : axCLC (χ ~> ψ), from imp_ax_imp himp,
      -- 1.1.4. [G]ψ ∈ s, from 1.1.2 & 1.1.3, by lemma 2.
      apply max_ax_contains_by_set_proof s.2 h,
      apply @derived_monoticity_rule agents (formCLC agents),
      exact hax, },
    { -- 1.2. ⇐ is immediate by definition.
      simp [hE, hG],
      intro h,
      apply exists.intro ψ,
      split,
      simp [tilde],
      exact h, }, },
end


end lemmas


----------------------------------------------------------
-- Playability
----------------------------------------------------------

-- 1. Ef (sf ) is live: ∀G ⊆ N : ∅ /∈ Ef (sf )(G)
lemma Ef_liveness {agents : Type} [hN : fintype agents] [ha : nonempty agents] (φ : formCLC agents) :
  ∀ s : (S_f φ), ∀ G : set agents, ∅ ∉ (E_f s G) := 
begin
  -- 1.2. Assume by contradiction ∅ ∈ Ef (sf )(G).
  intros sf G hf,
  unfold E_f at hf,
  split_ifs at hf with h h,
  -- 1.4. Case: G = N
  { -- 1.4.1. ∃t ∈ S, sf = tf and  ̃φ∅ ∈ E(t)(N), from 1.2, by definition Ef .
    simp[h] at hf,
    -- 1.4.2. ∃t ∈ S, sf = tf and ∅ ∈ E(t)(N), from 1.4.1 & 1.1.
    cases hf with t hf,
    -- 1.4.3. ∀t, ∅ ∉ E(t)(N) because E(t) is live.
    have hlive := (canonical_model_CLC agents).f.E.liveness t univ,
    -- 1.4.4. Contradiction from 1.4.2 & 1.4.3.
    exact hlive hf.right, },
  -- 1.3. Case: G ≠ N
  { -- 1.3.1. ∀t ∈ S, sf = tf ⇒  ̃φ∅ ∈ E(t)(G), from 1.2, by definition Ef
    -- 1.3.2. ∀t ∈ S, sf = tf ⇒ ∅ ∈ E(t)(G), from 1.3.1 & 1.1
    simp[E_f, h] at hf,
    -- 1.3.3. ∅ ∈ E(s)(G), from 1.3.2
    cases (s_f_to_s φ sf) with s hs,
    specialize hf s @hs,
    -- 1.3.4. ∅ /∈ E(s)(G) because E(s) is live.
    have hlive := (canonical_model_CLC agents).f.E.liveness s,
    -- 1.3.5. Contradiction from 1.3.3 & 1.3.4.
    exact hlive G hf, },
end

-- 2. Ef (sf) is safe: ∀G ⊆ N : Sf ∈ Ef (sf )(G)
lemma Ef_safety {agents : Type} [hN : fintype agents] [ha : nonempty agents] (φ : formCLC agents) :
  ∀ (s : S_f φ) (G : set agents), univ ∈ E_f s G :=
begin
  -- 2.2. Additionally, because E(s) is safe for all s ∈ S, ∀G ⊆ N, S ∈ E(s)(G).
  have hsafe := (canonical_model_CLC agents).f.E.safety,
  -- 2.4. Case: G = N
  intros sf G, cases em (G = univ) with hG hG,
  { -- 2.4.1. Sf ∈ Ef (sf )(N ) iff ∃t ∈ S, sf = tf and  ̃φSf ∈ E(t)(N ), by definition Ef .
    simp[hG] at *,
    -- 2.4.2. Sf ∈ Ef (sf )(N ) iff ∃t ∈ S, sf = tf and S ∈ E(t)(N ), from 2.1 & 2.4.1.
    simp[E_f],
    -- 2.4.3. ∃t ∈ S, sf = tf and S ∈ E(t)(N ), when t = s, because sf = sf and S ∈ E(s)(N ), from 2.2.
    cases (s_f_to_s φ sf) with s hs,
    apply exists.intro s,
    -- 2.4.4. Sf ∈ Ef (sf )(N ), from 2.4.2 & 2.4.3s
    simp at *,
    split,
    exact @hs,
    apply hsafe, },
  -- 2.3. Case: G ≠ N
  { -- 2.3.1. Sf ∈ Ef (sf )(G) iff ∀t ∈ S, sf = tf ⇒  ̃φSf ∈ E(t)(G), by definition Ef .
    -- 2.3.2. Sf ∈ Ef (sf )(G) iff ∀t ∈ S, sf = tf ⇒ S ∈ E(t)(G), from 2.1 & 2.3.1.
    simp[E_f, hG] at *,
    -- 2.3.3. Sf ∈ Ef (sf )(G), from 2.2 & 2.3.2
    intros t ht,
    apply hsafe, }, 
end

-- 3. Ef (sf) is N-maximal: ∀X ⊆ Sf : Xᶜ ∉ Ef(sf)(∅) ⇒ X ∈ Ef(sf)(N)
lemma Ef_nmax {agents : Type} [hN : fintype agents] [ha : nonempty agents] (φ : formCLC agents) :
  N_max agents (S_f φ) (E_f) :=
begin
  -- 3.1. Assume some X ⊆ Sf such that Xᶜ ∉ Ef(sf)(∅).
  intros sf X hXc,
  -- 3.2. ¬(Xᶜ ∈ Ef sf ∅), from 3.1.
  -- 3.3. ¬(∀t ∈ S, sf = tf ⇒ ~φXᶜ ∈ E(t)(∅)), from 3.2, by definition Ef . 
  -- 3.4. ∃t ∈ S, sf = tf and ~φXᶜ ∉ E(t)(∅)), from 3.3, by first order logic. 
  simp[E_f, empty_ne_univ] at *,
  obtain ⟨t, ht, hXc⟩ := hXc,
  refine ⟨t, @ht, _⟩,
  { 
    have h_tilde: tilde (¬ (phi_X_set φ X) : formCLC agents) = 
      tilde (phi_X_set φ Xᶜ), from
    begin
      simp[tilde],
      ext1 u,
      split,
      { intro hu,
        simp at *,
        apply max_ax_contains_by_set_proof u.2 hu,
        apply (phi_X_set_disjunct_of_disjuncts φ _ _).mpr,
        rw (union_compl_self X),
        apply univ_disjunct_provability,
        exact canonical.nonempty_S_f φ, },
      { intro hu,
        simp at *,
        apply max_ax_contains_by_set_proof u.2 hu,
        unfold phi_X_set,
        apply phi_X_set_unique,
        simp, },
    end,

    -- 3.6. ∃t ∈ S, sf = tf and ~¬φX ∉ E(t)(∅)), from 3.4 & 3.5
    have hX : tilde (¬ (phi_X_set φ X) : formCLC agents) ∉ 
      (canonical_model_CLC agents).f.to_frameCL.E.E t ∅, from
    begin
      simp[h_tilde] at *,
      exact hXc,
    end,  
    -- 3.7. ∃t ∈ S,sf = tf and (~φX)ᶜ ∉ E(t)(∅)), from 3.6, because all s ∈ S are maximally consistent.
  simp at *,
  simp[h_tilde_compl] at hX,
    -- 3.8. ∃t ∈ S,sf = tf and φ􏰓 ∈ E(t)(N)), from 3.7, because E(s) is N-maximal X for all s ∈ S (∀X ⊆ S|X ∈/ E(s)(∅) ⇒ X ∈ E(s)(N))
    -- 3.9. Ef (sf )(N), from 3.8, by definition Ef .
  exact (canonical_model_CLC agents).f.to_frameCL.E.N_max t (tilde (phi_X_set φ X)) hX, },
end

-- Ef (sf ) is outcome monotonic: ∀G ⊆ N, ∀X ⊆ Y ⊆ Sf : X ∈ Ef (sf )(G) ⇒ Y ∈ Ef (sf )(G)
lemma Ef_monoticity {agents : Type} [hN : fintype agents] [ha : nonempty agents] (φ : formCLC agents) :
  ∀ (sf : S_f φ) (G : set agents) (X Y : set (S_f φ)), X ⊆ Y → X ∈ E_f sf G → Y ∈ E_f sf G :=
begin
  -- 4.1. Let G be some G ⊆ N and X and Y be some X ⊆ Y ⊆ Sf .
  intros s G X Y hXY,
  -- 4.2. Assume X ∈ Ef (sf )(G).
  intro hX,
  -- 4.3. First we note that ∀s ∈ S, ∀G ⊆ N,  ̃φX ∈ E(s)(G) ⇒  ̃φY ∈ E(s)(G)
  have himp : ∀ s G, 
    (tilde (phi_X_set φ X)) ∈ (canonical_model_CLC agents).f.E.E s G → 
    (tilde (phi_X_set φ Y)) ∈ (canonical_model_CLC agents).f.E.E s G, from
  begin
    -- 4.3.1. Let s be some s ∈ S and G be some G ⊆ N .
    clear hX, intros s G hX,
    -- 4.3.2. ⊢ φX → φY , from 4.1 (X ⊆ Y ).
    have hax : axCLC ((phi_X_set φ X) ~> (phi_X_set φ Y)), 
      from phi_X_set_subset_Y_imp _ _ _ hXY,
    -- 4.3.3.  ̃φX ⊆  ̃φY , from 4.3.2.
    have h_phiXY : (tilde (phi_X_set φ X)) ⊆ (tilde (phi_X_set φ Y)), from
    begin 
      rw set.subset_def,
      intros t ht,
      apply max_ax_contains_by_set_proof t.2 ht hax,
    end,
    -- 4.3.4. E(s) is outcome monotonic for all s ∈ S: ∀G ⊆ N, ∀X ⊆ Y ⊆ S, X ∈ E(s)(G) ⇒ Y ∈ E(s)(G)
    have hmonoticity := (canonical_model_CLC agents).f.E.monoticity s G _ _ h_phiXY,
    -- 4.3.5.  ̃φX ∈ E(s)(G) ⇒  ̃φY ∈ E(s)(G), from 4.3.3 & 4.3.4
    apply hmonoticity hX,
  end,
  -- 4.5. Case G = N
  cases em (G = univ) with hG hG,
  { -- 4.5.1. ∃t ∈ S, sf = tf and  ̃φX ∈ E(t)(N ), from 4.2, by definition Ef .
    simp[E_f, hG] at *,
    -- 4.5.2. ∃t ∈ S, sf = tf and  ̃φY ∈ E(t)(N ), from 4.3 & 4.5.1.
    -- 4.5.3. Y ∈ Ef (sf )(N ), from 4.5.2, by definition Ef . 
    cases hX with t ht,
    apply exists.intro t,
    split,
    { exact ht.1 },
    { exact himp _ _ ht.2, }, },
  -- 4.4. Case: G ≠ N
  { -- 4.4.1. ∀t ∈ S, sf = tf ⇒  ̃φX ∈ E(t)(N ), from 4.2, by definition Ef .
    simp[E_f, hG] at *,
    -- 4.4.2. ∀t ∈ S, sf = tf ⇒  ̃φY ∈ E(t)(N ), from 4.3 & 4.4.1.
    -- 4.4.3. Y ∈ Ef (sf )(G), from 4.4.2, by definition Ef .
    intros t ht,
    exact himp t G (hX t @ht), },
end

lemma phi_X_list_inter {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : list (S_f φ)) (hX : list.nodup X) (hY : list.nodup Y) :
  axCLC (finite_disjunction (phi_X_list φ X)→' finite_disjunction (phi_X_list φ Y) →' 
        finite_disjunction (phi_X_list φ (X ∩ Y))) :=
begin
  induction' X with x X ihx,
  { simp [phi_X_list, finite_disjunction],
    apply axCLC.Prop1, },
  { simp [phi_X_list, finite_disjunction],
    apply @or_cases (formCLC agents),
    { cases (em (x ∈ Y)),
      { apply cut,
        apply iff_l,
        apply phi_X_list_single,
        apply @cut _ _ _ _ (finite_disjunction (phi_X_list φ ((x :: X) ∩ Y))),
        apply imp_finite_disjunction_subset,
        apply phi_X_list_subset,
        simp,
        exact h,
        exact axCLC.Prop1, },
      { apply cut,
        apply iff_l,
        apply phi_X_list_single,
        apply cut1,
        apply phi_X_list_unique,
        exact list.singleton_disjoint.mpr h,
        exact list.nodup_singleton x,
        exact hY,
        exact explosion, }, },
    { simp at hX,
      specialize ihx Y hY hX.2,
      apply cut1,
      apply ihx,
      apply imp_finite_disjunction_subset,
      apply phi_X_list_subset,
      intros y hy,
      simp at *,
      split,
      apply or.intro_right,
      exact hy.1,
      exact hy.2, }, },
end

lemma phi_X_finset_inter {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : finset (S_f φ)) :
  axCLC ((phi_X_finset φ X) →' phi_X_finset φ Y →' (phi_X_finset φ (X ∩ Y))) :=
begin
  unfold phi_X_finset,
  apply @cut1 (formCLC agents),
  apply phi_X_list_inter,
  repeat {exact finset.nodup_to_list _, },
  apply imp_finite_disjunction_subset,
  apply phi_X_list_subset,
  intros x hx,
  simp [finset.mem_to_list] at *,
  exact hx,
end

lemma phi_X_set_inter {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : set (S_f φ)) :
  axCLC ((phi_X_set φ X) →' (phi_X_set φ Y) →' (phi_X_set φ (X ∩ Y))) :=
begin
  simp[phi_X_set],
  apply @cut1 (formCLC agents),
  apply phi_X_finset_inter,
  apply phi_X_subset_Y_imp,
  intros x hx,
  simp at *,
  exact hx, 
end
--  Ef (sf ) is superadditive ∀G, F ⊆ N (where G ∩ F = ∅), 
  -- ∀X, Y ⊆ Sf : X ∈ Ef (sf )(G) and Y ∈ Ef (sf )(F ) ⇒ X ∩ Y ∈ Ef (sf )(G ∪ F )
lemma Ef_superadd {agents : Type} [hN : fintype agents] [ha : nonempty agents] (φ : formCLC agents) :
  ∀ (sf : S_f φ) (G F : set agents) (X Y : set (S_f φ)),
  X ∈ E_f sf G → Y ∈ E_f sf F → G ∩ F = ∅ → X ∩ Y ∈ E_f sf (G ∪ F) :=
begin      
  -- 5.1. Let G, F be some G, F ⊆ N , such that G ∩ F = ∅. Let X, Y be some
    -- X, Y ⊆ S such that X ∈ Ef (sf )(G) and Y ∈ Ef (sf )(F ).
  -- intros sf G F X Y hX hY hGF,
  -- 5.2. First we note that ∀s ∈ S, ∀G, F ⊆ N (where G ∩ F = ∅),  ̃φX ∈ E(s)(G) ⇒  ̃φY ∈ E(s)(F ) ⇒  ̃φX∩Y ∈ E(s)(G ∪ F )
  have hint : ∀ s G F X Y, G ∩ F = ∅ → 
    (tilde (phi_X_set φ X)) ∈ (canonical_model_CLC agents).f.E.E s G →
    (tilde (phi_X_set φ Y)) ∈ (canonical_model_CLC agents).f.E.E s F →
    (tilde (phi_X_set φ (X ∩ Y))) ∈ (canonical_model_CLC agents).f.E.E s (G ∪ F), from
  begin
    -- 5.2.1. Let s be some s ∈ S. Let G, F , be some G, F ⊂ N where G ∩ F = ∅. Assume  ̃φX ∈ E(s)(G) and  ̃φY ∈ E(s)(F ).
    intros s G F X Y hGF hG hF,
    -- 5.2.2. E(s) is superadditive so: ∀X, Y ⊆ S : X ∈ E(s)(G) and Y ∈ E(s)(F ) ⇒ X ∩ Y ∈ E(s)(G ∪ F )
    have hsuperadd := ((canonical_model_CLC agents).f.E.superadd) s G F,
    -- 5.2.3.  ̃φX ∩  ̃φY ∈ E(s)(G ∪ F ), from 5.2.1 & 5.2.2.
    specialize hsuperadd (tilde (phi_X_set φ X)) (tilde (phi_X_set φ Y)) hG hF hGF,
    -- 5.2.4.  ̃φX∩Y ∈ E(s)(G ∪ F ), from 5.2.3, because  ̃φX →  ̃φX∩Y and  ̃φY →  ̃φX∩Y .
    have h_tilde_eq : tilde (phi_X_set φ X) ∩ tilde (phi_X_set φ Y) = tilde (phi_X_set φ (X ∩ Y)), from
    begin
      ext1 s,
      simp[tilde],
      split,
      { intro h,
        apply max_ax_contains_by_set_proof_2h s.2 h.1 h.2 ,
        apply phi_X_set_inter, },
      { intro h,
        split,
        repeat 
        { apply max_ax_contains_by_set_proof s.2 h,
          apply phi_X_set_subset_Y_imp,
          simp, }, },
    end,
    
    rw h_tilde_eq at hsuperadd,
    exact hsuperadd,
  end,
  
  intros sf G F X Y hX hY hGF,

  -- 5.4. Case G = N or F = N :
  have h_G_or_F_univ : ∀ X' Y', X' ∈ E_f sf univ → Y' ∈ E_f sf ∅ → (X' ∩ Y') ∈ E_f sf univ, from
  begin
    -- 5.4.1. Rename G, F, X&Y to G′, F ′, X′&Y ′, such that G′ = N , F ′ = ∅, X′ ∈ Ef (sf )(G′) and Y ′ ∈ Ef (sf )(F ′).
    clear hX hY,
    intros X' Y',
    -- 5.4.2. ∃t ∈ S, sf = tf and  ̃φX′ ∈ E(t)(N ), from 5.4.1 (X′ ∈ Ef (sf )(G′)), by definition Ef .
    intro hX,
    -- 5.4.3. ∀t ∈ S, sf = tf ⇒  ̃φY ′ ∈ E(t)(∅), from 5.4.1 (Y ′ ∈ Ef (sf )(F ′)), by definition Ef .
    intro hY,
    -- 5.4.4. ∃t ∈ S, sf = tf and  ̃φX′ ∈ E(t)(N ) and  ̃φY ′ ∈ E(t)(∅), from 5.4.2 & 5.4.3.
    simp[E_f, empty_ne_univ] at *,
    cases hX with t hX,
    specialize hY t hX.left,
    apply exists.intro t,
    split, exact hX.left,
    -- 5.4.5. ∃t ∈ S, sf = tf and  ̃φX′ ∩Y ′ ∈ E(t)(N ), from 5.3 & 5.4.4.
    specialize hint t univ ∅ X' Y' (by simp) hX.right hY,
    simp[univ_union] at hint,
    exact hint,
  end,

  cases em (G = univ),
  { simp[h] at *,
    simp[hGF] at *,
    exact h_G_or_F_univ X Y hX hY, },
  -- case G ≠ N
  { cases em (F = univ),
    { simp[h_1] at *,
      simp[hGF] at *,
      rw inter_comm X Y,
      exact h_G_or_F_univ Y X hY hX, },
    -- 5.3. Case G ≠ N and F ≠ N
    { -- 5.3.1. ∀t ∈ S, sf = tf ⇒  ̃φX ∈ E(t)(G), from 5.1 (X ∈ Ef (sf )(G)), by definition Ef .
      -- 5.3.2. ∀t ∈ S, sf = tf ⇒  ̃φY ∈ E(t)(F ), from 5.1 (Y ∈ Ef (sf )(F )), by definition Ef .
      simp[E_f, h, h_1] at *,
      -- 5.3.3. ∀t ∈ S, sf = tf ⇒ (  ̃φX ∈ E(t)(G)and  ̃φY ∈ E(t)(F )), from 5.3.1 & 5.3.2.
      -- 5.3.4. ∀t ∈ S, sf = tf ⇒  ̃φX∩Y ∈ E(t)(G ∪ F ), from 5.2 & 5.3.3.

      -- 5.3.6. Case G ∪ F = N : sf = sf and  ̃φX∩Y ∈ E(s)(G ∪ F ), from 5.3.4. So X ∩ Y ∈ Ef (sf )(G ∪ F = N ), by definition Ef
      cases em (G ∪ F = univ),
      { have hs := s_f_to_s φ sf,
        cases hs with s hs,
        specialize hint s G F X Y hGF (hX s @hs) (hY s @hs),
        simp[h_2] at *,
        apply exists.intro s,
        split, exact @hs, exact hint, },
      -- 5.3.5. Case G ∪ F ̸ = N : X ∩ Y ∈ Ef (sf )(G ∪ F ), from 5.3.4, by definition Ef
      { simp[h_2],
        intros t ht,
        exact hint t G F X Y hGF (hX t @ht) (hY t @ht), }, }, },
end

----------------------------------------------------------
-- Building the coplete filtered CLC model
----------------------------------------------------------
 
@[simps?] def filtered_model_CLC {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) :
  modelCLK agents := 
{ f := 
  { states := S_f φ,
    hs := canonical.nonempty_S_f φ,
    ha := ha,
    E := 
    
-- ∀u∈Sc if [u]=[s] then [φ ]c ∈Ec(u)(G) G̸=N
    { E          := E_f,
      liveness   := Ef_liveness φ,
      safety     := Ef_safety φ,
      N_max      := Ef_nmax φ,
      monoticity := Ef_monoticity φ,
      superadd   := Ef_superadd φ, },
    rel   := λ i s, {t | {φ | K' (i) (φ) ∈ s} = {φ | K' (i) (φ) ∈ t}},
    rfl   := by simp,
    sym   := λ i s t ht, eq.symm ht,
    trans := λ i s t u hst htu, (rfl.congr htu).mp hst, },
  v := λ  n, {s | (formCLC.var n) ∈ s.1.1}, }

----------------------------------------------------------
-- Truth Lemma
----------------------------------------------------------

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

-- lemma E_contains {agents : Type} [ha : nonempty agents] [hN : fintype agents] 
--   {s : (canonical_model_CLC agents).f.states} {X : set (canonical_model_CLC agents).f.states} {G : set agents} :
--   X ∈ (canonical_model_CLC agents).f.to_frameCL.E.E s G := sorry



-- 2. CGψ ∈ sf ⇒ ∀sn ∈ S that are reachable from sf by some path sf ∼f i1 sf1 ∼fi2 ... ∼f in sfn, 
      -- where {i1, i2..in} ⊆ G, then ψ ∈ sfn and CGψ ∈ sfn
-- lemma truth_C_helper {agents : Type} [ha : nonempty agents] [hN : fintype agents]
--   {ψ : formCLC agents} {s} {ss} {G : set (agents)} {is : list (agents)} 
--   (hG : ∀ i, i ∈ is → i ∈ G) (hC : (C G ψ) ∈ s) :
--   ∀ t : (canonical_model_CLC agents).f.to_frameCL.states, (C_path is ss s t) → (ψ ∈ t ∧ (C G ψ) ∈ t):=
-- begin
--     -- This proof is by induction on the length of the path.
--     induction' is with i is ih,
--     { simp [C_path], },
--     cases ss with t ss,
--     -- 2.1. Base case: length = 0
--     { -- 2.1.1. Assume CGψ ∈ sf
--       -- 2.1.2. ⊢ (CGψ) → ψ, by Axiom C and T.
--       intros t ht,
--       -- apply @ih ha hN,
--       -- { exact hC, },
--       -- { intros j hj,
--       --   apply hG j,
--       --   exact list.mem_cons_of_mem i hj, },
--       -- -- exact ht,
--       -- specialize @ih i hN ψ _ _ G hC hG.right u,
--       unfold C_path at ht,
--       dsimp at ht,
--       simp[ext_iff] at ht,
--       have hi := hG i,
--       simp at hi,
--       have hkt : K i (C G ψ) ∈ t, from
--       begin
--         apply (ht _).mp,
--         apply max_ax_contains_by_set_proof (formCLC agents),
--         exact s.2,
--         exact hC,
--         exact @c_imp_kc (agents) (formCLC agents) _ _ _ _ _ ψ G i hi,
--       end,
--       have hct : (C G ψ) ∈ t, from by apply max_ax_contains_by_set_proof t.2 hkt axCLC.T,
--       have ht : ψ ∈ t, 
--         from by apply max_ax_contains_by_set_proof t.2 hct (@c_imp (agents) (formCLC agents) _ _ _ _ ψ G i hi),
--       exact and.intro ht hct,
--     },
--     { -- 2.2. Inductive step: length (n) = m + 1
--       -- 2.2.1. Inductive Hypothesis: ∀sf m′ ∈ Sf if there exists some path sf ∼fi1 sf1 ∼fi2 ... ∼f im′ sfm′ , 
--         --  where {i1, i2..im′ } ⊆ G and m′ ≤ m then ψ ∈ sfm′ and CGψ ∈ sfm′ .
--       -- 2.2.2. Assume CGψ ∈ sf .
--       intros u hu,
--       simp [C_path] at *,
--       cases hu with hst htu,
--       dsimp at hst,
--       simp[ext_iff] at hst,
--       have hkt : K i (C G ψ) ∈ t, from
--       begin
--         apply (hst _).mp,
--         apply max_ax_contains_by_set_proof s.2 hC,
--         exact @c_imp_kc (agents) (formCLC agents) _ _ _ _ ψ G i hG.left,
--       end,
--       have hct : (C G ψ) ∈ t, from by apply max_ax_contains_by_set_proof t.2 hkt axCLC.T,
--       -- 2.2.3. ψ ∈ sfm and CGψ ∈ sfm, from 2.2.1.
--       -- specialize @ih i hN ψ _ (t :: ss) G hC hG.right u,
--       -- specialize @ih_s ψ t G hC i is hG.left hG.right ih u,
--       exact @ih i hN ψ t (ss) G hct hG.right u htu,
--       -- 2.2.4. Kim+1 CGψ ∈ sfm, by Axiom C, from 2.2.3.
--       -- 2.2.5. Kim+1 CGψ ∈ sfm+1, by definition ∼f (given that sfm ∼im+1sfm+1), from 2.2.4.
--       -- 2.2.6. CGψ ∈ sfm+1, by Axiom T, from 6.2.6.
--       -- 2.2.7. ψ ∈ sfm+1, by Axioms C & T, from 6.2.7.
--     },
-- end

-- 2. CGψ ∈ sf ⇒ ∀sn ∈ S that are reachable from sf by some path sf ∼f i1 sf1 ∼fi2 ... ∼f in sfn, 
--       where {i1, i2..in} ⊆ G, then ψ ∈ sfn and CGψ ∈ sfn
lemma truth_C_helper' {agents : Type} [ha : nonempty agents] [hN : fintype agents]
  {φ ψ : formCLC agents} {sf: S_f φ} {sfs : list (S_f φ)} {G : set (agents)} {is : list (agents)} 
  (hG : ∀ i, i ∈ is → i ∈ G) (hC : (C G ψ) ∈ sf) 
  (hcl : ψ ∈ cl φ) (hcl' : C G ψ ∈ cl φ) (hcl'' : ∀ i ∈ G, (K i (C G ψ)) ∈ cl φ) :
  ∀ tf : (S_f φ), (@C_path agents (filtered_model_CLC φ) is sfs sf tf) → (ψ ∈ tf ∧ (C G ψ) ∈ tf):=
begin
    -- This proof is by induction on the length of the path.
    obtain ⟨s, hs⟩ := s_f_to_s φ sf,
    induction' is with i is ih,
    { simp [C_path], },
    { simp only [list.mem_cons_iff, forall_eq_or_imp] at hG,
      -- simp [hs, ht, hcl, hcl'] at *, 
      cases sfs with tf sfs,
      { intros tf htf,
        obtain ⟨t, ht⟩ := @s_f_to_s agents ha hN φ tf,unfold C_path at htf,
        dsimp at htf,
        simp[ext_iff] at htf,
        -- specialize htf ψ,
        specialize hcl'' i hG.left,
        -- specialize htf _ (hcl'' i hG.left),
        -- simp [hcl''] at htf,
        have hkt : K i (C G ψ) ∈ tf, from
        begin
          -- specialize htf _ (hcl'' i hG.left),
          apply (htf _ ).mp,
          simp [hs, ht, hcl, hcl'] at *,
          split,
          apply @max_ax_contains_by_set_proof _ _ (@formula_axCLC _ hN) _ _ _ s.2 hC,
          exact @c_imp_kc _ hN _ _ (@formula_axCLC _ hN) _ _ _ ψ G i hG.left,
          exact hcl'',
        end,
        simp [hs, ht, hcl, hcl'] at *,
        have hct : (C G ψ) ∈ t, 
          from by apply @max_ax_contains_by_set_proof _ _ (@formula_axCLC _ hN) _ _ _ t.2 hkt.left (@axCLC.T _ hN _ _),
        have ht : ψ ∈ t, 
          from by apply @max_ax_contains_by_set_proof _ _ (@formula_axCLC _ hN) _ _ _ t.2 hct 
            (@c_imp _ hN _ _ (@formula_axCLC _ hN) _ _ _ ψ G i hG.left),
        exact and.intro ht hct, },
      { -- 2.2. Inductive step: length (n) = m + 1
        -- 2.2.1. Inductive Hypothesis: ∀sf m′ ∈ Sf if there exists some path sf ∼fi1 sf1 ∼fi2 ... ∼f im′ sfm′ , 
          --  where {i1, i2..im′ } ⊆ G and m′ ≤ m then ψ ∈ sfm′ and CGψ ∈ sfm′ .
        -- 2.2.2. Assume CGψ ∈ sf .
        intros uf huf,
        obtain ⟨t, ht⟩ := @s_f_to_s agents ha hN φ tf,
        obtain ⟨u, hu⟩ := @s_f_to_s agents ha hN φ uf,
        simp only [C_path] at *,
        cases huf with hst htu,
        dsimp at hst,
        simp[ext_iff] at hst,
        have hkt : K i (C G ψ) ∈ tf, from
        begin
          apply (hst _ ).mp,
          simp [hs, ht, hcl, hcl'] at *,
          split,
          apply @max_ax_contains_by_set_proof _ _ (@formula_axCLC _ hN) _ _ _ s.2 hC,
          exact @c_imp_kc _ hN _ _ (@formula_axCLC _ hN) _ _ _ ψ G i hG.left,
          exact hcl'' i hG.left,
        end,
        simp [hs, ht, hcl, hcl'] at hkt,
        have hct : (C G ψ) ∈ tf, from 
        begin
          simp [hs, ht, hcl, hcl'] at *,
          apply @max_ax_contains_by_set_proof _ _ (@formula_axCLC _ hN) _ _ _ t.2 hkt.left (@axCLC.T _ hN _ _),
        end,
        -- 2.2.3. ψ ∈ sfm and CGψ ∈ sfm, from 2.2.1.
        -- specialize @ih i hN ψ _ (t :: ss) G hC hG.right u,
        -- specialize @ih_s ψ t G hC i is hG.left hG.right ih u,
        apply @ih ha,
        -- apply ih hct hG.right uf htu,
        exact hct,
        repeat { assumption, },
        exact hG.right,

        -- exact @ih ha hN _ _ _ _ _ _ _ _ _ i hN ψ tf (sfs) G hct hG.right uf htu,
        -- 2.2.4. Kim+1 CGψ ∈ sfm, by Axiom C, from 2.2.3.
        -- 2.2.5. Kim+1 CGψ ∈ sfm+1, by definition ∼f (given that sfm ∼im+1sfm+1), from 2.2.4.
        -- 2.2.6. CGψ ∈ sfm+1, by Axiom T, from 6.2.6.
        -- 2.2.7. ψ ∈ sfm+1, by Axioms C & T, from 6.2.7.
    }, },
end

lemma truth_C_helper'' {agents : Type} [ha : nonempty agents] [hN : fintype agents]
  {φ ψ : formCLC agents} {sf: S_f φ} {G : set (agents)} 
  (hcl : ψ ∈ cl φ) (hcl' : C G ψ ∈ cl φ) (hcl'' : ∀ i ∈ G, (K i (C G ψ)) ∈ cl φ)
  (h : ∀ tf : (S_f φ), (∃ is sfs, (∀ i, i ∈ is → i ∈ G) ∧ 
  @C_path agents (filtered_model_CLC φ) is sfs sf tf) → (ψ ∈ tf ∧ (C G ψ) ∈ tf)) :
  (C G ψ) ∈ sf :=
begin
    -- 3.1. Assume ∀sfn ∈ Sf if there exists some path sf ∼fi1 sf1 ∼fi2 ... ∼fin sfn,where {i1, i2..in} ⊆ G then ψ ∈ sfn
    -- 3.2. let Σ be the set of all tf ∈ Sf, 
      -- such that for every state tfn if that tf n is reachable from tf through some path tf ∼f i1 tf 1 ∼fi2 ... ∼fin tf n,
      -- where {i1, i2..in} ⊆ G, then ψ ∈ tf .
    let Γ := {sf : S_f φ | ∀ tf : (S_f φ), (∃ is sfs, (∀ i, i ∈ is → i ∈ G) ∧ 
      @C_path agents (filtered_model_CLC φ) is sfs sf tf) → (ψ ∈ tf ∧ (C G ψ) ∈ tf)},
    -- 3.3. sf ∈ Σ, from 2.3.1 and 2.3.2.
    have hsfΓ : sf ∈ Γ, from h,
    -- 3.4. ⊢ φsf→ φΣ , by propositional logic, from 2.3.3.
    have hax1 : axCLC ((phi_s_f φ sf) ~> (phi_X_set φ Γ)), from ax_phi_s_f_imp_phi_X_set_of_mem' hsfΓ,
    -- 3.5. ⊢ φΣ → EGψ, by propositional logic, because all t ∈ Σ, ψ ∈ t.
    -- 3.6. ⊢ φΣ → EGφΣ , from 2.3.2.
    -- 3.7. ⊢ φsf → CGψ, by Axiom RC, from 2.3.4, 2.3.5 & 2.3.6.
    have hψΓ : (∃ i, i ∈ G) → ∀ sf ∈ Γ, ψ ∈ sf, from
    begin
      intros hi sf hsf,
      cases hi with i hi,
      simp [Γ] at hsf,
      apply and.elim_left,
      apply hsf sf (i :: list.nil) (by simp [hi]) (list.nil),
      unfold C_path,
      exact rfl,
    end,
    have hax2 : axCLC ((phi_X_set φ Γ) ~> E G (ψ & (phi_X_set φ Γ))), from sorry,
    -- 3.8. CGψ ∈ sf , from 2.3.7.
    obtain ⟨s, hs⟩ := s_f_to_s φ sf,
    simp [hs, hcl'],
    -- apply max_ax_contains_by_set_proof s.2 (phi_s_f_in_s ), --(by @cut (formCLC agents) _ _ _ _ hax1 hax2),
    sorry,
end

lemma truth_lemma_CLC {agents : Type} [ha : nonempty agents] [hN : fintype agents]
  (χ : formCLC agents) (sf : (S_f χ)) (φ) (hχ : subformula φ χ) :
  (s_entails_CLC (@filtered_model_CLC agents hN ha χ) sf φ) ↔ (φ ∈ sf) :=
begin
  -- This proof is by induction on φ.
  induction' φ fixing ha hN φ with n φ ψ _ _ φ ψ _ _, -- sf needs to vary for the modal operators
  all_goals
  { have hs := s_f_to_s χ sf,
    cases hs with s hs, },

  { -- case bot
    simp [s_entails_CLC, s_entails_CLC.aux],
    apply s_f_n_contains,
    exact @hs, 
    apply or.intro_left,
    exact @bot_not_mem_of_ax_consistent (formCLC agents) _ _ s.1 s.2.1, },

  { -- case var
    simpa [s_entails_CLC, s_entails_CLC.aux], },

  { -- case and
    have hφ := subformula.trans (subformula.and_left _ _) hχ,
    have hψ := subformula.trans (subformula.and_right _ _) hχ,
    specialize ih_φ _ sf hφ,
    specialize ih_ψ _ sf hψ,
    unfold s_entails_CLC s_entails_CLC.aux at *,
    rw [ih_φ, ih_ψ, hs, hs, hs],
    simp only [hφ.mem_cl, hψ.mem_cl, hχ.mem_cl, and_true],
    split,
    { rintro ⟨hφs, hψs⟩,
      apply max_ax_contains_by_set_proof_2h s.2 hφs hψs axCLC.Prop4 },
    { intro hφψs,
      split,
      { apply max_ax_contains_by_set_proof s.2 hφψs axCLC.Prop5 },
      { apply max_ax_contains_by_set_proof s.2 hφψs axCLC.Prop6 } } },

  { -- case imp
    have hφ := subformula.trans (subformula.imp_left _ _) hχ,
    have hψ := subformula.trans (subformula.imp_right _ _) hχ,
    specialize ih_φ _ sf hφ,
    specialize ih_ψ _ sf hψ,
    unfold s_entails_CLC s_entails_CLC.aux at *,
    rw [ih_φ, ih_ψ, hs, hs, hs],
    simp only [hφ.mem_cl, hψ.mem_cl, hχ.mem_cl, and_true],
    split,

    { intro h,
      exact max_ax_contains_imp_by_proof s.2 h, },

    { intros h hφ,
      exact max_ax_contains_by_set_proof_2h s.2 hφ h likemp, }, },

  { -- case [G] ψ
    -- have hE : (filtered_model_CLC χ).f.E.E = E_f, from rfl,
    have hφ := subformula.trans (subformula.effectivity _ _) hχ,
    let ih := λ sf, ih _ sf hφ,
    cases em (G = univ) with hG hG,
    { -- case [G]ψ, where G = N :
      calc s_entails_CLC (filtered_model_CLC χ) sf ([G]φ) 
          -- ↔ {sf ∈ Sf | M f , sf ⊨ ψ} ∈ E(sf )(N ), by definition ⊨
          ↔ {t | s_entails_CLC.aux (filtered_model_CLC χ) φ t} ∈ (filtered_model_CLC χ).f.to_frameCL.E.E sf G : 
            by unfold s_entails_CLC s_entails_CLC.aux at *
          -- ↔ ∃t ∈ S, sf = tf and  ̃φ{sf ∈Sf |M f ,sf ⊨ψ} ∈ E(t)(N ), by definition E.
      ... ↔ ∃ t, (∀ x, x ∈ sf ↔ x ∈ t ∧ x ∈ cl χ) ∧ tilde (phi_X_set χ ({sf | s_entails_CLC (filtered_model_CLC χ) sf φ})) ∈ (canonical_model_CLC agents).f.to_frameCL.E.E t (univ) :
          begin
            simp [E_f, hG] { eta := ff },
            split,
            repeat { intro h, apply h, },
          end
          -- ↔ ∃t ∈ S, sf = tf and  ̃φ{sf ∈Sf |ψ∈sf } ∈ E(t)(N ), , by the inductive hypothesis: ∀sf ∈ Sf , M f , sf ⊨ ψ iff ψ ∈ sf .
      ... ↔ ∃ t, (∀ x, x ∈ sf ↔ x ∈ t ∧ x ∈ cl χ) ∧ tilde (phi_X_set χ ({sf | φ ∈ sf} : set (S_f χ))) ∈ (canonical_model_CLC agents).f.to_frameCL.E.E t (univ) :
          by simp only [ih]
          -- ↔ ∃t ∈ S, sf = tf and  ̃ψ ∈ E(t)(N ), by Lemma 6.
      ... ↔ ∃ t, (∀ x, x ∈ sf ↔ x ∈ t ∧ x ∈ cl χ) ∧ tilde φ ∈ (canonical_model_CLC agents).f.to_frameCL.E.E t (univ) :
          by rw tilde_ax_iff χ (phi_X_contains_iff_psi χ φ (subformula.mem_cl hφ))
          -- ↔ ∃t ∈ S, sf = tf and [N ]ψ ∈ E(t)(N ), by Lemma 7.
          -- ↔ [N ]ψ ∈ sf , by definition Sf .
      ... ↔ ([G] φ) ∈ sf : 
          begin
            rw hG,
            split,
            { intro h,
              cases h with t h,
              rw E_s_contains_tilde_iff_E_in_s χ φ t univ at *,
              cases h with heq h,
              apply (heq ([univ] φ)).mpr,
              split,
              { exact h, },
              { simp [hG] at hχ,
                exact subformula.mem_cl hχ, }, },
            { intro h,
              apply exists.intro s,
              split,
              { simp at hs,
                exact @hs, },
              { simp [@hs] at h,
                rw E_s_contains_tilde_iff_E_in_s χ φ s univ at *,
                exact h.left, }, },
          end, },
    { calc s_entails_CLC (filtered_model_CLC χ) sf ([G]φ) 
          -- ↔ {sf ∈ Sf | M f , sf ⊨ ψ} ∈ E(sf )(G), by definition ⊨
          ↔ {t | s_entails_CLC.aux (filtered_model_CLC χ) φ t} ∈ (filtered_model_CLC χ).f.to_frameCL.E.E sf G : 
            by unfold s_entails_CLC s_entails_CLC.aux at *
          -- ↔ ∀t ∈ S, sf = tf ⇒  ̃φ{sf ∈Sf |M f ,sf ⊨ψ} ∈ E(t)(G), by definition E.
      ... ↔ ∀ t, (∀ x, x ∈ sf ↔ x ∈ t ∧ x ∈ cl χ) → tilde (phi_X_set χ ({sf | s_entails_CLC (filtered_model_CLC χ) sf φ})) ∈ (canonical_model_CLC agents).f.to_frameCL.E.E t (G) :
          begin
            simp [E_f, hG] { eta := ff },
            split,
            repeat { intro h, apply h, }
          end
          -- ↔ ∀t ∈ S, sf = tf ⇒  ̃φ{sf ∈Sf |M f ,ψ∈sf } ∈ E(t)(G), by the inductive hypothesis: ∀sf ∈ Sf , M f , sf ⊨ ψ iff ψ ∈ sf .
      ... ↔ ∀ t, (∀ x, x ∈ sf ↔ x ∈ t ∧ x ∈ cl χ) → tilde (phi_X_set χ ({sf | φ ∈ sf})) ∈ (canonical_model_CLC agents).f.to_frameCL.E.E t (G) :
          by simp only [ih]
          -- ↔ ∀t ∈ S, sf = tf ⇒  ̃ψ ∈ E(t)(G), by Lemma 6.
      ... ↔ ∀ t, (∀ x, x ∈ sf ↔ x ∈ t ∧ x ∈ cl χ) → tilde φ ∈ (canonical_model_CLC agents).f.to_frameCL.E.E t (G) :
          by rw tilde_ax_iff χ (phi_X_contains_iff_psi χ φ (subformula.mem_cl hφ))
          -- ↔ ∀t ∈ S, sf = tf ⇒ [G]ψ ∈ t, by Lemma 7.
          -- ↔ [G]ψ ∈ sf , by definition Sf .
      ... ↔ ([G] φ) ∈ sf : 
          begin
            split,
            { intro h,
              specialize h s @hs,
              rw E_s_contains_tilde_iff_E_in_s χ φ s G at h,
              simp only [@hs, subformula.mem_cl hχ, and_true],
              exact h, },
            { intros h t ht,
              rw E_s_contains_tilde_iff_E_in_s χ φ t G,
              apply and.elim_left,
              exact (ht _).mp h, },
          end, }, },
  
  -- case K
  { 
    -- have hK : (filtered_model_CLC χ).f.rel = λ i : agents, λ s : (@filtered_model_CLC agents hN ha χ).f.states, 
  --   {t : (@filtered_model_CLC agents hN ha χ).f.states | {φ : formCLC agents| ((K' i φ) : formCLC agents) ∈ s} = {φ | (K' i φ) ∈ t}},
  --     from rfl,
    have hφ := subformula.trans (subformula.knows _ _) hχ,
    let ih := λ sf, ih _ sf hφ,
    -- unfold s_entails_CLC s_entails_CLC.aux at *
    split,
    { -- ⇒
      simp only [@hs, hφ.mem_cl, hχ.mem_cl, and_true],
      -- 1. Let M f , sf ⊨ Kiψ
      intro h,
      -- 2. ∀tf ∈ Sf , sf ∼fi tf ⇒ M f , tf ⊨ ψ, by the definition of ⊨, from 1.
      unfold s_entails_CLC s_entails_CLC.aux at h ih,
      -- 3. ∀tf ∈ Sf , sf ∼fi tf ⇒ ψ ∈ tf , by the induction hypothesis, from 2.
      simp only [ih] at h,
      -- 4. Assume by contradiction that ¬Kiψ ∈ s.
      by_contradiction hnin,
      have hnk := not_in_from_notin s.2 hnin,
      -- 5. Consider the set Σ = {φ | φ is of the shape Kiχ and φ ∈ sf }.
      let Γ := {ψ : formCLC agents | K a ψ ∈ s},
      -- 6. Σ ∪ {¬ ψ} is consistent.
      have hcon : ax_consistent (Γ ∪ {¬ φ}), from
      begin
        -- 6.1. Assume by contradiction Σ ∪ {¬ψ} is inconsistent.
        by_contradiction hncon,
        -- 6.2. ⊢ (φΣ ∧ ¬ψ) → ⊥, from 6.1.
        have hncon' := five Γ (¬ φ) hncon,
        cases hncon' with ψs hncon', 
        -- 6.3. ⊢ φΣ → ψ, by propositional logic, from 6.2.
        cases hncon' with hΓ hax,
        -- 6.4. ⊢ Ki(φΣ → ψ), by Axiom RN, from 6.3.
        -- 6.5. ⊢ (KiφΣ ) → (Kiψ), by Axiom K, from 6.4.
        have h5 : axCLC ((finite_conjunction (list.map (K a) ψs)) ~> K a (φ)), from by
        begin 
          apply @cut (formCLC agents),
          apply @knows_conjunction agents hN (formCLC agents) _,
          apply axCLC.MP axCLC.K,
          apply axCLC.RN,
          simp at hax,
          apply @cut (formCLC agents),
          exact hax,
          exact dne,
        end,
        -- 6.6. ⊢ φΣ → KiφΣ , by Axiom K, and propositional logic.
        have h6 := exercise1,
        -- 6.7. φΣ ∈ s, by definition Sigma, from 5.
        -- 6.8. Kiψ ∈ s, from 6.5, 6.6 & 6.7.
        have h7 : ∀ ψ ∈ (list.map (K a) ψs), ψ ∈ s, from
        begin
          intros ψ h8, simp at *, cases h8 with a h8,
          cases h8 with h8l h8r,
          subst h8r, exact hΓ a h8l,
        end,
        specialize h6 s.2 h7 h5,
        have h8 := (max_ax_contains_phi_xor_neg s.1 (max_imp_ax s.2)).mp s.2 (K a (φ)),
        cases h8 with h8l h8r, simp at *, 
        -- 6.9. Contradiction from 4 and 6.8.
        apply (h8r h6),
        exact hnk,
      end,
      -- 7. ∃u ∈ S, sf ∼fi u and ¬ψ ∈ uf , from 6, based on the definitions of ∼fi and Σ.
      obtain ⟨t', ht, hsub⟩ := lindenbaum hcon,
      let t : (canonical_model_CLC agents).f.to_frameCL.states := ⟨t', ht⟩,
      have h5 := set.union_subset_iff.mp hsub,
      simp at h5,
      cases h5,
      have hnin : (¬ φ) ∈ t, from h5_right,
      simp at hnin,
      obtain ⟨tf, htf⟩ := s_to_s_f χ t,
      have hrel : tf ∈ (filtered_model_CLC χ).f.rel a sf, from
      begin
        simp,
        ext1,
        split,
        { simp [@hs, htf],
          intros hks hcl,
          split,
          { apply mem_of_mem_of_subset _ h5_left,
            simp only [Γ],
            apply max_ax_contains_by_set_proof s.2 hks axCLC.Four, },
          { exact hcl, },
        },
        { simp [@hs, htf],
          intros hkt hcl,
          split,
          { by_contradiction hnks,
            have hnks' := not_in_from_notin s.2 hnks,
            have hknks := max_ax_contains_by_set_proof s.2 hnks' axCLC.Five,
            have hnkΓ : (¬ K a x) ∈ Γ, from hknks,
            have hnkt : (¬ K a x) ∈ t.1, from mem_of_mem_of_subset hnkΓ h5_left,
            exact contra_containts_pr_false t.2 hkt hnkt, },
          { exact hcl, },
        },
      end,
      specialize h tf hrel,
      simp [@hs, htf] at h,
      -- 8. Contradiction from 3 & 7.
      apply contra_containts_pr_false t.2 h.left hnin, },
    {  -- ⇐
      -- 1. Let Kiψ ∈ sf .
      intro h,
      -- 2. Consider any tf ∈ Sf , such that sf ∼f i tf .
      -- 3. {χ | Kiχ ∈ sf } = {χ | Kiχ ∈ tf }, by definition ∼f i , from 2.
      unfold s_entails_CLC s_entails_CLC.aux at *,
      dsimp,
      intros tf htf,
      obtain ⟨t, ht⟩ := s_f_to_s χ tf,
      -- simp at tf,
      -- 4. Kiψ ∈ tf , from 1 & 3.
      have hkt : (K' a φ) ∈ tf, from 
      begin
        simp [ext_iff] at htf,
        exact (htf φ).mp h, 
      end,
      -- 5. ψ ∈ tf , by Axiom T, from 4.
      have hφt : φ ∈ tf, from
      begin
        simp only [ht, hφ.mem_cl, hχ.mem_cl, and_true] at *,
        exact max_ax_contains_by_set_proof t.2 hkt.left axCLC.T,
      end,
      -- 6. ∀tf ∈ Sf , sf ∼fi tf ⇒ ψ ∈ tf , from 2 & 5.
      -- 7. ∀tf ∈ Sf , sf ∼fi tf ⇒ M f , tf ⊨ ψ, by the induction hypothesis, from 6.
      simp only [ih],
      -- 8. M f , sf ⊨ Kiψ, by the definition of ⊨, from 7.
      exact hφt, }, },
  
  -- case E
  { sorry, },

  -- case C
  { have hφ := subformula.trans (subformula.common_know _ _) hχ,
    let ih := λ sf, ih _ sf hφ,
    unfold s_entails_CLC s_entails_CLC.aux at *,

    -- 2. CGψ ∈ sf ⇒ ∀sn ∈ S that are reachable from sf by some path sf ∼f i1 sf1 ∼fi2 ... ∼f in sfn, 
      -- where {i1, i2..in} ⊆ G, then ψ ∈ sfn and CGψ ∈ sfn
    -- have hcpath := truth_C_helper',
    -- 3. (∀sn ∈ S that are reachable from sf by some path sf ∼fi1 sf1 ∼fi2 ... ∼finsfn, where {i1, i2..in} ⊆ G, then ψ ∈ sfn) ⇒ CGψ ∈ sf .
    -- 4. CGψ ∈ sf ⇔ ∀sn ∈ S if sf n is reachable from sf by some path sf ∼fi1 sf1 ∼fi2 ... ∼fin sf n, 
      -- where {i1, i2..in} ⊆ G, then ψ ∈ sfn, from 2 & 3.
    -- 5. CGψ ∈ sf ⇔ ∀sn ∈ S if sfn is reachable from sf by some path sf ∼fi1 sf1 ∼fi2 ... ∼f in sfn, where {i1, i2..in} ⊆ G, then M f , sfn ⊨ ψ, from 1 & 4.
    -- 6. CGψ ∈ sf ⇔ M f , sf ⊨ CGψ, by definition ⊨, from 5.
    sorry, },
end

----------------------------------------------------------
-- Completeness
----------------------------------------------------------

-- Completeness
----------------------------------------------------------
theorem completenessCLC {agents : Type} [h : fintype agents] (φ : formCLC agents) [ha : nonempty agents] : 
  global_valid φ → axCLC φ :=
begin
  -- rw from contrapositive
  rw ←not_imp_not, 
  -- assume ¬ ⊢ φ
  intro hnax,
  -- from ¬ ⊢ φ, have that {¬ φ} is a consistent set
  obtain ⟨s, hmax, hnφ⟩ := @exists_max_ax_consistent_neg_mem (formCLC agents) _ _ _ hnax,
  -- show that φ is not globally valid, 
  -- by showing that there exists some model where φ is not valid.
  simp[global_valid],
  -- let that model be the canonical model
  apply exists.intro (canonical_model_CLC agents),
  -- in the canonical model (M) there exists some state (s) where ¬ M s ⊨ φ
  simp[valid_m],
  -- let that state (s) be the maximally consistent set extended from {¬ φ}
  apply exists.intro (subtype.mk s hmax),
  -- assume by contradiction that M s ⊨ φ
  intro hf,
  -- by the truth lemma φ ∈ s
  -- have hφ, from (truth_lemma_CLC φ (subtype.mk s hmax)).mp hf,
  -- in that state (s), φ ∈ s, so we do not have ¬ φ ∈ s (by consistency)
  -- contradiction with hnφ
  -- apply contra_containts_pr_false hmax hφ hnφ,
  sorry,
end

end canonical
