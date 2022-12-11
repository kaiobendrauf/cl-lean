import soundness.soundnessCLC
import completeness.canonical
import completeness.closureC
-- import syntax.axiomsCLC
import syntax.consistency_lemmas
-- import syntax.CLClemmas
-- import tactic.induction
-- import data.finset.powerset


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
  (φ : formCLC agents) {sf tf : (S_f φ)} : 
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

lemma s_f_to_s_to_s_f {agents : Type} [ha : nonempty agents] [hN : fintype agents] {φ : formCLC agents} 
  {sf : (S_f φ)} {s : (canonical_model_CLC agents).f.states} (hs : ∀ {x}, x ∈ sf ↔ (x ∈ s.1 ∧ x ∈ cl φ)) : 
    (s_f φ s) = sf :=
begin
  rw s_f_eq,
  unfold s_f,
  ext1 x,
  split,
  { intro h,
    apply hs.mpr,
    rw finset.mem_filter at h,
    rw and.comm,
    exact h, },
  { intro h,
    rw [finset.mem_filter, and.comm],
    apply hs.mp,
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

end canonical