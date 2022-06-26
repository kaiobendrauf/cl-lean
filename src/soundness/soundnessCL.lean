/-
Copyright (c) 2021 Paula Neeley. All rights reserved.
Author: Paula Neeley
-/

import syntax.syntaxCL syntax.axiomsCL semantics.semanticsCL
-- import basicmodal.semantics.definability basicmodal.syntax.syntaxlemmas
local attribute [instance] classical.prop_decidable

open set

variable {agents : Type}

---------------------- Soundness ----------------------

theorem soundnessCL (φ : formCL agents) : axCL φ → global_valid φ :=
begin
intro h,
induction h,
{
  intros m s h1 h2, 
  exact h1,
},
{
  intros m s h1 h2 h3, 
  apply h1, 
    { exact h3,},
    { 
      apply h2, 
      exact h3
      },
},
{
  intros m s h1 h2,
  by_contradiction hf,
  exact (h1 hf) (h2 hf)
},
{
  intros m s h1 h2, 
  exact and.intro h1 h2
},
{
  intros m s h1, 
  exact h1.left,
},
{
  intros m s h1, 
  exact h1.right,
},
{
  intros m s h1 h2,
  by_contradiction hf,
  exact h1 hf h2
},
{
  intros m s h1, 
  exact m.f.E.liveness s h h1
},
{
  intros m s,
  simp [s_entails],
  exact m.f.E.safety s h,
},
{
  intros m s h1,
  apply m.f.E.N_max,
  by_contradiction,
  exact h1 h,
},
{
  intros m s,
  apply m.f.E.monoticity s h_G (tilde m (h_φ & h_ψ)) (tilde m h_φ),
  intros t h1,
  exact h1.left,
  },
  {
    intros m s h1,
    exact m.f.E.superadd s h_G h_F (tilde m h_φ) (tilde m h_ψ) h1.left h1.right h_hInt,
  },
  {
    intros m s,
    apply h_ih_hImp,
    exact h_ih_hL m s,
  },
  {
    intros m s,
    have heq: (tilde m h_φ) = (tilde m h_ψ), from
      begin
        apply set.ext,
        intros u,
        cases (h_ih m u),
        apply iff.intro,
        {
          intro hu,
          exact left hu,
        },
        {
          intro hu,
          exact right hu,
        }
      end,
    apply and.intro,
    {
      intro h1,
      simp[tilde, s_entails] at *,
      rw ←heq,
      exact h1,
    },
    {
      intro h1,
      simp[tilde, s_entails] at *,
      rw heq,
      exact h1,
    },
  },
end


-- lemma soundnesshelper {Γ : ctx} {φ : form} {C : set (frame)} : 
--   prfK Γ φ → (∀ ψ ∈ Γ, F_valid ψ C) → F_valid φ C :=
-- begin
-- intros h1 h2 f h3 v, induction h1,
-- {intro x, exact h2 h1_φ h1_h f h3 v x},
-- {intros x h4 h5, exact h4},
-- {intros x h4 h5 h6, exact (h4 h6) (h5 h6)},
-- {intros x h3 h4, by_contradiction h5, specialize h3 h5, 
-- rw ←not_forces_imp at h3, exact h3 (h4 h5)},
-- {intros x h4 h5, exact and.intro h4 h5}, 
-- {intros x h4, exact h4.left}, 
-- {intros x h4, exact h4.right}, 
-- {intros x h4 h5, repeat {rw forces at h4}, 
-- repeat {rw imp_false at h4},
-- rw not_imp_not at h4, exact h4 h5},
-- {intros x h3 h4, intros x' h5,
-- exact (h3 x' h5) (h4 x' h5)},
-- {intro x, exact h1_ih_hpq h2 x (h1_ih_hp h2 x)},
-- {intros x y h3, apply h1_ih, exact h2}
-- end


-- lemma inclusion_valid {C C' : set (frame)} : ∀ ψ, C ⊆ C' → F_valid ψ C' → F_valid ψ C :=
-- begin
-- intros φ h1 h2 f h3 v x, 
-- exact h2 f (set.mem_of_subset_of_mem h1 h3) v x
-- end


-- def T_axioms  : ctx := {φ : form | ∃ ψ, φ = (□ ψ ⊃ ψ)}
-- def S4_axioms : ctx := T_axioms ∪ {φ : form | ∃ ψ, φ = (□ ψ ⊃ □ (□ ψ))}
-- def S5_axioms : ctx := T_axioms ∪ {φ : form | ∃ ψ, φ = (◇ ψ ⊃ □ (◇ ψ))}


-- lemma T_helper : ∀ φ ∈ T_axioms, F_valid φ ref_class :=
-- begin
-- intros φ h1 f h2 v x,
-- cases h1 with ψ h1, subst h1, 
-- apply ref_helper, exact h2
-- end


-- theorem T_soundness (φ : form) : prfK T_axioms φ → F_valid φ ref_class :=
-- begin
-- intro h, apply soundnesshelper, apply h, apply T_helper 
-- end


-- lemma S4_helper : ∀ φ ∈ S4_axioms, F_valid φ ref_trans_class :=
-- begin
-- intros φ h1 f h2 v x,
-- cases h2 with h2l h2r, 
-- cases h1 with h1 h3, 
-- {apply T_helper, exact h1, exact h2l},
-- {cases h3 with ψ h3, subst h3, 
-- apply trans_helper, exact h2r}
-- end


-- theorem S4_soundness (φ : form) : prfK S4_axioms φ → F_valid φ ref_trans_class :=
-- begin
-- intro h, apply soundnesshelper, apply h, apply S4_helper
-- end


-- lemma S5_helper : ∀ φ ∈ S5_axioms, F_valid φ equiv_class :=
-- begin
-- intros φ h1 f h2 v x,
-- cases h2 with h2l h2r, 
-- cases h2r with h2r h2rr,
-- cases h1 with h1 h3, 
-- {apply T_helper, exact h1, 
-- exact h2l},
-- {cases h3 with ψ h3, dsimp at h3,
-- subst h3, apply euclid_helper,
-- intros x y z h1 h2,
-- exact h2rr (h2r h1) h2}
-- end


-- theorem S5_soundness (φ : form) : prfK S5_axioms φ → F_valid φ equiv_class :=
-- begin
-- intro h, apply soundnesshelper, apply h, apply S5_helper
-- end

inductive single : Type
  | one: single


lemma univ_single : (set.univ: set single) = {single.one} := 
begin
  rw eq_comm,
  rw set.eq_univ_iff_forall,
  intro x,
  cases x,
  simp,
end

lemma single_nonempty : nonempty single := 
begin
  apply exists_true_iff_nonempty.mp,
  apply exists.intro single.one,
  exact trivial,
end

def m_ex (ha: nonempty agents) : modelCL agents  :=
{
  f := 
  {
    states := single,
    hs := single_nonempty,
    ha := ha,
    E  :=  
    {
      E := λ s G, {{single.one}},
      liveness := 
      begin 
        intros _ _ hf, 
        simp at hf, 
        rw set.ext_iff at hf, 
        simp at hf,
        apply hf single.one,
        refl, 
      end,
      safety:=
        begin
          intros _ _, simp at *,
          exact univ_single,
        end,
      N_max :=
        begin
          intros _ _ hxc, simp at *,
          rw ←univ_single at *,
          have hcond : {single.one} ≠ (∅: set single), 
            {
              intro hf,
              rw set.ext_iff at hf, 
              simp at *,
              apply hf single.one,
              refl,
            },
          simp [hcond] at *, by_contradiction,
          have hex: ∃ x, x ∈ X, from nonempty_def.mp (ne_empty_iff_nonempty.mp hxc),
          cases hex with s hs,
          cases s,
          rw ←singleton_subset_iff at hs,
          rw ←univ_single at hs,
          exact h (univ_subset_iff.mp hs),
        end,
      monoticity:=
        begin
          intros _ _ _ _ hxy hx,
          simp [←univ_single] at *,
          rw hx at hxy,
          exact univ_subset_iff.mp hxy,
        end,
      superadd:=
      begin
        intros _ _ _ _ _ hX hY hGF,
        simp at *,
        simp[hX, hY],
      end
    }
  },
  v := λ _, {},
}

lemma nprfalseCL {agents: Type} (ha: nonempty agents): ¬ @axCL agents (⊥) :=
begin
apply (mt (soundnessCL (@formCL.bot agents))),
intro hf ,
simp[global_valid, valid_m, s_entails] at hf,
apply hf (m_ex ha),
exact single.one,
end
