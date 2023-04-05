/-
Authors : Kai Obendrauf
Following the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley

This file contains the proof that CL is complete.
Given completeness we also prove that CL does not prove ⊥, 
  by coming up with a simple instance of a coalition model. 
-/

import semantics.semanticsCL
local attribute [instance] classical.prop_decidable

open set

----------------------------------------------------------
-- Soundness
----------------------------------------------------------

theorem soundnessCL {agents : Type} (φ : formCL agents) : '⊢ φ → '⊨ φ :=
begin
  intro h,
  induction h,
  -- case Prop1
  { intros m s h1 h2, 
    exact h1, },
  -- case Prop2
  { intros m s h1 h2 h3, 
    apply h1, 
      { exact h3,},
      { apply h2, 
        exact h3 }, },
  -- case Prop3
  { intros m s h1 h2,
    by_contradiction hf,
    exact (h1 hf) (h2 hf), },
  -- case Prop4
  { intros m s h1 h2, 
    exact and.intro h1 h2, },
  -- case Prop5
  { intros m s h1, 
    exact h1.left, },
  -- case Prop6
  { intros m s h1, 
    exact h1.right, },
  -- case Prop7
  { intros m s h1 h2,
    by_contradiction hf,
    exact h1 hf h2, },
  -- case ⊥
  { intros m s h1,
    exact m.f.E.liveness s h h1, },
  -- case ⊤
  { intros m s,
    simp [s_entails_CL],
    exact m.f.E.safety s h, },
  -- case N
  { intros m s h1,
    apply m.f.E.N_max,
    by_contradiction,
    exact h1 h, },
  -- case M
  { intros m s,
    apply m.f.E.mono s h_G _ {t | m; t '⊨ h_φ},
    intros t h1,
    exact h1.left, },
  -- case S
  { intros m s h1,
    exact m.f.E.superadd s h_G h_F _ _ h1.left h1.right h_hInt, },
  -- case MP
  { intros m s,
    apply h_ih_hImp,
    exact h_ih_hL m s, },
  -- case Eq
  { intros m s,
    have heq : {t | m; t '⊨ h_φ} = {t | m; t '⊨ h_ψ}, from
      begin
        apply set.ext,
        intro u,
        apply iff.intro,
        { intro hu,
          exact (h_ih m u).left hu, },
        { intro hu,
          exact (h_ih m u).right hu, },
      end,
    apply and.intro,
    { intro h1,
      simp only [s_entails_CL, ←heq] at *,
      exact h1, },
    { intro h1,
      simp only [s_entails_CL, heq] at *,
      exact h1, }, },
end

----------------------------------------------------------
-- CL does not prove ⊥
----------------------------------------------------------
-- create an example Model
inductive single : Type
  | one : single

lemma univ_single : (set.univ : set single) = {single.one} := 
begin
  rw eq_comm,
  rw set.eq_univ_iff_forall,
  intro x,
  cases x,
  simp,
end

instance single_nonempty : nonempty single := 
begin
  apply exists_true_iff_nonempty.mp,
  apply exists.intro single.one,
  exact trivial,
end

def m_ex {agents : Type} : modelCL agents :=
{ f := 
  { states := single,
    hs := single_nonempty,
    E  :=  
    { E := λ s G, {{single.one}},
      liveness := 
      begin 
        intros _ _ hf, 
        simp at hf, 
        rw set.ext_iff at hf, 
        simp at hf,
        apply hf single.one,
        refl, 
      end,
      safety :=
        begin
          intros _ _, simp at *,
          exact univ_single,
        end,
      N_max :=
        begin
          intros _ _ hxc, simp at *,
          rw ←univ_single at *,
          have hcond : {single.one} ≠ (∅ : set single), 

            { intro hf,
              rw set.ext_iff at hf, 
              simp at *,
              apply hf single.one,
              refl, },
          simp [hcond] at *, by_contradiction,
          have hex : ∃ x, x ∈ X, from nonempty_def.mp (ne_empty_iff_nonempty.mp hxc),
          cases hex with s hs,
          cases s,
          rw ←singleton_subset_iff at hs,
          rw ←univ_single at hs,
          exact h (univ_subset_iff.mp hs),
        end,
      mono :=
        begin
          intros _ _ _ _ hxy hx,
          simp [←univ_single] at *,
          rw hx at hxy,
          exact univ_subset_iff.mp hxy,
        end,
      superadd :=
      begin
        intros _ _ _ _ _ hX hY hGF,
        simp at *,
        simp[hX, hY],
      end } },
  v := λ _, {}, }


lemma nprfalseCL {agents : Type} : ¬ ('⊢ ('⊥ : formCL agents)) :=
begin
  -- prove with the contrapositive of soundness : ¬ ⊨ ⊥
  apply (mt (soundnessCL (@formCL.bot agents))),
  -- assume by contradiction : ⊨ ⊥
  intro hf,
  -- ⊨ ⊥ only holds if no model with states exists
  simp[global_valid, valid_m, s_entails_CL] at hf,
  -- we create an example model with a single state to prove a contradiction
  exact hf (m_ex) single.one,
end
