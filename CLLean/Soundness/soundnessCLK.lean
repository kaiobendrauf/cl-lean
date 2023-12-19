/-
Authors: Kai Obendrauf
Following the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley

This file contains the proof that CLK is complete.
Given completeness we also prove that CLK does not prove ⊥
  by coming up with a simple instance of a coalition model. 
-/

import Mathlib.Tactic
import CLLean.Semantics.semanticsCLK
local attribute [instance] classical.prop_decidable

open Set

----------------------------------------------------------
-- Soundness
----------------------------------------------------------

---------------------- Soundness ----------------------

theorem soundnessCLK {agents: Type} (φ : formCLK agents) : 
  '⊢ φ → '⊨ φ :=
begin
  intro h
  induction' h

  -- Prop 1
  { intro m s h1 h2
    exact h1, }

  -- Prop 2
  { intro m s h1 h2 h3
    apply h1
      { exact h3,}

      { apply h2
        exact h3 }, }

  -- Prop 3
  { intro m s h1 h2
    by_contradiction hf
    exact (h1 hf) (h2 hf), }

  -- Prop 4
  { intro m s h1 h2
    exact and.intro h1 h2, }

  -- Prop 5
  { intro m s h1
    exact h1.left, }

  -- Prop 6
  { intro m s h1
    exact h1.right, }

  -- Prop 7
  { intro m s h1 h2
    by_contradiction hf
    exact h1 hf h2, }

  -- Bot
  { intro m s h1
    exact m.f.E.liveness s G h1, }

  -- Top
  { intro m s
    simp [s_entails_CLK]
    exact m.f.E.safety s G, }

  -- N
  { intro m s h1
    apply m.f.E.N_max
    by_contradiction
    exact h1 h, }

  -- M
  { intro m s
    apply m.f.E.mono s G {t : m.f.states | m; t '⊨ (φ '∧ φ_1)}
      {t : m.f.states | m; t '⊨ φ}
    intro t h1
    unfold s_entails_CLK at h1
    exact h1.left, }

  -- S
  { intro m s h1
    exact m.f.E.superadd s G F {t : m.f.states | m; t '⊨ φ} 
      {t : m.f.states | m; t '⊨ φ_1} h1.left h1.right hInt, }

  -- MP
  { intro m s
    apply ih_h
    exact ih_h_1 m s, }

  -- Eq
  { intro m s
    have heq: {t : m.f.states | m; t '⊨ φ} = {t : m.f.states | m; t '⊨ φ_1}
    { apply Set.ext
      intro u
      cases (ih m u)
      apply iff.intro
      { intro hu
        exact left hu, }
      { intro hu
        exact right hu } }
    apply and.intro
    { intro h1
      simp only [s_entails_CLK, ←heq] at *
      exact h1, }
    { intro h1
      simp only [s_entails_CLK, heq] at *
      exact h1, }, }

  -- K
  { intro m s h1 h2 t ht
    exact h1 t ht (h2 t ht), }

  -- T
  { intro m s h
    exact h s (m.f.rfl i s), }

  -- Four
  { intro m s h t ht u hu
    exact h u (m.f.trans i s t u ht hu), }

  -- Five
  { intro m s h1 t ht ht1
    apply h1
    intro u hu
    apply ht1
    exact m.f.trans _ _ _ _ (m.f.sym _ _ _ ht) hu, }

  -- RN
  { intro m s t hst
    apply ih, }
end

----------------------------------------------------------
-- CL does not prove ⊥
----------------------------------------------------------
-- create an example Model
inductive single : Type
  | one: single

lemma univ_single : (Set.univ: Set single) = {single.one} := 
begin
  rw eq_comm
  rw Set.eq_univ_iff_forall
  intro x
  cases x
  simp
end

instance single_nonempty : Nonempty single := 
begin
  apply exists_true_iff_nonempty.mp
  apply Exists.intro single.one
  exact trivial
end

instance single_finite : Fintype single := 
begin
  refine {elems := {single.one}, complete := _}
  intro x
  cases x
  exact Finset.mem_singleton.mpr rfl
end

def m_ex {agents : Type} : modelECL agents  :=
{ f := 
  { states := single
    hs := single_nonempty
    E  :=  truly_playable_from_finite
    { E := λ s G, {{single.one}}
      liveness := 
      begin 
        intro _ _ hf
        simp at hf
        rw Set.ext_iff at hf
        simp at hf
        apply hf single.one
        refl
      end
      safety:=
        begin
          intro _ _, simp at *
          exact univ_single
        end
      N_max :=
        begin
          intro _ _ hxc, simp at *
          rw ←univ_single at *
          have hcond : {single.one} ≠ (∅: Set single)

            { intro hf
              rw Set.ext_iff at hf
              simp at *
              apply hf single.one
              refl, }
          simp [hcond] at *, by_contradiction
          have hex: ∃ x, x ∈ X:= nonempty_def.mp (ne_empty_iff_nonempty.mp hxc)
          cases hex with s hs
          cases s
          rw ←singleton_subset_iff at hs
          rw ←univ_single at hs
          exact h (univ_subset_iff.mp hs)
        end
      mono :=
        begin
          intro _ _ _ _ hxy hx
          simp [←univ_single] at *
          rw hx at hxy
          exact univ_subset_iff.mp hxy
        end
      superadd :=
      begin
        intro _ _ _ _ _ hX hY hGF
        simp at *
        simp[hX, hY]
      end }
    rel := λ a s, {s}
    rfl := by simp
    sym :=
    begin
      intro i s t h
      simp at *
      rw h
    end
    trans :=
    begin
      intro i s t u hst htu
      simp at *
      simp[hst, htu]
    end, }
  v := λ _, {}, }

lemma nprfalseCLK {agents : Type} :
  ¬ (axCLK (formCLK.bot : formCLK agents )) :=
begin
  apply (mt (soundnessCLK (@formCLK.bot agents)))
  intro hf 
  simp[global_valid, valid_m, s_entails_CLK] at hf
  apply hf (m_ex)
  exact single.one
end
