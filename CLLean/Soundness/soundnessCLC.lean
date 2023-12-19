/-
Authors: Kai Obendrauf
Following the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley

This file contains the proof that CLC is complete.
Given completeness we also prove that CLC does not prove ⊥
  by coming up with a simple instance of a coalition model. 
-/

import Mathlib.Tactic
import CLLean.Semantics.semanticsCLC
local attribute [instance] classical.prop_decidable

open Set

----------------------------------------------------------
-- Soundness
----------------------------------------------------------

---------------------- Soundness ----------------------

theorem soundnessCLC {agents: Type} [hN : Fintype agents] (φ : formCLC agents) : 
  '⊢ φ → '⊨ φ := by
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
    simp [s_entails_CLC]
    exact m.f.E.safety s G, }

  -- N
  { intro m s h1
    apply m.f.E.N_max
    by_contradiction
    exact h1 h, }

  -- M
  { intro m s
    apply m.f.E.mono s G {t : m.f.states | m; t '⊨ (φ _∧ φ_1)}
      {t : m.f.states | m; t '⊨ φ}
    intro t h1
    unfold s_entails_CLC at h1
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
      simp only [s_entails_CLC, ←heq] at *
      exact h1, }
    { intro h1
      simp only [s_entails_CLC, heq] at *
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
  
  -- C
  { intro m s h
    rw s_entails_CLC_conjunction
    intro ψ hψ
    simp only [List.mem_map, Finset.mem_to_list, Finite.mem_to_finset] at hψ
    cases hψ with i hi, cases hi with hi hψ
    rw [←(hψ)]
    unfold s_entails_CLC
    intro t hts
    split
    { apply h
      split
      { split
        { show ∀ a, a ∈ [i] → a ∈ G
          simp
          exact hi, }
        { apply Exists.intro []
          unfold C_path
          exact hts, }, }, }
    { intro u hu, cases hu with js hu, cases hu with hjs hu, cases hu with us htu
      apply h
      split
      { split
        { show ∀ a, a ∈ (i :: js) → a ∈ G
          simp
          exact and.intro hi hjs, }
        { apply Exists.intro (t :: us)
          unfold C_path
          exact and.intro hts htu, }, }, }, }

  -- RN
  { intro m s t hst
    apply ih, }

  -- RC
  { intro m s hs t hC
    cases hC with is hC
    cases hC with his hC
    cases hC with ss hC
    unfold global_valid valid_m s_entails_CLC at *
    induction' is with i is ih_is
    { by_contradiction
      apply hC, }
    { have ih' := ih
      specialize ih m s hs
      rw s_entails_CLC_conjunction at ih
      specialize ih (_K i (φ _∧ φ_1))
      simp [s_entails_CLC] at ih
      simp[C_path] at *
      cases ss with u ss
      { simp[C_path] at *
         specialize ih his.left t hC
        exact ih.left, }
      { simp[C_path] at *
        specialize @ih_is hN _ _ _ h m u
        apply ih_is
        { apply and.elim_right
          apply ih his.left u hC.left, }
          { intro m s hs
            specialize ih' m s hs
            simp [s_entails_CLC_conjunction, s_entails_CLC] at *
            exact ih', }
          exact his.right
          exact hC.right, }, }, }

----------------------------------------------------------
-- CL does not prove ⊥
----------------------------------------------------------
-- create an example Model
inductive single : Type
  | one: single

lemma univ_single : (Set.univ: Set single) = {single.one} :=  by
  rw eq_comm
  rw Set.eq_univ_iff_forall
  intro x
  cases x
  simp

instance single_nonempty : Nonempty single :=  by
  apply exists_true_iff_nonempty.mp
  apply Exists.intro single.one
  exact trivial

instance single_finite : Fintype single :=  by
  refine {elems := {single.one}, complete := _}
  intro x
  cases x
  exact Finset.mem_singleton.mpr rfl

def m_ex {agents : Type} : modelECL agents  :=
{ f := 
  { states := single
    hs := single_nonempty
    E  :=  truly_playable_from_finite
    { E := λ s G, {{single.one}}
      liveness :=  by
        intro _ _ hf
        simp at hf
        rw Set.ext_iff at hf
        simp at hf
        apply hf single.one
        refl
      safety:= by
          intro _ _, simp at *
          exact univ_single
      N_max := by
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
      mono := by
          intro _ _ _ _ hxy hx
          simp [←univ_single] at *
          rw hx at hxy
          exact univ_subset_iff.mp hxy
      superadd := by
        intro _ _ _ _ _ hX hY hGF
        simp at *
        simp[hX, hY]
    rel := λ a s, {s}
    rfl := by simp
    sym := by
      intro i s t h
      simp at *
      rw h
    trans := by
      intro i s t u hst htu
      simp at *
      simp[hst, htu]
  v := λ _, {}, }

lemma nprfalseCLC {agents : Type} [hN : Fintype agents] :
  ¬ (axCLC (formCLC.bot : formCLC agents )) := by
  apply (mt (soundnessCLC (@formCLC.bot agents)))
  intro hf 
  simp[global_valid, valid_m, s_entails_CLC] at hf
  apply hf (m_ex)
  exact single.one
