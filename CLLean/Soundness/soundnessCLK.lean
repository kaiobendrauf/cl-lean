/-
Authors: Kai Obendrauf
Following the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley

This file contains the proof that CLK is complete.
Given completeness we also prove that CLK does not prove ⊥
  by coming up with a simple instance of a coalition model.
-/

import Mathlib.Tactic
import CLLean.Semantics.semanticsCLK

open Set Logic

----------------------------------------------------------
-- Soundness
----------------------------------------------------------

---------------------- Soundness ----------------------

theorem soundnessCLK {agents: Type} (φ : formCLK agents) :
  _⊢ φ → _⊨ φ := by
  intro h
  induction' h
  -- case Prop1
  · intro m s h1 _
    exact h1
  -- case Prop2
  · intro m s h1 h2 h3
    apply h1
    · exact h3
    · apply h2
      exact h3
  -- case Prop3
  · intro m s h1 h2
    by_contra hf
    simp [s_entails_CLK] at *
    exact (h1 hf) (h2 hf)
  -- case Prop4
  · intro m s h1 h2
    simp [s_entails_CLK] at *
    exact And.intro h1 h2
  -- case Prop5
  · intro m s h1
    exact h1.left
  -- case Prop6
  · intro m s h1
    exact h1.right
  -- case Prop7
  · intro m s h1 h2
    by_contra hf
    simp [s_entails_CLK] at *
    exact h1 hf h2
  -- case ⊥
  · intro m s h1
    simp [s_entails_CLK] at *
    exact m.f.E.liveness s _ h1
  -- case ⊤
  · intro m s
    simp [s_entails_CLK]
    exact m.f.E.safety s _
  -- case N
  · intro m s h1
    apply m.f.E.N_max
    by_contra h
    simp [s_entails_CLK] at *
    exact h1 h
  -- case M
  · intro m s
    apply m.f.E.mono s _ _ { t | (s_entails_CLK m t _) }
    intro t h1
    exact h1.left
  -- case S
  · intro m s h1
    exact m.f.E.superadd s _ _ _ _ h1.left h1.right (by assumption)
  -- case MP
  case MP _ hImp ih =>
    intro m s
    apply hImp
    exact ih m s
  -- case Eq
  case Eq ih =>
    intro m s
    have heq : {t | (s_entails_CLK m t _) } = {t | (s_entails_CLK m t _) }:= by
        apply Set.ext
        intro u
        apply Iff.intro
        · intro hu
          exact (ih m u).left hu
        · intro hu
          exact (ih m u).right hu
    apply And.intro
    · intro h1
      simp only [s_entails_CLK, ←heq] at *
      exact h1
    · intro h1
      simp only [s_entails_CLK, heq] at *
      exact h1
  -- K
  · intro m s h1 h2 t ht
    exact h1 t ht (h2 t ht)
  -- T
  · intro m s h
    exact h s (m.f.rfl _ s)
  -- Four
  · intro m s h t ht u hu
    exact h u (m.f.trans _ s t u ht hu)
  -- Five
  · intro m s h1 t ht ht1
    apply h1
    intro u hu
    apply ht1
    exact m.f.trans _ _ _ _ (m.f.sym _ _ _ ht) hu
  -- RN
  · intros m s t hst
    rename_i _ _ _ ih
    apply ih

----------------------------------------------------------
-- CL does not prove ⊥
----------------------------------------------------------
-- create an example Model
inductive single : Type
  | one: single

lemma univ_single : (Set.univ: Set single) = {single.one} :=  by
  rw [eq_comm, Set.eq_univ_iff_forall]
  intro x
  cases x
  simp

instance single_nonempty : Nonempty single :=  by
  apply exists_true_iff_nonempty.mp
  apply Exists.intro single.one
  exact trivial

instance single_finite : Fintype single :=  by
  refine {elems := {single.one}, complete := (by simp)}

def e_ex {agents : Type} : playable_effectivity_struct agents single :=
{ E := λ _ _ => {{single.one}}
  liveness :=  by
    intros _ _ hf
    simp [Set.ext_iff] at hf

  safety:= by
      intro _ _
      simp at *
      exact univ_single

  N_max := by
      intros s X hxc
      simp[←univ_single] at *
      have hcond : {single.one} ≠ (∅: Set single) := by
        simp[Set.ext_iff]
      simp [hcond] at *
      by_contra
      rename_i h
      have hex: ∃ x, x ∈ X := nonempty_def.mp (Set.nonempty_iff_ne_empty.mpr hxc)
      cases' hex with s hs
      cases s
      rw [←singleton_subset_iff, ←univ_single] at hs
      exact h (univ_subset_iff.mp hs)
  mono := by
      intro _ _ _ _ hxy hx
      simp [←univ_single] at *
      rw [hx] at hxy
      exact univ_subset_iff.mp hxy
  superadd := by
    intro _ _ _ _ _ hX hY _
    simp at *
    simp[hX, hY] }

def m_ex {agents : Type} : modelECL agents  :=
{ f :=
  { states := single
    hs := single_nonempty
    E  :=  truly_playable_from_finite e_ex
    rel := λ _ s => {s}
    rfl := by simp
    sym := by
      intro i s t _
      simp at *
    trans := by
      intro i s t u _ _
      simp at * }
  v := λ _ => {} }


lemma nprfalseCLK {agents : Type} [hN : Fintype agents] :
  ¬ (axCLK (formCLK.bot : formCLK agents )) := by
  apply (mt (soundnessCLK (@formCLK.bot agents)))
  intro hf
  simp[global_valid, valid_m, s_entails_CLK] at hf
  apply hf (m_ex)
  exact single.one
