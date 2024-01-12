/-
Authors: Kai Obendrauf
Following the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley

This file contains the proof that CL is complete.
Given completeness we also prove that CL does not prove ⊥.
-/

import CLLean.Semantics.semanticsCL

open Set

----------------------------------------------------------
-- Soundness
----------------------------------------------------------

theorem soundnessCL {agents : Type} (φ : formCL agents) : _⊢ φ → _⊨ φ := by
  intro h
  induction h
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
    simp only [s_entails_CL, imp_false] at *
    exact (h1 hf) (h2 hf)
  -- case Prop4
  · intro m s h1 h2
    simp only [s_entails_CL] at *
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
    simp only [s_entails_CL, imp_false] at *
    exact h1 hf h2
  -- case ⊥
  · intro m s h1
    simp only [s_entails_CL, setOf_false] at *
    exact m.f.E.liveness s _ h1
  -- case ⊤
  · intro m s
    simp only [s_entails_CL, IsEmpty.forall_iff, setOf_true]
    exact m.f.E.safety s _
  -- case N
  · intro m s h1
    apply m.f.E.N_max
    by_contra h
    simp only [s_entails_CL, imp_false] at *
    exact h1 h
  -- case M
  · intro m s
    apply m.f.E.mono s _ _ { t | (s_entails_CL m t _) }
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
    have heq : {t | (s_entails_CL m t _) } = {t | (s_entails_CL m t _) }:= by
        apply Set.ext
        intro u
        apply Iff.intro
        · intro hu
          exact (ih m u).left hu
        · intro hu
          exact (ih m u).right hu
    apply And.intro
    · intro h1
      simp only [s_entails_CL, ←heq] at *
      exact h1
    · intro h1
      simp only [s_entails_CL, heq] at *
      exact h1

----------------------------------------------------------
-- CL does not prove ⊥
----------------------------------------------------------

lemma nprfalseCL {agents : Type} : ¬ (_⊢ (_⊥ : formCL agents)) := by
  -- prove with the contrapositive of soundness : ¬ ⊨ ⊥
  apply (mt (soundnessCL (@formCL.bot agents)))
  -- assume by contradiction : ⊨ ⊥
  intro hf
  -- ⊨ ⊥ only holds if no model with states exists
  simp[global_valid, valid_m, s_entails_CL] at hf
  -- we create an example model with a single state to prove a contradiction
  exact hf (m_ex_CM) single.one
