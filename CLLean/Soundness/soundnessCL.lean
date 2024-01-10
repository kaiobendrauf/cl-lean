/-
Authors: Kai Obendrauf
Following the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley

This file contains the proof that CL is complete.
Given completeness we also prove that CL does not prove ⊥
  by coming up with a simple instance of a coalition model.
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
-- create an example Model
inductive single : Type
  | one : single

lemma univ_single : (Set.univ : Set single) = {single.one} :=  by
  rw [eq_comm]
  rw [Set.eq_univ_iff_forall]
  intro x
  cases x
  simp only [mem_singleton_iff]

instance single_nonempty : Nonempty single :=  by
  apply exists_true_iff_nonempty.mp
  apply Exists.intro single.one
  exact trivial

def m_ex {agents : Type} : modelCL agents :=
{ f :=
  { states := single
    hs := single_nonempty
    E  :=
    { E := λ _ _ => {{single.one}}
      liveness := by
        intro _ _ hf
        simp only [mem_singleton_iff] at hf
        rw [Set.ext_iff] at hf
        simp only [mem_empty_iff_false, mem_singleton_iff, iff_true, forall_const] at hf
      safety := by
          intro _ _
          simp only [mem_singleton_iff] at *
          exact univ_single
      N_max := by
          intro s X hxc
          simp only [mem_singleton_iff] at *
          rw [←univ_single] at *
          have hcond : {single.one} ≠ (∅ : Set single)
          · intro hf
            rw [Set.ext_iff] at hf
            simp only [compl_univ_iff, mem_singleton_iff, mem_empty_iff_false, iff_false,
              not_true_eq_false, forall_const] at *
          simp only [compl_univ_iff, ne_eq, singleton_ne_empty, not_false_eq_true] at *
          by_contra
          have hex : ∃ x, x ∈ X := nonempty_def.mp (nonempty_iff_ne_empty.mpr hxc)
          cases hex
          cases s
          case _ h s hs =>
            rw [←singleton_subset_iff] at hs
            rw [←univ_single] at hs
            exact h (univ_subset_iff.mp hs)
      mono := by
          intro _ _ _ _ hxy hx
          simp only [← univ_single, mem_singleton_iff] at *
          rw [hx] at hxy
          exact univ_subset_iff.mp hxy
      superadd := by
        intro _ _ _ _ _ hX hY _
        simp only [mem_singleton_iff] at *
        simp only [hX, hY, inter_self] } },
  v := λ _ => {}, }


lemma nprfalseCL {agents : Type} : ¬ (_⊢ (_⊥ : formCL agents)) := by
  -- prove with the contrapositive of soundness : ¬ ⊨ ⊥
  apply (mt (soundnessCL (@formCL.bot agents)))
  -- assume by contradiction : ⊨ ⊥
  intro hf
  -- ⊨ ⊥ only holds if no model with states exists
  simp[global_valid, valid_m, s_entails_CL] at hf
  -- we create an example model with a single state to prove a contradiction
  exact hf (m_ex) single.one
