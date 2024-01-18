/-
Authors: Kai Obendrauf
Following the paper "A Modal Logic for Coalitional Power in Games" by Mark Pauly
the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley
and the paper "Coalition Logic with Individual, Distributed and Common Knowledge
by Thomas Ågotnes and Natasha Alechina.

This file contains the structure definitions for frames and models for CL and CLK.
Note that CLC uses CLK frames and models.
Simple example models are created for each.
-/

import CLLean.Semantics.playability
import Mathlib.Order.Filter.Basic

open Set


----------------------------------------------------------
-- Coalition Frames and Models
----------------------------------------------------------
structure frameCL (agents : Type) :=
(states : Type)
(hs     : Nonempty states)
(E      : playable_effectivity_struct agents states)

structure modelCL (agents : Type) :=
(f : frameCL agents)
(v : ℕ → Set f.states)

----------------------------------------------------------
-- Epistemic Coalition Frames and Models
----------------------------------------------------------

structure frameECL (agents : Type) :=
(states    : Type)
(hs        : Nonempty states)
(E         : truly_playable_effectivity_struct agents states)
(rel       : agents → states → Set states)
(rfl       : ∀ i s, s ∈ rel i s)
(sym       : ∀ i s t, t ∈ rel i s → s ∈ rel i t)
(trans     : ∀ i s t u, t ∈ rel i s → u ∈ rel i t → u ∈ rel i s)

structure modelECL (agents : Type) :=
(f : frameECL agents)
(v : ℕ → Set f.states)


----------------------------------------------------------
-- Example Models
----------------------------------------------------------

-- create a simple type
inductive single : Type
  | one: single

-- prove some lemmas aboout that type
lemma univ_single : (Set.univ: Set single) = {single.one} :=  by
  rw [eq_comm, Set.eq_univ_iff_forall]
  intro x
  cases x
  simp only [mem_singleton_iff]

instance single_nonempty : Nonempty single :=  by
  apply exists_true_iff_nonempty.mp
  apply Exists.intro single.one
  exact trivial

instance single_finite : Fintype single :=  by
  refine {elems := {single.one}, complete := (by simp only [Finset.mem_singleton, forall_const])}

-- example function E
def e_ex {agents : Type} : playable_effectivity_struct agents single :=
{ E := λ _ _ => {{single.one}}
  liveness :=  by
    intros _ _ hf
    simp only [mem_singleton_iff, ext_iff, mem_empty_iff_false, iff_true, forall_const] at hf

  safety:= by
      intro _ _
      simp only [mem_singleton_iff]
      exact univ_single

  N_max := by
      intros s X hxc
      simp only [← univ_single, mem_singleton_iff, compl_univ_iff] at *
      by_contra
      rename_i h
      have hex: ∃ x, x ∈ X := nonempty_def.mp (Set.nonempty_iff_ne_empty.mpr hxc)
      cases' hex with s hs
      cases s
      rw [←singleton_subset_iff, ←univ_single] at hs
      exact h (univ_subset_iff.mp hs)
  mono := by
      intro _ _ _ _ hxy hx
      simp only [← univ_single, mem_singleton_iff] at *
      rw [hx] at hxy
      exact univ_subset_iff.mp hxy
  superadd := by
    intro _ _ _ _ _ hX hY _
    simp only [mem_singleton_iff] at *
    simp only [hX, hY, inter_self] }

-- example models
def m_ex_CM {agents : Type} : modelCL agents :=
{ f :=
  { states := single
    hs := single_nonempty
    E  := e_ex }
  v := λ _ => {}, }

def m_ex_ECM {agents : Type} : modelECL agents  :=
{ f :=
  { states := single
    hs := single_nonempty
    E  :=  truly_playable_from_finite e_ex
    rel := λ _ s => {s}
    rfl := by simp only [mem_singleton_iff, forall_const, implies_true]
    sym := by
      intro i s t _
      simp only [mem_singleton_iff]
    trans := by
      intro i s t u _ _
      simp only [mem_singleton_iff] }
  v := λ _ => {} }
