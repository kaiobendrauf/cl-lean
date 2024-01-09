/-
Authors: Kai Obendrauf

This file contains proofs for a variety of lemmas about common knowledge.
-/

import CLLean.Syntax.propLemmas

open Logic

lemma c_imp_kc {agents form : Type} [hN : Fintype agents]
  [pf : Pformula_ax form] [kf : Kformula agents form] [cf : Cformula agents form]
  {φ : form} {G : Set (agents)} {i : agents} (hi : i ∈ G):
  ⊢' ((C' G φ) →' (K' i (C' G φ))) := by
  apply cut
  apply C
  apply cut
  apply finite_conj_forall_imp (K' i (φ ∧' (C' G φ)))
  simp only [List.mem_map, Finset.mem_toList, Set.Finite.mem_toFinset]
  apply Exists.intro i
  simp only [hi, and_self]
  apply mp
  apply K
  apply RN
  exact p6 _ _

lemma c_imp_k {agents form : Type} [hN : Fintype agents]
  [pf : Pformula_ax form] [kf : Kformula agents form] [cf : Cformula agents form]
  {φ : form} {G : Set (agents)} {i : agents} (hi : i ∈ G):
  ⊢' ((C' G φ) →' (K' i φ)) := by
  apply cut
  apply C
  apply cut
  apply finite_conj_forall_imp (K' i (φ ∧' (C' G φ)))
  simp only [List.mem_map, Finset.mem_toList, Set.Finite.mem_toFinset]
  apply Exists.intro i
  simp only [hi, eq_self_iff_true, and_self]
  apply mp
  apply K
  apply RN
  exact p5 _ _

lemma c_imp {agents form : Type} [Fintype agents]
  [Pformula_ax form] [Kformula agents form] [Cformula agents form]
  {φ : form} {G : Set (agents)} {i : agents} (hi : i ∈ G) :
  ⊢' ((C' G φ) →' φ) := cut (c_imp_k hi) (T φ i)
