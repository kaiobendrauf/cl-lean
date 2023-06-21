/-
Authors: Kai Obendrauf

This file contains proofs for a variety of lemmas about common knowledge.
-/

import syntax.consistency

lemma c_imp_kc {agents form : Type} [hN : fintype agents]
  [pf : Pformula_ax form] [kf : Kformula agents form] [cf : Cformula agents form]
  {φ : form} {G : set (agents)} {i : agents} (hi : i ∈ G): 
  ⊢' ((C' G φ) →' (K' i (C' G φ))) :=
begin
  apply cut, apply C,
  apply cut, apply finite_conj_forall_imp (K' i (φ ∧' (C' G φ))),
  simp only [list.mem_map, finset.mem_to_list, set.finite.mem_to_finset],
  apply exists.intro i,
  simp only [hi, eq_self_iff_true, and_self],
  apply mp,
  apply K,
  apply RN,
  exact p6 _ _,
end

lemma c_imp_k {agents form : Type} [hN : fintype agents]
  [pf : Pformula_ax form] [kf : Kformula agents form] [cf : Cformula agents form]
  {φ : form} {G : set (agents)} {i : agents} (hi : i ∈ G): 
  ⊢' ((C' G φ) →' (K' i φ)) :=
begin
  apply cut, apply C,
  apply cut, apply finite_conj_forall_imp (K' i (φ ∧' (C' G φ))),
  simp only [list.mem_map, finset.mem_to_list, set.finite.mem_to_finset],
  apply exists.intro i,
  simp only [hi, eq_self_iff_true, and_self],
  apply mp,
  apply K,
  apply RN,
  exact p5 _ _,
end

lemma c_imp {agents form : Type} [hN : fintype agents]
  [pf : Pformula_ax form] [kf : Kformula agents form] [cf : Cformula agents form]
  {φ : form} {G : set (agents)} {i : agents} (hi : i ∈ G) : 
  ⊢' ((C' G φ) →' φ) := cut (c_imp_k hi) (T φ i)