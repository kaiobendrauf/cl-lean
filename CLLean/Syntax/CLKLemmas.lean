/-
Authors: Kai Obendrauf

This file contains proofs for a variety of lemmas about individual knowledge.
-/

import CLLean.Syntax.consistency
open Set

-- ⊢ ((¬ φ) → (¬ (K i φ)))
lemma n_imp_nk {agents form : Type} [pf : Pformula_ax form] [kf : Kformula agents form]
  {φ : form} {i : agents} : ⊢'  ((¬' φ) →' (¬' (K' i φ))) := by
  apply by_contra_ax
  apply imp_switch
  apply cut
  apply kf.T
  exact likemp

-- ⊢ ψ → φ ⇒ ⊢ ¬ (K i φ) → ¬ (K i ψ)
lemma nk_imp_nk {agents form : Type} [pf : Pformula_ax form] [kf : Kformula agents form]
  (i : agents) {φ ψ : form} (h : ⊢' (ψ →' φ)) : ⊢' ((¬' (K' i φ)) →' (¬' (K' i ψ))) := by
  apply contrapos.mpr
  apply MP' (RN _ _ h)
  apply K

-- ⊢ ¬ K i (¬ K i φ) → K i φ
lemma nnk_imp_k  {agents form : Type} [pf : Pformula_ax form] [kf : Kformula agents form]
  {i : agents} {φ : form} :
  ⊢' ((¬' (K' i (¬' (K' i (φ))))) →' (K' i (φ))) := by
  apply contrapos.mp
  apply cut (Five _ _)
  exact dni

-- ⊢ (∧{φ ∈ φs} K i φ) → K i (∧{φ ∈ φs} φ)
lemma knows_conjunction  {agents form : Type} [pf : Pformula_ax form] [kf : Kformula agents form]
  {i : agents} {φs : List (form)} :
  ⊢' ((finite_conjunction (List.map (K' i) φs)) →' (K' i (finite_conjunction φs))) := by
induction φs
{ apply mp
  exact p1 _ _
  apply RN
  exact prtrue, }
{ apply cut
  { apply imp_and_imp
    exact φs_ih, }
  { exact (mp _ _ double_imp (cut2 (p6 _ _) (cut (p5 _ _) 
    (cut (mp _ _ (K _ _ _) ((RN _ _ )(p4 _ _))) (K _ _ _))))), }, }

-- ⊢ ¬ K i (∨{φ ∈ φs} φ) → (∨{φ ∈ φs} ¬ K i φ)
lemma nk_disjunction {agents form : Type} [pf : Pformula_ax form] [kf : Kformula agents form]
  (i : agents) (φs : List (form)) :
  ⊢' ((¬' (K' i (¬' (finite_disjunction φs)))) →' 
    (finite_disjunction (List.map (λ φ, ¬' (K' i (¬' φ))) φs))) := by
  apply cut (nk_imp_nk _ (iff_r demorans_fin_dis))
  apply cut
  apply contrapos.mpr
  apply knows_conjunction
  apply cut
  apply iff_l
  apply demorans_fin_con
  have heq : List.map ¬' (List.map (K' i) (List.map ¬' φs)) = 
    List.map (λ (φ : form), ¬' (K' i (¬' φ))) φs:= by simp only [List.map_map]
  rw heq
  exact iden

lemma everyone_empty {agents form : Type} [hN : Fintype agents] 
  [pf : Pformula_ax form] [kf : Kformula agents form] {φ : form} 
  {G : Set (agents)} (hG : G = ∅ ):
  ⊢' (E' G φ) := by
  rw hG
  simp only [finite_empty_to_finset, Finset.to_list_empty, List.map_nil, finite_conjunction_nil
              explosion]

lemma everyone_knows_pr  {agents form : Type} [hN : Fintype agents] 
  [pf : Pformula_ax form] [kf : Kformula agents form] 
  {φ : form} {G : Set (agents)} (h : ⊢' φ) : ⊢' (E' G φ) := by
  apply finite_conj_forall_iff.mp
  simp only [List.mem_map, Finset.mem_to_list, Finite.mem_to_finset, forall_exists_index, and_imp
             forall_apply_eq_imp_iff₂]
  intro i hi
  apply RN
  exact h

lemma everyone_knows_imp_knows  {agents form : Type} [hN : Fintype agents] 
  [pf : Pformula_ax form] [kf : Kformula agents form] {φ : form}
  {G : Set (agents)} {i : agents} (hi : i ∈ G) :
  ⊢' ((E' G φ) →' (K' i φ)) := by
  apply finite_conj_imp
  simp only [List.mem_map, Finset.mem_to_list, Finite.mem_to_finset]
  apply Exists.intro i
  exact and.intro hi rfl

lemma K_everyone  {agents form : Type} [hN : Fintype agents] 
  [pf : Pformula_ax form] [kf : Kformula agents form] 
  {φ ψ : form} {G : Set (agents)} :
  ⊢' ((E' G (φ →' ψ)) →' ((E' G φ) →' (E' G ψ))) := by
  apply imp_switch
  simp only
  induction (Finset.to_list (Finite.toFinset (Set.toFinite G)))
  { simp only [List.map_nil, finite_conjunction_nil, ax_not_bot_imp, explosion],}
  { simp only [List.map, finite_conjunction_cons]
    apply imp_and_and_and_imp
    apply ax_and.mpr
    split
    { apply cut2
      apply K
      exact likemp, }
    { exact ih, }, }
