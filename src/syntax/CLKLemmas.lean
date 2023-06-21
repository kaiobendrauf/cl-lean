/-
Authors : Kai Obendrauf

This file contains proofs for a variety of lemmas about individual knowledge.
-/

import syntax.consistency
open set

-- ⊢ ((¬ φ) → (¬ (K i φ)))
def n_imp_nk {agents form : Type} [pf : Pformula_ax form] [kf : Kformula agents form]
  {φ : form} {i : agents} : ⊢'  ((¬' φ) →' (¬' (K' i φ))) :=
begin
  apply by_contra_ax,
  apply imp_switch,
  apply cut,
  apply kf.T,
  exact likemp,
end

-- ⊢ ψ → φ ⇒ ⊢ ¬ (K i φ) → ¬ (K i ψ)
lemma nk_imp_nk {agents form : Type} [pf : Pformula_ax form] [kf : Kformula agents form]
  (i : agents) {φ ψ : form} (h : ⊢' (ψ →' φ)) : ⊢' ((¬' (K' i φ)) →' (¬' (K' i ψ))) :=
begin
  apply contrapos.mpr,
  apply MP' (RN _ _ h),
  apply K,
end

-- ⊢ ¬ K i (¬ K i φ) → K i φ
lemma nnk_imp_k  {agents form : Type} [pf : Pformula_ax form] [kf : Kformula agents form]
  {i : agents} {φ : form} :
  ⊢' ((¬' (K' i (¬' (K' i (φ))))) →' (K' i (φ))) :=
begin
  apply contrapos.mp,
  apply cut (Five _ _),
  exact dni,
end

-- ⊢ (∧{φ ∈ φs} K i φ) → K i (∧{φ ∈ φs} φ)
lemma knows_conjunction  {agents form : Type} [pf : Pformula_ax form] [kf : Kformula agents form]
  {i : agents} {φs : list (form)} :
  ⊢' ((finite_conjunction (list.map (K' i) φs)) →' (K' i (finite_conjunction φs))) :=
begin
induction φs,
{ apply mp,
  exact p1 _ _,
  apply RN,
  exact prtrue, },
{ apply cut,
  { apply imp_and_imp,
    exact φs_ih, },
  { exact (mp _ _ double_imp (cut2 (p6 _ _) (cut (p5 _ _) 
    (cut (mp _ _ (K _ _ _) ((RN _ _ )(p4 _ _))) (K _ _ _))))), }, },
end

-- ⊢ ¬ K i (∨{φ ∈ φs} φ) → (∨{φ ∈ φs} ¬ K i φ)
lemma nk_disjunction {agents form : Type} [pf : Pformula_ax form] [kf : Kformula agents form]
  (i : agents) (φs : list (form)) :
  ⊢' ((¬' (K' i (¬' (finite_disjunction φs)))) →' 
    (finite_disjunction (list.map (λ φ, ¬' (K' i (¬' φ))) φs))) :=
begin
  apply cut (nk_imp_nk _ (iff_r demorans_fin_dis)),
  apply cut,
  apply contrapos.mpr,
  apply knows_conjunction,
  apply cut,
  apply iff_l,
  apply demorans_fin_con,
  have heq : list.map ¬' (list.map (K' i) (list.map ¬' φs)) = 
    list.map (λ (φ : form), ¬' (K' i (¬' φ))) φs, from by simp only [list.map_map],
  rw heq,
  exact iden,
end

lemma everyone_empty {agents form : Type} [hN : fintype agents] 
  [pf : Pformula_ax form] [kf : Kformula agents form] {φ : form} 
  {G : set (agents)} (hG : G = ∅ ):
  ⊢' (E' G φ) :=
begin
  rw hG,
  simp only [finite_empty_to_finset, finset.to_list_empty, list.map_nil, finite_conjunction_nil, 
              explosion],
end

lemma everyone_knows_pr  {agents form : Type} [hN : fintype agents] 
  [pf : Pformula_ax form] [kf : Kformula agents form] 
  {φ : form} {G : set (agents)} (h : ⊢' φ) : ⊢' (E' G φ) :=
begin
  apply finite_conj_forall_iff.mp,
  simp only [list.mem_map, finset.mem_to_list, finite.mem_to_finset, forall_exists_index, and_imp,
             forall_apply_eq_imp_iff₂],
  intros i hi,
  apply RN,
  exact h,
end

lemma everyone_knows_imp_knows  {agents form : Type} [hN : fintype agents] 
  [pf : Pformula_ax form] [kf : Kformula agents form] {φ : form}
  {G : set (agents)} {i : agents} (hi : i ∈ G) :
  ⊢' ((E' G φ) →' (K' i φ)) :=
begin
  apply finite_conj_imp,
  simp only [list.mem_map, finset.mem_to_list, finite.mem_to_finset],
  apply exists.intro i,
  exact and.intro hi rfl,
end

lemma K_everyone  {agents form : Type} [hN : fintype agents] 
  [pf : Pformula_ax form] [kf : Kformula agents form] 
  {φ ψ : form} {G : set (agents)} :
  ⊢' ((E' G (φ →' ψ)) →' ((E' G φ) →' (E' G ψ))) :=
begin
  apply imp_switch,
  simp only,
  induction (finset.to_list (finite.to_finset (finite.of_fintype G))),
  { simp only [list.map_nil, finite_conjunction_nil, ax_not_bot_imp, explosion],},
  { simp only [list.map, finite_conjunction_cons],
    apply imp_and_and_and_imp,
    apply ax_and.mpr,
    split,
    { apply cut2,
      apply K,
      exact likemp, },
    { exact ih, }, },
end

