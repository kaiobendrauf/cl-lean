import syntax.consistency
import data.set.finite
import data.fintype.basic
import data.set.basic 
open set

-- ⊢ ((¬ φ) → (¬ (K i φ)))
def n_imp_nk {agents : Type} [hN : fintype agents] {form : Type} [ft : formula form] 
  [fax : formula_ax form] [kf : Kformula agents form]
  {φ : form} {i : agents} : 
  ax ((¬' φ) →' (¬' (K' i φ))) :=
begin
  apply by_contra_ax,
  apply imp_switch,
  apply cut,
  apply kf.T,
  rw ft.notdef,
  exact likemp,
end

lemma nk_imp_nk {agents : Type} [hN : fintype agents] {form : Type} [ft : formula form] 
  [fax : formula_ax form] [kf : Kformula agents form] 
  {i : agents} {φ ψ : form} (h : ax (ψ →' φ)) :
  ax ((¬' (K' i φ)) →' (¬' (K' i ψ))) :=
begin
  apply contrapos.mpr,
  apply MP' (RN _ _ h),
  apply K,
end

lemma knows_conjunction {agents : Type} [hN : fintype agents] {form : Type} [ft : formula form] 
  [fax : formula_ax form] [kf : Kformula agents form] 
  {i : agents} {φs : list (form)} :
  ax ((finite_conjunction (list.map (K' i) φs)) →' (K' i (finite_conjunction φs))) :=
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

lemma nk_disjunction {agents : Type} [hN : fintype agents] {form : Type} [ft : formula form] 
  [fax : formula_ax form] [kf : Kformula agents form] 
  {i : agents} {φs : list (form)} :
  ax ((¬' (K' i (¬' (finite_disjunction φs)))) →' 
    (finite_disjunction (list.map (λ φ, ¬' (K' i (¬' φ))) φs))) :=
begin
  apply cut (nk_imp_nk (iff_r demorans_fin_dis)),
  apply cut,
  apply contrapos.mpr,
  apply knows_conjunction,
  apply cut,
  apply iff_l,
  apply demorans_fin_con,
  have heq : list.map ¬' (list.map (K' i) (list.map ¬' φs)) = 
    list.map (λ (φ : form), ¬' (K' i (¬' φ))) φs, from by simp,
  rw heq,
  exact iden,
end

lemma everyone_empty {agents : Type} [hN : fintype agents] {form : Type} [ft : formula form] 
  [fax : formula_ax form] [kf : Kformula agents form] {φ : form} :
  ax (E' ∅ φ) :=
begin
  rw kf.edef,
  simp,
  exact prtrue,
end

lemma everyone_knows_pr {agents : Type} [hN : fintype agents] {form : Type} [ft : formula form] 
  [fax : formula_ax form] [kf : Kformula agents form] {φ : form} {G : set (agents)} (h : ax φ) :
  ax (E' G φ) :=
begin
  rw kf.edef,
  apply finite_conj_forall_iff.mp,
  simp,
  intros i hi,
  apply RN,
  exact h,
end

lemma everyone_knows_imp_knows {agents : Type} [hN : fintype agents] {form : Type} [ft : formula form] 
  [fax : formula_ax form] [kf : Kformula agents form] {φ : form} {G : set (agents)} {i : agents} (hi : i ∈ G) :
  ax ((E' G φ) →' (K' i φ)) :=
begin
  rw kf.edef,
  apply finite_conj_imp,
  simp,
  apply exists.intro i,
  exact and.intro hi rfl,
end

lemma K_everyone {agents : Type} [hN : fintype agents] {form : Type} [ft : formula form] 
  [fax : formula_ax form] [kf : Kformula agents form] {φ ψ : form} {G : set (agents)} :
  ax ((E' G (φ →' ψ)) →' ((E' G φ) →' (E' G ψ))) :=
begin
  rw kf.edef,
  apply imp_switch,
  simp,
  induction (finset.to_list (finite.to_finset (finite.of_fintype G))),
  { simp,
    exact prtrue, },
  { simp,
    apply imp_and_and_and_imp,
    apply and_ax _ ih,
    apply cut2,
    apply K,
    exact likemp, },
end

