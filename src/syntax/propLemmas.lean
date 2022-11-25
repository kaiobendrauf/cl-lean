/-
Adapted from : 
Copyright (c) 2021 Paula Neeley. All rights reserved.
Authors : Paula Neeley
-/

import syntax.formula 
import data.set.basic
import tactic.induction
local attribute [instance] classical.prop_decidable


variables {agents : Type}
 
---------------------- Helper Lemmas ----------------------


lemma MP' {form : Type} [ft : formula form] {φ ψ : form} 
-- ⊢ φ ⇒  ⊢ φ → ψ ⇒  ⊢ ψ 
  (hL : ax φ) (hImp : ax (φ →' ψ)) : ax (ψ) :=
begin
  apply mp,
  exact hImp,
  exact hL,
end

lemma iff_l {form : Type} [ft : formula form] {φ ψ : form} : 
-- ⊢ φ ↔ ψ ⇒ ⊢ φ → ψ
  ax (φ ↔' ψ) → ax (φ →' ψ) :=
begin
  rw formula.iffdef,
  exact mp _ _ (p5 _ _),
end

lemma iff_r {form : Type} [ft : formula form] {φ ψ : form} : 
-- ⊢ φ ↔ ψ ⇒ ⊢ ψ → φ
  ax (φ ↔' ψ) → ax (ψ →' φ)  :=
begin
  rw formula.iffdef,
  exact mp _ _ (p6 _ _),
end

lemma iden {form : Type} [ft : formula form] {φ : form} : 
-- ⊢ φ → φ 
  ax (φ →' φ) := 
begin
  apply mp,
  apply mp,
  exact p2 φ (φ →' φ) φ,
  apply p1,
  apply p1,
end

lemma iff_iden' {form : Type} [ft : formula form] {φ : form} : 
-- ⊢ φ ↔ φ 
  ax ((φ →' φ) ∧' (φ →' φ)) := 
begin
  apply mp,
  apply mp,
  apply p4,
  repeat {exact iden,},
end

lemma iff_iden {form : Type} [ft : formula form] {φ : form} : 
-- ⊢ φ ↔ φ 
  ax (φ ↔' φ) := 
begin
  simp[ft.iffdef],
  exact iff_iden',
end


lemma prtrue {form : Type} [ft : formula form] : 
-- ⊢ ⊤
  ax (ft.top) := 
begin
  rw ft.topdef,
  exact iden,
end


lemma not_bot {form : Type} [ft : formula form] : 
-- ⊢ ⊤
  ax (¬' ft.bot) := 
begin
  rw formula.notdef,
  exact iden,
end

lemma topnotbot {form : Type} [ft : formula form] : 
-- ⊢ ⊤ = ¬ ⊥
  ft.top = ¬' ft.bot :=
by simp[formula.notdef, ft.topdef]

lemma cut {form : Type} [ft : formula form] {φ ψ χ : form} : 
-- ⊢ (φ → ψ) ⇒  ⊢ (ψ → χ) ⇒  ⊢ (φ → χ)
 ax (φ →' ψ) → ax (ψ →' χ) → ax (φ →' χ) :=
begin
  intros h1 h2,
  apply mp,
  apply mp,
  exact p2 _ ψ _,
  apply mp,
  exact p1 _ _,
  exact h2,
  exact h1,
end 

lemma hs1 {form : Type} [ft : formula form] {φ ψ χ : form} : 
-- ⊢ (ψ → χ) → ((φ → ψ) → (φ → χ))
  ax ((ψ →' χ) →' ((φ →' ψ) →' (φ →' χ))) :=
(mp _ _ (mp _ _ (p2 _ _ _) (mp _ _ (p1 _ _) (p2 _ _ _))) (p1 _ _))

lemma likemp {form : Type} [ft : formula form] {φ ψ : form} : 
-- ⊢ φ → ((φ → ψ) → ψ)
  ax (φ →' ((φ →' ψ) →' ψ)) :=
(mp _ _ (mp _ _ hs1 (mp _ _ (p2 _ _ _) iden)) (p1 _ _))

lemma dne {form : Type} [ft : formula form] {φ : form} : 
-- ⊢ ¬ ¬ φ → φ
  ax ((¬' (¬' φ)) →' φ) :=
begin
  have h1 : ax (φ →' (φ →' φ)), from p1 _ _,
  exact (cut (cut (p1 _ _) (cut (p7 _ _) (p7 _ _))) (mp _ _ likemp h1)),
end

lemma dni {form : Type} [ft : formula form] {φ : form} : 
-- ⊢ φ → ¬ ¬ φ
  ax (φ →' (¬' (¬' φ))) :=
begin
  exact mp _ _ (p7 _ _) dne
end

lemma nnn_bot {form : Type} [ft : formula form] : 
-- ⊢ ⊤
  ax (¬' (¬' (¬' ft.bot))) := 
begin
  apply mp,
  apply dni,
  exact not_bot,
end

lemma iff_dne {form : Type} [ft : formula form] {φ : form} : 
  ax (((¬' (¬' φ)) →' φ) ∧' (φ →' (¬' (¬' φ)))) :=
begin
  apply mp,
  apply mp,
  apply p4,
  exact dne,
  exact dni,
end

lemma iff_dni {form : Type} [ft : formula form] {φ : form} : 
  ax ((φ →' (¬' (¬' φ))) ∧' ((¬' (¬' φ)) →' φ)) :=
begin
  apply mp,
  apply mp,
  apply p4,
  exact dni,
  exact dne,
end

lemma imp_if_imp_imp {form : Type} [ft : formula form] {φ ψ χ : form} : 
-- ⊢ (φ → χ) ⇒  ⊢ φ → (ψ → χ)
  ax (φ →' χ) → ax (φ →' (ψ →' χ)) :=
λ h1, mp _ _ (mp _ _ (p2 _ _ _) (mp _ _ (p1 _ _) (p1 _ _))) h1

lemma cut1 {form : Type} [ft : formula form] {φ ψ χ θ : form} : 
-- ⊢ θ → (φ → ψ) ⇒  ⊢ (ψ → χ) ⇒ ⊢ θ → (φ → χ)
  ax (θ →' (φ →' ψ)) → ax (ψ →' χ) → ax (θ →' (φ →' χ)) :=
λ h1 h2, cut h1 (mp _ _ (p2 _ _ _) (mp _ _ (p1 _ _ )h2))

lemma imp_switch {form : Type} [ft : formula form] {φ ψ χ : form} : 
-- ⊢ φ → (ψ → χ) ⇒  ⊢ ψ → (φ → χ)
  ax (φ →' (ψ →' χ)) → ax (ψ →' (φ →' χ)) :=
λ h1, mp _ _ (mp _ _ (p2 _ _ _ ) (mp _ _ (p1 _ _) (mp _ _ (p2 _ _ _) h1))) (p1 _ _)

-- ⊢ (φ → (ψ → χ)) → (ψ → (φ → χ))
lemma l2 {form : Type} [ft : formula form] {φ ψ χ : form} : 
  ax ((φ →' (ψ →' χ)) →' (ψ →' (φ →' χ))) :=
(mp _ _ (mp _ _ (p2 _ _ _) (cut (p2 _ _ _) hs1)) (mp _ _ (p1 _ _) (p1 _ _)))

-- ⊢ (φ → ψ) → ((ψ → χ) → (φ → χ))
lemma hs2 {form : Type} [ft : formula form] {φ ψ χ : form} : 
  ax ((φ →' ψ) →' ((ψ →' χ) →' (φ →' χ))) :=
(mp _ _ l2 hs1)

lemma cut2 {form : Type} [ft : formula form] {φ ψ χ θ : form} : 
-- ⊢ (φ → ψ) ⇒  ⊢ θ → (ψ → χ) ⇒ ⊢ θ → (φ → χ)
  ax (φ →' ψ) → ax (θ →' (ψ →' χ)) → ax (θ →' (φ →' χ)) :=
λ h1 h2, imp_switch (cut h1 (imp_switch h2))

-- ⊢ (φ → (φ → ψ)) → (φ → ψ)
lemma double_imp {form : Type} [ft : formula form] {φ ψ : form} : 
  ax ((φ →' (φ →' ψ)) →' (φ →' ψ)) :=
mp _ _ (p2 _ _ _) (imp_switch iden)

lemma imp_imp_iff_imp {form : Type} [ft : formula form] {θ φ ψ : form} : 
-- ⊢ θ → (φ → (φ → ψ)) ⇔ ⊢ θ → (φ → ψ)
  ax (θ →' (φ →' (φ →' ψ))) ↔ ax (θ →' (φ →' ψ)) :=
begin
  split,
  {intro h1,
  exact cut h1 double_imp},
  {intro h1,
  exact cut h1 (p1 _ _)}
end

lemma imp_shift {form : Type} [ft : formula form] {θ φ ψ χ : form} : 
-- ⊢ θ → (φ → (ψ → χ)) ⇔ ⊢ θ → (ψ → (φ → χ))
  ax (θ →' (φ →' (ψ →' χ))) ↔ ax (θ →' (ψ →' (φ →' χ))) :=
begin
  split,
  repeat {intro h1, exact cut h1 (cut2 (p1 _ _) (p2 _ _ _))}
end

lemma left_and_imp {form : Type} [ft : formula form] {φ ψ χ : form} : 
-- ⊢ ψ → ((φ ∧ ψ) → χ ) ⇒ ⊢ (φ ∧ ψ) → χ
  ax (ψ →' ((φ ∧' ψ) →' χ)) → ax ((φ ∧' ψ) →' χ) :=
λ h1, mp _ _ double_imp (cut (p6 _ _) h1)

lemma and_right_imp {form : Type} [ft : formula form] {φ ψ χ : form} : 
-- ⊢ (φ ∧ ψ) → χ  ⇔ ⊢  ψ → (φ → χ)
  ax ((φ ∧' ψ) →' χ) ↔ ax (ψ →' (φ →' χ)) :=
begin
  split, 
  {intro h1,
  exact mp _ _ (cut2 (p1 _ _) (p2 _ _ _)) (cut1 (p4 _ _) h1)},
  intro h1,
  exact left_and_imp (cut2 (p5 _ _) h1)
end

lemma not_and_subst {form : Type} [ft : formula form] {φ ψ χ : form} : 
-- ⊢ (φ ↔' ψ) ⇒ (⊢ ¬ (χ ∧ φ) ⇔ ⊢ ¬ (χ ∧ ψ))
  ax (φ ↔' ψ) → (ax (¬' (χ ∧' φ)) ↔ ax (¬' (χ ∧' ψ))) :=
begin
  intro h1, rw formula.iffdef at *, split, 
  {intro h2,
  exact mp _ _ (mp _ _ (p3 _ _) (mp _ _ (p1 _ _) h2)) 
    (cut dne (mp _ _ double_imp (cut2 
      (cut (p6 _ _) (mp _ _ (p6 _ _) h1)) 
      (cut (p5 _ _) (p4 _ _)))))},
  {intro h2,
  exact mp _ _ (mp _ _ (p3 _ _) (mp _ _ (p1 _ _) h2)) 
    (cut dne (mp _ _ double_imp (cut2 
      (cut (p6 _ _) (mp _ _ (p5 _ _) h1)) 
      (cut (p5 _ _) (p4 _ _)))))},
end

lemma not_contra {form : Type} [ft : formula form] {φ : form} : 
-- ⊢ ¬ (φ ∧ ¬ φ) 
  ax (¬' (φ ∧' (¬' φ))) :=
mp _ _ (mp _ _ (p3 _ _) (cut dne (p6 _ _))) (cut dne (p5 _ _))

lemma phi_and_true {form : Type} [ft : formula form] {φ : form} : 
-- ⊢  (φ ∧ ⊤) ↔' φ 
  ax ((φ ∧' (¬' ft.bot)) ↔' φ) :=
begin
  rw formula.iffdef at *,
  exact (mp _ _ (mp _ _ (p4 _ _) (p5 _ _)) (mp _ _ (imp_switch (p4 _ _)) not_bot))
end

lemma phi_and_true' {form : Type} [ft : formula form] {φ : form} : 
  ax (((φ ∧' (¬' ft.bot)) →' φ) ∧' (φ →' (φ ∧' (¬' ft.bot)))) :=
(mp _ _ (mp _ _ (p4 _ _) (p5 _ _)) (mp _ _ (imp_switch (p4 _ _)) not_bot))


lemma imp_and_and_imp {form : Type} [ft : formula form] {φ ψ χ θ : form} : 
-- ⊢ (φ → ψ) ∧ (χ → θ)⇒ ⊢ (φ ∧ χ) → (ψ ∧ θ)
  ax (((φ →' ψ) ∧' (χ →' θ))) → ax (((φ ∧' χ) →' (ψ ∧' θ))) :=
begin
  intro h,
  exact (mp _ _ double_imp (cut (cut (p5 _ _) (mp _ _ (p5 _ _) h)) 
    (cut2 (cut (p6 _ _) (mp _ _ (p6 _ _) h)) (p4 _ _))))
end

lemma not_contra_equiv_true {form : Type} [ft : formula form] {φ : form} : 
-- ⊢ ¬ (φ ∧ ¬ φ) ↔' ¬ ⊥
  ax ((¬' (φ ∧' (¬' φ))) ↔' (¬' ft.bot) ) :=
begin
  rw formula.iffdef at *,
  exact (mp _ _ (mp _ _ (p4 _ _) (mp _ _ (p1 _ _) not_bot)) (mp _ _ (p1 _ _) not_contra))
end

lemma contrapos {form : Type} [ft : formula form] {φ ψ : form} : 
-- ⊢ ¬ ψ → ¬ φ ⇔ ⊢ φ → ψ
  ax ((¬' ψ) →' (¬' φ)) ↔ ax (φ →' ψ) :=
begin
  split,
  intro h1,
  exact mp _ _ (p7 _ _) h1,
  intro h1,
  exact mp _ _ (cut (cut (mp _ _ hs1 dni) (mp _ _ hs2 dne)) (p7 _ _)) h1,
end

lemma contrapos' {form : Type} [ft : formula form] {φ ψ : form} : 
-- ⊢ (¬ ψ → ¬ φ) ↔ (φ → ψ)
  ax (((¬' ψ) →' (¬' φ)) ↔' (φ →' ψ)) :=
begin
  simp [ft.iffdef],
  apply mp,
  apply mp,
  apply p4,
  { apply p7, },
  { apply cut (cut (mp _ _ hs1 dni) (mp _ _ hs2 dne)) (p7 _ _),},
end

lemma iff_not {form : Type} [ft : formula form] {φ ψ : form} : 
-- ⊢ φ ↔' ψ ⇒ ⊢ ¬ φ ↔' ¬ ψ
  ax (φ ↔' ψ) → ax ((¬' ψ) ↔' (¬' φ)) :=
begin
  intro h1,
  rw formula.iffdef at *,
  have h2 : ax (φ →' ψ), from mp _ _ (p5 _ _) h1,
  have h3 : ax (ψ →' φ), from mp _ _ (p6 _ _) h1,
  rw ←contrapos at h2,
  rw ←contrapos at h3,
  exact (mp _ _ (mp _ _ (p4 _ _) h2) h3)
end

lemma contra_equiv_false {form : Type} [ft : formula form] {φ : form} : 
-- ⊢ (φ ∧ ¬ φ) ↔' ⊥
  ax (formula.iff(φ ∧' (¬' φ)) ft.bot) :=
begin
  have h1 := iff_not not_contra_equiv_true,
  rw formula.iffdef at *,
  exact (mp _ _ (mp _ _ (p4 _ _) (cut dni (cut (mp _ _ (p6 _ _) h1) dne))) 
    (cut dni (cut (mp _ _ (p5 _ _) h1) dne)))
end

lemma contra_equiv_false' {form : Type} [ft : formula form] {φ : form} : 
  ax (((φ ∧' (¬' φ)) →' ft.bot) ∧' (ft.bot →' (φ ∧' (¬' φ)))) :=
begin
  have h1 := @contra_equiv_false form ft φ,
  rw formula.iffdef at *,
  exact h1,
end

lemma contra_imp_false {form : Type} [ft : formula form] {φ : form} : 
-- ⊢ (φ ∧ ¬ φ) → ⊥
  ax ((φ ∧' (¬' φ)) →'  ft.bot) :=
mp _ _ (p5 _ _) contra_equiv_false'

lemma contra_imp_imp_false {form : Type} [ft : formula form] {φ : form} : 
-- ⊢ ¬ φ → φ → ⊥
  ax ((¬' φ) →' (φ →' ft.bot)) :=
begin
  rw ←and_right_imp,
  exact contra_imp_false,
end

lemma contra_not_imp_false_ax {form : Type} [ft : formula form] {φ : form} : 
-- ⊢ ¬ φ → ⊥ ⇒ ⊢ φ
  ax ((¬' (φ)) →' ft.bot) → ax φ :=
begin
  intro h,
  apply mp,
  exact dne,
  simp[formula.notdef] at *,
  exact h,
end

lemma contra_imp_false_not_ax {form : Type} [ft : formula form] {φ : form} : 
-- ⊢  φ → ⊥ ⇒ ⊢ ¬ φ
  ax (φ →' ft.bot) → ax (¬' (φ)) :=
begin
  intro h,
  have hnnn : ax (¬' (¬' (¬' φ))) = 
    ax ((¬' (¬' φ)) →' ft.bot),
      from by simp[formula.notdef],
  apply contra_not_imp_false_ax,
  rw ← hnnn,
  apply mp,
  apply dni,
  simp[formula.notdef],
  exact h,
end

lemma and_switch {form : Type} [ft : formula form] {φ ψ : form} : 
-- ⊢ (φ ∧ ψ) ↔' (ψ ∧ φ)
  ax ((φ ∧' ψ) ↔' (ψ ∧' φ)) :=
begin
  rw formula.iffdef at *,
  exact (mp _ _ (mp _ _ (p4 _ _) (mp _ _ double_imp (cut (p5 _ _) 
    (imp_switch (cut (p6 _ _) (p4 _ _)))))) 
    (mp _ _ double_imp (cut (p5 _ _) (imp_switch (cut (p6 _ _) (p4 _ _))))))
end

lemma and_switch' {form : Type} [ft : formula form] {φ ψ : form} : 
  ax (((ψ ∧' φ) →' (φ ∧' ψ)) ∧' ((φ ∧' ψ) →' (ψ ∧' φ))) :=
begin
  have h : _, from @and_switch form ft φ ψ,
  exact (mp _ _ (mp _ _ (p4 _ _) (mp _ _ double_imp (cut (p5 _ _) 
    (imp_switch (cut (p6 _ _) (p4 _ _)))))) 
    (mp _ _ double_imp (cut (p5 _ _) (imp_switch (cut (p6 _ _) (p4 _ _))))))
end

lemma true_and_phi {form : Type} [ft : formula form] {φ : form} : 
-- ⊢  (⊤ ∧ φ) ↔' φ 
  ax (((¬' ft.bot) ∧' φ) ↔' φ) :=
begin
  rw formula.iffdef at *,
  exact mp _ _(mp _ _ (p4 _ _) (cut (iff_l and_switch) (iff_l phi_and_true))) 
    (mp _ _ (p4 _ _) not_bot),
end

lemma contra_imp_imp_false' {form : Type} [ft : formula form] {φ : form} : 
-- ⊢ φ → ¬ φ → ⊥
  ax ((φ) →' (¬' φ →' ft.bot)) :=
begin
  rw ←and_right_imp,
  apply cut,
  apply mp,
  apply p5,
  exact (φ ∧' ¬' φ) →' (¬' φ ∧' φ),
  exact and_switch',
  exact contra_imp_false,
end

lemma and_switch_ax {form : Type} [ft : formula form] {φ ψ : form} : 
-- ⊢ (φ ∧ ψ) ⇔ ⊢ (ψ ∧ φ)
  (ax (φ ∧' ψ)) ↔ (ax (ψ ∧' φ)) :=
begin
  split,
  repeat { exact λ h, mp _ _ (mp _ _ (p5 _ _) and_switch') h, },
end

lemma and_commute {form : Type} [ft : formula form] {φ ψ χ : form} : 
-- ⊢ ((φ ∧ ψ) ∧ χ) ↔' (φ ∧ (ψ ∧ χ))
  ax (((φ ∧' ψ) ∧' χ) ↔' (φ ∧' (ψ ∧' χ))) :=
begin
  rw formula.iffdef at *,
  exact mp _ _ (mp _ _ (p4 _ _) (mp _ _ double_imp (imp_imp_iff_imp.mp 
  (cut (cut (p5 _ _) (p6 _ _)) (cut2 (p6 _ _) (cut1 (p4 _ _) 
    (imp_switch (cut (cut (p5 _ _) (p5 _ _)) (p4 _ _))))))))) 
  (mp _ _ double_imp (imp_imp_iff_imp.mp (cut (cut (p6 _ _) (p5 _ _)) 
  (imp_switch (cut (p5 _ _) (cut1 (p4 _ _) (cut2 (cut (p6 _ _) (p6 _ _)) (p4 _ _))))))))
end

lemma and_commute' {form : Type} [ft : formula form] {φ ψ χ : form} : 
  ax ((((φ ∧' ψ) ∧' χ) →' (φ ∧' (ψ ∧' χ))) ∧' ((φ ∧' (ψ ∧' χ)) →' ((φ ∧' ψ) ∧' χ))) :=
begin
  exact mp _ _ (mp _ _ (p4 _ _) (mp _ _ double_imp (imp_imp_iff_imp.mp 
  (cut (cut (p5 _ _) (p6 _ _)) (cut2 (p6 _ _) (cut1 (p4 _ _) 
    (imp_switch (cut (cut (p5 _ _) (p5 _ _)) (p4 _ _))))))))) 
  (mp _ _ double_imp (imp_imp_iff_imp.mp (cut (cut (p6 _ _) (p5 _ _)) 
  (imp_switch (cut (p5 _ _) (cut1 (p4 _ _) (cut2 (cut (p6 _ _) (p6 _ _)) (p4 _ _))))))))
end

lemma contra_iff_false_ax_not {form : Type} [ft : formula form] {φ : form} : 
-- ⊢ ¬ φ ↔ ⊢ φ → ⊥
  ax (¬' φ) ↔ ax (φ →' ft.bot) :=
 begin
  simp[formula.notdef],
end

lemma imp_and_imp {form : Type} [ft : formula form] {φ ψ χ : form} : 
-- ⊢ φ → ψ ⇒ ⊢ (χ ∧ φ) → (χ ∧ ψ)
  ax (φ →' ψ) → ax ((χ ∧' φ) →' (χ ∧' ψ)) :=
begin
  intros h1,
  exact imp_and_and_imp (mp _ _ (mp _ _ (p4 _ _) iden) h1)
end

lemma demorgans {form : Type} [ft : formula form] {φ ψ : form} : 
-- ⊢ ¬ (φ ∧ ψ) ⇔ ⊢ φ → ¬ ψ
  ax (¬' (φ ∧' ψ)) ↔ ax (φ →' (¬' ψ)) :=
begin
  split,
  { intro h1,
    simp[formula.notdef] at *,
    apply and_right_imp.mp,
    apply cut,
    { exact mp _ _ (p5 _ _) and_switch', },
    { exact h1, }, },
  { intro h1,
    apply (mp _ _ (contrapos.mpr (mp _ _ (p5 _ _) and_switch'))),
    simp[formula.notdef] at *,
    exact(and_right_imp.mpr h1), },
end

lemma explosion {form : Type} [ft : formula form] {φ : form} : 
-- ⊢ ⊥ → φ 
  ax (ft.bot →' φ) :=
begin
  apply contrapos.mp, exact (mp _ _ (p1 _ _) not_bot)
end

lemma and_iden {form : Type} [ft : formula form] {φ : form} : 
-- ⊢ φ → (φ ∧ φ) 
  ax (φ →' (φ ∧' φ)) :=
begin
  have hdi : ax ((φ →' (φ →' (φ ∧' φ))) →' (φ →' (φ ∧' φ))), from double_imp,
  apply mp _ _ hdi,
  exact (p4 _ _),
end

lemma imp_and_iden {form : Type} [ft : formula form] {φ ψ : form} : 
-- ⊢ φ → ψ ⇒ ⊢ φ → (φ ∧ ψ)
  ax (φ →' ψ) → ax (φ →' (φ ∧' ψ)) :=
begin
  intro h,
  have hab : ax (φ →' (φ ∧' φ)), from and_iden,
  have hbc : ax ((φ ∧' φ) →' (φ ∧' ψ)), from imp_and_imp h,
  exact cut hab hbc,
end

lemma and_ax {form : Type} [ft : formula form] {φ ψ : form} : 
-- ⊢ φ ⇒ ⊢ ψ ⇒ ⊢ φ ∧ ψ
  ax φ → ax ψ → ax (φ ∧' ψ) :=
begin
  intros hφ hψ,
  apply mp,
  apply mp,
  apply p4,
  exact hφ,
  exact hψ,
end

lemma imp_imp_and {form : Type} [ft : formula form] {φ ψ χ : form} : 
-- ⊢ (φ → ψ) ⇒ ⊢ (φ → χ) ⇒ ⊢ φ → (ψ ∧ χ)
  ax (φ →' ψ) → ax (φ →' χ) → ax (φ →' (ψ ∧' χ)) :=
begin
  intros h1 h2,
  apply cut,
  { exact and_iden, },
  { exact imp_and_and_imp (and_ax h1 h2)},
end

lemma imp_and_r {form : Type} [ft : formula form] {φ ψ χ : form} : 
-- ⊢ (φ → ψ) ⇒ ⊢ (χ ∧ φ) → ψ
  ax (φ →' ψ) → ax ((χ ∧' φ) →' ψ) :=
begin
  intro h,
  apply cut,
  exact p6 _ _,
  exact h,
end

lemma imp_and_l {form : Type} [ft : formula form] {φ ψ χ : form} : 
-- ⊢ (φ → ψ) ⇒ ⊢ (φ ∧ χ) → ψ
  ax (φ →' ψ) → ax ((φ ∧' χ) →' ψ) :=
begin
  intro h,
  apply cut,
  exact p5 _ _,
  exact h,
end

lemma ax_bot_imp {form : Type} [ft : formula form] {φ : form} : 
-- ⊢ (⊤ → ⊥) ⇒ ⊢ (φ → ⊥) 
  ax (ft.top →' ft.bot) → ax (φ →' ft.bot) :=
begin
  intro hf,
  apply mp,
  apply mp,
  apply p2,
  exact ft.top,
  apply mp,
  exact p1 _ _,
  exact hf,
  apply mp,
  exact p1 _ _,
  exact prtrue,
end

lemma iff_and_top {form : Type} [ft : formula form] {φ ψ : form} : 
-- ⊢ (φ ∧ ⊤) → ψ ⇔ ⊢ (φ → ψ) 
  ax ((φ ∧' ft.top) →' ψ) ↔ ax (φ →' ψ) :=
begin
  split,
  { intro h,
    apply cut,
    { exact mp _ _ (p6 _ _ ) phi_and_true', },
    { rw topnotbot at h, 
      exact h,} },
  { intro h,
    apply cut,
    apply p5,
    exact h, }
end

lemma remove_and_imp {form : Type} [ft : formula form] {φ ψ χ : form} : 
-- ⊢ (φ ∧ φ ∧ ψ) → χ ⇒ ⊢ (φ ∧ ψ) → χ
  ax ((φ ∧' (φ ∧' (ψ))) →' χ) → ax ((φ ∧' (ψ)) →' χ) :=
begin
  intro h,
  apply cut,
  { exact imp_imp_and (p5 _ _) (iden), },
  { exact h, },
end

lemma by_contra_ax {form : Type} [ft : formula form] {φ ψ : form} : 
-- ⊢ φ → ψ → ⊥ ⇒ ⊢ φ → ¬ ψ
 ax (φ →' (ψ →' ft.bot)) → ax (φ →' (¬' ψ)) :=
by simp[formula.notdef]

lemma imp_and {form : Type} [ft : formula form] {φ ψ χ : form} :
  ax ((φ →' (ψ ∧' χ)) →' (φ →' ψ)) :=
begin
  apply mp,
  apply p2,
  apply mp,
  apply p1,
  apply p5,
end

def combS {form : Type} [ft : formula form] {φ ψ χ : form} (x : ax (φ →' ψ →' χ)) (y : ax (φ →' ψ))
  : ax (φ →' χ) :=
mp _ _ (mp _ _ (p2 _ _ _) x) y

def combS2 {form : Type} [ft : formula form] {φ ψ χ ω : form} (x : ax (φ →' ψ →' χ →' ω)) (y : ax (φ →' ψ)) (z : ax (φ →' χ))
  : ax (φ →' ω) :=
combS (combS x y) z

def propS {φ ψ χ : Type} (x : φ → ψ → χ) (y : φ → ψ) : (φ → χ) := λ z, (x z) (y z)
def propS2 {φ ψ χ ω : Type} (x : φ → ψ → χ → ω) (y : φ → ψ) (z : φ → χ) : (φ → ω) := λ w, (x w) (y w) (z w)

def combK {form : Type} [ft : formula form] {φ ψ : form} (x : ax φ) : ax (ψ →' φ) :=
mp _ _ (p1 _ _) x

def propK {φ ψ : Type} (x : φ) : ψ → φ := λ _, x

def combI {form : Type} [ft : formula form] {φ : form} : ax (φ →' φ) :=
iden

def propI {φ : Type} : φ → φ :=
id

lemma demorgans' {form : Type} [ft : formula form] {φ ψ : form} : 
-- ⊢ (¬ φ → ψ) → ¬ (¬ φ ∧ ¬ ψ)
  ax (((¬' φ) →' ψ) →' ¬' (¬' φ ∧' ¬' ψ)) :=
begin
  simp [formula.notdef],
  exact combS2 (combK (p2 _ _ _)) (combK (combS (combK (p6 _ _)) combI)) 
    (combS2 (combK (p2 _ _ _)) (combS (combK (p1 _ _)) combI) (combK (combS (combK (p5 _ _)) combI))),
end

lemma demorgans'' {form : Type} [ft : formula form] {φ ψ : form} : 
  ax (¬' (φ →' ¬' ψ) →' φ ∧' ψ) :=
begin
  rw ←contrapos,
  apply cut _ dni,
  apply imp_switch,
  simp[ft.notdef],
  rw imp_shift,
  apply cut1,
  apply p4,
  exact likemp,
end

lemma or_cases {form : Type} [ft : formula form] {φ ψ χ : form} : 
-- ⊢ (φ → χ) ⇒  ⊢ (ψ → χ) ⇒ ⊢ (¬ φ → ψ) → χ 
  ax (φ →' χ) → ax (ψ →' χ) → ax ((¬' φ →' ψ) →' χ) :=
begin
  intros h1 h2,
  have h1' := contrapos.mpr h1,
  have h2' := contrapos.mpr h2,
  have h3 := imp_imp_and h1' h2',
  rw ←contrapos,
  apply by_contra_ax,
  apply cut h3,
  apply @cut _ _ _ (¬' (¬' φ →' ψ)) _,
  { 
    refine contrapos.mp _,
    apply cut,
    apply dne,
    exact demorgans',
  },
  exact contra_imp_imp_false,
end

-- Motivation: easier to prove Lean's `and` than in `ax`
@[simp] lemma ax_and {form : Type} [ft : formula form] {φ ψ : form} :
  ax (φ ∧' ψ) ↔ ax φ ∧ ax ψ :=
⟨λ h, ⟨mp _ _ (p5 _ _) h, mp _ _ (p6 _ _) h⟩,
 λ ⟨h1, h2⟩, mp _ _ (mp _ _ (p4 _ _) h1) h2⟩

-- Motivation: corresponds to Lean's `iff.intro`
@[simp] lemma ax_iff_intro {form : Type} [ft : formula form] {φ ψ : form}
  (h1 : ax (φ →' ψ)) (h2 : ax (ψ →' φ)) : ax (φ ↔' ψ) :=
begin
  simp only [ft.iffdef, ax_and],
  exact ⟨h1, h2⟩
end

-- Motivation: corresponds more or less to Lean's `imp_congr`
@[simp] lemma ax_imp_congr_left {form : Type} [ft : formula form] {φ φ' ψ : form}
  (hl : ax (φ ↔' φ')) : ax ((φ →' ψ) ↔' (φ' →' ψ)) :=
ax_iff_intro
  (mp _ _ (imp_switch hs1) (iff_r hl))
  (mp _ _ (imp_switch hs1) (iff_l hl))

/-- `φ` is provable iff `ψ` is, if it's provable `φ` and `ψ` are equivalent.

If we have the deduction theorem, the converse is also true: formulas are provably equivalent iff
their provability is equivalent. -/
-- Motivation: allows rewriting after proving equivalence
lemma ax_iff_mp {form : Type} [ft : formula form] {φ ψ : form} (hiff : ax (φ ↔' ψ)) :
  ax φ ↔ ax ψ :=
⟨mp _ _ (iff_l hiff), mp _ _ (iff_r hiff)⟩

-- Motivation: for simplication in combination with `ax_iff_mp`
@[simp] lemma ax_and_top_iff {form : Type} [ft : formula form] {φ : form} :
  ax ((φ ∧' ⊤') ↔' φ) :=
by simpa [ft.topdef, ft.notdef] using @phi_and_true _ _ φ

-- Motivation: for simplication in combination with `ax_iff_mp`
@[simp] lemma ax_top_imp_iff {form : Type} [ft : formula form] (φ : form) :
  ax ((⊤' →' φ) ↔' φ) :=
ax_iff_intro
  (combS combI (combK prtrue)) -- λ h, h prtrue
  (p1 _ _)

  -- Motivation: for simplication in combination with `ax_iff_mp`
@[simp] lemma ax_not_bot_imp_iff {form : Type} [ft : formula form] (φ : form) :
  ax (((¬' ⊥' ) →' φ) ↔' φ) :=
begin
  have h := ax_top_imp_iff φ,
  rw ft.topdef at h,
  rw ft.notdef,
  exact h,
end

-- Motivation: useful simplification lemma
@[simp] lemma ax_top_imp {form : Type} [ft : formula form] {φ : form} :
  ax (⊤' →' φ) ↔ ax φ :=
ax_iff_mp (ax_top_imp_iff φ)

@[simp] lemma ax_not_bot_imp {form : Type} [ft : formula form] {φ : form} :
  ax ((¬' ⊥' ) →' φ) ↔ ax φ :=
begin
  have h := @ax_top_imp _ _ φ,
  rw ft.topdef at h,
  rw ft.notdef,
  exact h,
end

-- Motivation: corresponds to Lean's `false.elim`
@[simp] lemma ax_bot_elim {form : Type} [ft : formula form] {φ : form} :
  ax (⊥' →' φ) :=
(ax_iff_mp (ax_imp_congr_left contra_equiv_false)).mp (p5 _ _)

-- finite disjunction of formulas
def finite_disjunction {form : Type} [ft : formula form] : (list form) → form
  | list.nil   := ft.bot
  | (f :: fs)  := f ∨' (finite_disjunction fs)

def disjunct_rw_iff {form : Type} [ft : formula form] (φ ψ : form) : 
  ax ((¬' φ) →' ψ) ↔ ax (finite_disjunction (φ :: ψ :: list.nil)) :=
begin
  split,
  { simp [finite_disjunction],
    intro h,
    apply mp,
    apply mp,
    apply hs1,
    exact ψ,
    apply contra_imp_imp_false',
    exact h,
  },
  { simp [finite_disjunction],
    intro h,
    apply @cut _ _ _ (¬' (¬' ψ)),
    rw ft.notdef at *,
    exact h,
    exact dne, },
end

lemma imp_finite_disjunction {form : Type} [ft : formula form] 
  (φ : form) (fs : list (form)) (h : φ ∈ fs) :
  ax (φ →' finite_disjunction fs) :=
begin
  induction fs with f fs ih,
  { by_contradiction, simp at *, exact h, },
  { simp [finite_disjunction] at *,
    cases em (f = φ) with hf hf,
    { rw hf at *,
      rw ←and_right_imp,
      apply cut,
      { exact mp _ _ (p5 _ _) and_switch', },
      { apply cut,
        { exact contra_imp_false, },
        { exact explosion, }, }, },
    { cases h,
    { exact false.rec _ (hf (eq.symm h)), },
    { exact imp_if_imp_imp (ih h), }, }, },
end

lemma imp_finite_disjunction_subset {form : Type} [ft : formula form] 
  (fs fs': list (form)) (hsubset : fs ⊆ fs') :
  ax (finite_disjunction fs →' finite_disjunction fs') :=
begin
  induction fs with f fs ih,
  { simp[finite_disjunction], },
  { simp [finite_disjunction] at *,
    cases hsubset with hf hsubset,
    specialize ih hsubset,
    have hfs' := imp_finite_disjunction f fs' hf,
    apply or_cases,
    exact hfs',
    exact ih,
  },
end

def disjunct_of_disjuncts {form : Type} [ft : formula form] (fs fs': list (form)) : 
  ax ((finite_disjunction ((finite_disjunction fs) :: (finite_disjunction fs') :: list.nil)) ↔' 
      (finite_disjunction (fs ++ fs'))) :=
begin
  rw ft.iffdef,
  apply and_ax,
  { rw finite_disjunction,
    apply or_cases,
    { apply imp_finite_disjunction_subset,
      simp, },
    { simp [finite_disjunction],
      have hdne := @dne _ _ (finite_disjunction fs'),
      simp [ft.notdef] at *,
      apply cut,
      apply hdne,
      apply imp_finite_disjunction_subset,
      simp, }, },
  { induction' fs,
    { simp [finite_disjunction] at *,
      apply cut1,
      apply p1,
      have hdni := @dni form ft (@finite_disjunction form ft fs'),
      rw ft.notdef at *,
      exact hdni, },
    { specialize @ih ft,
      apply or_cases,
      { rw finite_disjunction,
        simp,
        apply cut,
        apply @imp_finite_disjunction form ft _ (hd :: fs),
        exact set.mem_insert hd (λ (hd : form), list.mem hd fs),
        apply cut1,
        apply contra_imp_imp_false',
        apply explosion, },
      { apply cut,
        apply ih,
        apply or_cases,
        { apply @cut1 _ _ _ (⊥'),
          apply cut,
          apply @imp_finite_disjunction_subset form ft _ (hd :: fs),
          simp,
          apply contra_imp_imp_false',
          apply explosion, },
        { unfold finite_disjunction,
          apply p1, }, }, }, },
end

lemma disjunc_disjunct {form : Type} [ft : formula form] 
  (fs fs' : list (form)) :
  ax ((¬' (finite_disjunction fs) →' finite_disjunction fs') →' finite_disjunction (fs ++ fs'))  :=
begin
  apply or_cases,
  apply imp_finite_disjunction_subset,
  simp,
  apply imp_finite_disjunction_subset,
  simp,
end


lemma ax_iff_disjunc_disjunct {form : Type} [ft : formula form] (fs fs' : list (form)) :
  ax (¬' (finite_disjunction fs) →' finite_disjunction fs') ↔ ax (finite_disjunction (fs ++ fs'))  :=
begin
  split,
  { intro h,
    apply MP' h,
    apply disjunc_disjunct, },
  { intro h,
    rw disjunct_rw_iff,
    apply MP' h,
    apply iff_r,
    apply disjunct_of_disjuncts, },
end

