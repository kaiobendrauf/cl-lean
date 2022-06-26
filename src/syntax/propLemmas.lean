/-
Copyright (c) 2021 Paula Neeley. All rights reserved.
Author: Paula Neeley
-/

import syntax.axiomsCL data.set.basic
local attribute [instance] classical.prop_decidable

-- open ft.ax

variables {agents : Type}


---------------------- Helper Lemmas ----------------------

lemma MP' {form: Type} {ft: formula form} {φ ψ : form} (hL: ft.ax φ) (hImp: ft.ax (ft.imp φ ψ)) : 
ft.ax (ψ) :=
begin
 apply ft.mp,
 exact hImp,
 exact hL,
end

lemma iden {form: Type} {ft: formula form} {φ : form} :
--  ⊢ φ → φ 
 ft.ax (ft.imp φ φ) := 
begin
apply ft.mp,
apply ft.mp,
exact ft.p2 φ (ft.imp φ φ) φ,
apply ft.p1,
apply ft.p1,
end

lemma prtrue {form: Type} {ft: formula form}: 
--  ⊢ ⊤
ft.ax (ft.top) := 
begin
  rw ft.topdef,
  exact iden,
end


lemma not_bot {form: Type} {ft: formula form}: 
--  ⊢ ⊤
ft.ax (ft.not ft.bot) := 
begin
  rw ft.notdef,
  exact iden,
end

lemma topnotbot {form: Type} {ft: formula form}: 
--  ⊢ ⊤ = ¬ ⊥
ft.top = ft.not ft.bot :=
begin
  simp[ft.notdef, ft.topdef],
end

-- lemma weak {Γ : ctx} {φ ψ : form} :
--  prfK Γ φ → prfK (Γ ∪ ψ) φ :=

-- lemma weak {Γ : ctx} {φ ψ : form} :
--  ft.ax φ → ft.ax (Γ ∪ ψ) φ :=
-- begin
-- intro h,
-- induction h,
-- {apply ax, exact (set.mem_insert_of_mem _ h_h)},
-- {exact ft.p1},
-- {exact ft.p2},
-- {exact ft.p3},
-- {exact ft.p4},
-- {exact ft.p5},
-- {exact ft.p6},
-- {exact ft.p7 _ _},
-- {exact kdist},
-- {apply ft.mp,
--  {exact h_ih_hpq},
--  {exact h_ih_hp}},
-- {exact nec h_ih }
-- end


-- lemma pr {φ : form} :
--  ft.ax (∪ φ) φ :=
-- begin
-- apply ax;
-- apply or.intro_left;
-- simp
-- end


lemma cut {form: Type} {ft: formula form} {φ ψ χ : form} :
--  ⊢ (φ → ψ) ⇒  ⊢ (ψ → χ) ⇒  ⊢ (φ → χ)
 ft.ax (ft.imp φ ψ) → ft.ax (ft.imp ψ χ) → ft.ax (ft.imp φ χ) :=
begin
intros h1 h2,
apply ft.mp,
apply ft.mp,
exact ft.p2 _ ψ _,
apply ft.mp,
exact ft.p1 _ _,
exact h2,
exact h1,
end 


-- lemma conv_deduction {φ ψ : form} :
--  ft.ax (φ ~> ψ) → ft.ax (∪ φ) ψ :=
-- begin
-- intro h, 
-- exact ft.mp (weak h) pr 
-- end


lemma hs1 {form: Type} {ft: formula form} {φ ψ χ : form} :
-- ⊢ (ψ → χ) → ((φ → ψ) → (φ → χ))
 ft.ax (ft.imp (ft.imp ψ χ) (ft.imp (ft.imp φ ψ) (ft.imp φ χ))) :=
begin
exact (ft.mp _ _ (ft.mp _ _ (ft.p2 _ _ _) (ft.mp _ _ (ft.p1 _ _) (ft.p2 _ _ _))) (ft.p1 _ _))
end


lemma likemp {form: Type} {ft: formula form} {φ ψ : form} : 
-- ⊢ φ → ((φ → ψ) → ψ)
 ft.ax (ft.imp φ (ft.imp (ft.imp φ ψ) ψ)) :=
begin
exact (ft.mp _ _ (ft.mp _ _ hs1 (ft.mp _ _ (ft.p2 _ _ _) iden)) (ft.p1 _ _))
end


lemma dne {form: Type} {ft: formula form} {φ : form} :
-- ⊢ ¬ ¬ φ → φ
ft.ax (ft.imp (ft.not (ft.not φ)) φ) :=
begin
have h1 : ft.ax (ft.imp φ (ft.imp φ φ)), from ft.p1 _ _,
exact (cut (cut (ft.p1 _ _) (cut (ft.p7 _ _) (ft.p7 _ _))) (ft.mp _ _ likemp h1)),
end


lemma dni {form: Type} {ft: formula form} {φ : form} : 
-- ⊢ φ → ¬ ¬ φ
ft.ax (ft.imp φ (ft.not (ft.not φ))) :=
begin
exact ft.mp _ _ (ft.p7 _ _) dne
end


lemma imp_if_imp_imp {form: Type} {ft: formula form} {φ ψ χ : form} : 
-- ⊢ (φ → χ) ⇒  ⊢ φ → (ψ → χ)
ft.ax (ft.imp φ χ) → ft.ax (ft.imp φ (ft.imp ψ χ)) :=
begin
intro h1,
exact ft.mp _ _ (ft.mp _ _ (ft.p2 _ _ _) (ft.mp _ _ (ft.p1 _ _) (ft.p1 _ _))) h1,
end


lemma cut1 {form: Type} {ft: formula form} {φ ψ χ θ : form} :
-- ⊢ θ → (φ → ψ) ⇒  ⊢ (ψ → χ) ⇒ ⊢ θ → (φ → χ)
 ft.ax (ft.imp θ (ft.imp φ ψ)) → ft.ax (ft.imp ψ χ) → ft.ax (ft.imp θ (ft.imp φ χ)) :=
begin
intros h1 h2,
exact cut h1 (ft.mp _ _ (ft.p2 _ _ _) (ft.mp _ _ (ft.p1 _ _ )h2))
end


lemma imp_switch {form: Type} {ft: formula form} {φ ψ χ : form} : 
-- ⊢ φ → (ψ → χ) ⇒  ⊢ ψ → (φ → χ)
ft.ax (ft.imp φ (ft.imp ψ χ)) → ft.ax (ft.imp ψ (ft.imp φ χ)) :=
begin
intro h1,
exact ft.mp _ _ (ft.mp _ _ (ft.p2 _ _ _ ) (ft.mp _ _ (ft.p1 _ _) (ft.mp _ _ (ft.p2 _ _ _) h1))) (ft.p1 _ _)
end


lemma l2 {form: Type} {ft: formula form} {φ ψ χ : form} : 
-- ⊢ (φ → (ψ → χ)) → (ψ → (φ → χ))
ft.ax (ft.imp (ft.imp φ (ft.imp ψ χ)) (ft.imp ψ (ft.imp φ χ))) :=
begin
exact (ft.mp _ _ (ft.mp _ _ (ft.p2 _ _ _) (cut (ft.p2 _ _ _) hs1)) (ft.mp _ _ (ft.p1 _ _) (ft.p1 _ _)))
end


lemma hs2 {form: Type} {ft: formula form} {φ ψ χ : form} :
-- ⊢ (φ → ψ) → ((ψ → χ) → (φ → χ))
 ft.ax (ft.imp (ft.imp φ ψ) (ft.imp (ft.imp ψ χ) (ft.imp φ χ))) :=
begin
exact (ft.mp _ _ l2 hs1)
end


lemma cut2 {form: Type} {ft: formula form} {φ ψ χ θ : form} :
-- ⊢ (φ → ψ) ⇒  ⊢ θ → (ψ → χ) ⇒ ⊢ θ → (φ → χ)
 ft.ax (ft.imp φ ψ) → ft.ax (ft.imp θ (ft.imp ψ χ)) → ft.ax (ft.imp θ (ft.imp φ χ)) :=
begin
intros h1 h2,
exact imp_switch (cut h1 (imp_switch h2))
end


lemma double_imp {form: Type} {ft: formula form} {φ ψ : form} :
-- ⊢ (φ → (φ → ψ)) → ((φ → ψ)
 ft.ax (ft.imp (ft.imp φ (ft.imp φ ψ)) (ft.imp φ ψ)) :=
begin
exact ft.mp _ _ (ft.p2 _ _ _) (imp_switch iden)
end


lemma imp_imp_iff_imp {form: Type} {ft: formula form} {θ φ ψ : form} : 
-- ⊢ θ → (φ → (φ → ψ)) ⇔ ⊢ θ → (φ → ψ)
 ft.ax (ft.imp θ (ft.imp φ (ft.imp φ ψ))) ↔ ft.ax (ft.imp θ (ft.imp φ ψ)) :=
begin
split,
{intro h1,
exact cut h1 double_imp},
{intro h1,
exact cut h1 (ft.p1 _ _)}
end


lemma imp_shift {form: Type} {ft: formula form} {θ φ ψ χ : form} : 
-- ⊢ θ → (φ → (ψ → χ)) ⇔ ⊢ θ → (ψ → (φ → χ)
 ft.ax (ft.imp θ (ft.imp φ (ft.imp ψ χ))) ↔ ft.ax (ft.imp θ (ft.imp ψ (ft.imp φ χ))) :=
begin
split,
repeat {intro h1, exact cut h1 (cut2 (ft.p1 _ _) (ft.p2 _ _ _))}
end


lemma left_and_imp {form: Type} {ft: formula form} {φ ψ χ : form} :
-- ⊢ ψ → ((φ ∧ ψ) → χ ) ⇒ ⊢ (φ ∧ ψ) → χ
 ft.ax (ft.imp ψ (ft.imp (ft.and φ ψ) χ)) → ft.ax (ft.imp (ft.and φ ψ) χ) :=
begin
intro h1,
exact ft.mp _ _ double_imp (cut (ft.p6 _ _) h1)
end


lemma and_right_imp {form: Type} {ft: formula form} {φ ψ χ : form} : 
-- ⊢ (φ ∧ ψ) → χ  ⇔ ⊢  ψ → φ → χ
 ft.ax (ft.imp (ft.and φ ψ) χ) ↔ ft.ax (ft.imp ψ (ft.imp φ χ)) :=
begin
split, 
{intro h1,
exact ft.mp _ _ (cut2 (ft.p1 _ _) (ft.p2 _ _ _)) (cut1 (ft.p4 _ _) h1)},
intro h1,
exact left_and_imp (cut2 (ft.p5 _ _) h1)
end


lemma not_and_subst {form: Type} {ft: formula form} {φ ψ χ : form} : 
-- ⊢ (φ ↔ ψ) ⇒ (⊢ ¬ (χ ∧ φ) ⇔ ⊢ ¬ (χ ∧ ψ))
 ft.ax (ft.iff φ ψ) → (ft.ax (ft.not (ft.and χ φ)) ↔ ft.ax (ft.not (ft.and χ ψ))) :=
begin
intro h1, rw ft.iffdef at *, split, 
{intro h2,
exact ft.mp _ _ (ft.mp _ _ (ft.p3 _ _) (ft.mp _ _ (ft.p1 _ _) h2)) (cut dne (ft.mp _ _ double_imp (cut2 (cut (ft.p6 _ _) (ft.mp _ _ (ft.p6 _ _) h1)) 
 (cut (ft.p5 _ _) (ft.p4 _ _)))))},
{intro h2,
exact ft.mp _ _ (ft.mp _ _ (ft.p3 _ _) (ft.mp _ _ (ft.p1 _ _) h2)) (cut dne (ft.mp _ _ double_imp (cut2 (cut (ft.p6 _ _) (ft.mp _ _ (ft.p5 _ _) h1)) 
 (cut (ft.p5 _ _) (ft.p4 _ _)))))},
end


lemma not_contra {form: Type} {ft: formula form} {φ : form} : 
-- ⊢ ¬ (φ ∧ ¬ φ) 
 ft.ax (ft.not (ft.and φ (ft.not φ))) :=
begin
exact ft.mp _ _ (ft.mp _ _ (ft.p3 _ _) (cut dne (ft.p6 _ _))) (cut dne (ft.p5 _ _))
end


lemma phi_and_true {form: Type} {ft: formula form} {φ : form} : 
-- ⊢  (φ ∧ ⊤) ↔ φ 
ft.ax (ft.iff (ft.and φ (ft.not ft.bot)) φ) :=
begin
rw ft.iffdef at *,
exact (ft.mp _ _ (ft.mp _ _ (ft.p4 _ _) (ft.p5 _ _)) (ft.mp _ _ (imp_switch (ft.p4 _ _)) not_bot))
end

lemma phi_and_true' {form: Type} {ft: formula form} {φ : form} : 
ft.ax (ft.and (ft.imp (ft.and φ (ft.not ft.bot)) φ) (ft.imp φ (ft.and φ (ft.not ft.bot)))) :=
begin
exact (ft.mp _ _ (ft.mp _ _ (ft.p4 _ _) (ft.p5 _ _)) (ft.mp _ _ (imp_switch (ft.p4 _ _)) not_bot))
end


lemma imp_and_and_imp {form: Type} {ft: formula form} {φ ψ χ θ : form} : 
-- ⊢ (φ → ψ) ∧ (χ → θ)⇒ ⊢ (φ ∧ χ) → (ψ ∧ θ)
 ft.ax ((ft.and (ft.imp φ ψ) (ft.imp χ θ))) → ft.ax ((ft.imp (ft.and φ χ) (ft.and ψ θ))) :=
begin
intro h,
exact (ft.mp _ _ double_imp (cut (cut (ft.p5 _ _) (ft.mp _ _ (ft.p5 _ _) h)) (cut2 (cut (ft.p6 _ _) (ft.mp _ _ (ft.p6 _ _) h)) (ft.p4 _ _))))
end


lemma not_contra_equiv_true {form: Type} {ft: formula form} {φ : form} : 
-- ⊢ ¬ (φ ∧ not φ) ↔ ¬ ⊥
 ft.ax (ft.iff (ft.not (ft.and φ (ft.not φ))) (ft.not ft.bot) ) :=
begin
rw ft.iffdef at *,
exact (ft.mp _ _ (ft.mp _ _ (ft.p4 _ _) (ft.mp _ _ (ft.p1 _ _) not_bot)) (ft.mp _ _ (ft.p1 _ _) not_contra))
end

lemma contrapos {form: Type} {ft: formula form} {φ ψ : form} :
-- ⊢ ¬ ψ → ¬ φ ⇔ ⊢ φ → ψ
 ft.ax (ft.imp (ft.not ψ) (ft.not φ)) ↔ ft.ax (ft.imp φ ψ) :=
begin
split,
intro h1,
exact ft.mp _ _ (ft.p7 _ _) h1,
intro h1,
exact ft.mp _ _ (cut (cut (ft.mp _ _ hs1 dni) (ft.mp _ _ hs2 dne)) (ft.p7 _ _)) h1,
end


lemma iff_not {form: Type} {ft: formula form} {φ ψ : form} :
-- ⊢ φ ↔ ψ ⇒ ⊢ ¬ φ ↔ ¬ ψ
 ft.ax (ft.iff φ ψ) → ft.ax (ft.iff (ft.not ψ) (ft.not φ)) :=
begin
intro h1,
rw ft.iffdef at *,
have h2 : ft.ax (ft.imp φ ψ), from ft.mp _ _ (ft.p5 _ _) h1,
have h3 : ft.ax (ft.imp ψ φ), from ft.mp _ _ (ft.p6 _ _) h1,
rw ←contrapos at h2,
rw ←contrapos at h3,
exact (ft.mp _ _ (ft.mp _ _ (ft.p4 _ _) h2) h3)
end


lemma contra_equiv_false {form: Type} {ft: formula form} {φ : form} : 
-- ⊢ (φ ∧ not φ) ↔ ⊥
 ft.ax (ft.iff(ft.and φ (ft.not φ)) ft.bot) :=
begin
have h1 := iff_not not_contra_equiv_true,
rw ft.iffdef at *,
exact (ft.mp _ _ (ft.mp _ _ (ft.p4 _ _) (cut dni (cut (ft.mp _ _ (ft.p6 _ _) h1) dne))) (cut dni (cut (ft.mp _ _ (ft.p5 _ _) h1) dne)))
end

lemma contra_equiv_false' {form: Type} {ft: formula form} {φ : form} : 
 ft.ax (ft.and (ft.imp(ft.and φ (ft.not φ)) ft.bot) (ft.imp ft.bot (ft.and φ (ft.not φ)))) :=
begin
have h1 := @contra_equiv_false form ft φ,
rw ft.iffdef at *,
exact h1,
end

lemma contra_imp_false {form: Type} {ft: formula form} {φ : form} : 
-- ⊢ (φ ∧ not φ) → ⊥
 ft.ax (ft.imp(ft.and φ (ft.not φ)) ft.bot) :=
begin
exact ft.mp _ _ (ft.p5 _ _) contra_equiv_false',
end


lemma and_switch {form: Type} {ft: formula form} {φ ψ : form} : 
-- ⊢ (φ ∧ ψ) ↔ (ψ ∧ φ)
ft.ax (ft.iff (ft.and φ ψ) (ft.and ψ φ)) :=
begin
rw ft.iffdef at *,
exact (ft.mp _ _ (ft.mp _ _ (ft.p4 _ _) (ft.mp _ _ double_imp (cut (ft.p5 _ _) (imp_switch (cut (ft.p6 _ _) (ft.p4 _ _)))))) 
(ft.mp _ _ double_imp (cut (ft.p5 _ _) (imp_switch (cut (ft.p6 _ _) (ft.p4 _ _))))))
end

lemma and_switch' {form: Type} {ft: formula form} {φ ψ : form} : 
ft.ax (ft.and (ft.imp (ft.and ψ φ) (ft.and φ ψ))(ft.imp (ft.and φ ψ) (ft.and ψ φ))) :=
begin
have h: _, from @and_switch form ft φ ψ,
exact (ft.mp _ _ (ft.mp _ _ (ft.p4 _ _) (ft.mp _ _ double_imp (cut (ft.p5 _ _) (imp_switch (cut (ft.p6 _ _) (ft.p4 _ _)))))) 
(ft.mp _ _ double_imp (cut (ft.p5 _ _) (imp_switch (cut (ft.p6 _ _) (ft.p4 _ _))))))
end


lemma and_commute {form: Type} {ft: formula form} {φ ψ χ : form} : 
-- ⊢ ((φ ∧ ψ) ∧ χ) ↔ (φ ∧ (ψ ∧ χ))
ft.ax (ft.iff (ft.and (ft.and φ ψ) χ) (ft.and φ (ft.and ψ χ))) :=
begin
rw ft.iffdef at *,
exact ft.mp _ _ (ft.mp _ _ (ft.p4 _ _) (ft.mp _ _ double_imp (imp_imp_iff_imp.mp 
 (cut (cut (ft.p5 _ _) (ft.p6 _ _)) (cut2 (ft.p6 _ _) (cut1 (ft.p4 _ _) (imp_switch (cut (cut (ft.p5 _ _) (ft.p5 _ _)) (ft.p4 _ _))))))))) 
 (ft.mp _ _ double_imp (imp_imp_iff_imp.mp (cut (cut (ft.p6 _ _) (ft.p5 _ _)) 
 (imp_switch (cut (ft.p5 _ _) (cut1 (ft.p4 _ _) (cut2 (cut (ft.p6 _ _) (ft.p6 _ _)) (ft.p4 _ _))))))))
end

lemma and_commute' {form: Type} {ft: formula form} {φ ψ χ : form} : 
ft.ax (ft.and (ft.imp (ft.and (ft.and φ ψ) χ) (ft.and φ (ft.and ψ χ))) (ft.imp (ft.and φ (ft.and ψ χ)) (ft.and (ft.and φ ψ) χ))) :=
begin
exact ft.mp _ _ (ft.mp _ _ (ft.p4 _ _) (ft.mp _ _ double_imp (imp_imp_iff_imp.mp 
 (cut (cut (ft.p5 _ _) (ft.p6 _ _)) (cut2 (ft.p6 _ _) (cut1 (ft.p4 _ _) (imp_switch (cut (cut (ft.p5 _ _) (ft.p5 _ _)) (ft.p4 _ _))))))))) 
 (ft.mp _ _ double_imp (imp_imp_iff_imp.mp (cut (cut (ft.p6 _ _) (ft.p5 _ _)) 
 (imp_switch (cut (ft.p5 _ _) (cut1 (ft.p4 _ _) (cut2 (cut (ft.p6 _ _) (ft.p6 _ _)) (ft.p4 _ _))))))))
end

lemma contra_imp_false_ax_not {form: Type} {ft: formula form} {φ : form} : 
-- ⊢ ¬ φ ⇒ ⊢ φ → ⊥
 ft.ax (ft.not φ) → ft.ax (ft.imp φ ft.bot) :=
begin
intro h,
apply cut (ft.mp _ _ (ft.p4 _ _) h),
apply cut (ft.mp _ _ (ft.p5 _ _) and_switch'),
exact contra_imp_false,
end

lemma imp_and_imp {form: Type} {ft: formula form} {φ ψ χ : form} : 
-- ⊢ φ → ψ ⇒ ⊢ (χ ∧ φ) → (χ ∧ ψ)
 ft.ax (ft.imp φ ψ) → ft.ax (ft.imp (ft.and χ φ) (ft.and χ ψ)) :=
begin
intros h1,
exact imp_and_and_imp (ft.mp _ _ (ft.mp _ _ (ft.p4 _ _) iden) h1)
end


lemma demorgans {form: Type} {ft: formula form} {φ ψ : form} : 
-- ⊢ ¬ (φ ∧ ψ) ⇔ ⊢ φ → ¬ ψ
ft.ax (ft.not (ft.and φ ψ)) ↔ ft.ax (ft.imp φ (ft.not ψ)) :=
begin
split,
{
  intro h1,
  simp[ft.notdef] at *,
  apply and_right_imp.mp,
  apply cut,
  { exact ft.mp _ _ (ft.p5 _ _) and_switch', },
  { exact h1, },
},
{
  intro h1,
  apply (ft.mp _ _ (contrapos.mpr (ft.mp _ _ (ft.p5 _ _) and_switch'))),
  simp[ft.notdef] at *,
  exact(and_right_imp.mpr h1),
},
end



lemma explosion {form: Type} {ft: formula form} {φ : form} : 
-- ⊢ ⊥ → φ 
ft.ax (ft.imp ft.bot φ) :=
begin
apply contrapos.mp, exact (ft.mp _ _ (ft.p1 _ _) not_bot)
end


-- lemma exfalso {φ ψ : form} : ft.ax ((φ & ¬φ) ~> ψ) :=
-- begin
-- exact cut not_contra explosion
-- end


-- lemma box_dn {φ : form} : ft.ax ((¬□φ) ↔ ¬(□(¬¬φ))) :=
-- begin
-- exact ft.mp _ _ (ft.mp (ft.p4 _ _) (contrapos.ft.mpr (ft.mp kdist (nec dne)))) (contrapos.ft.mpr (ft.mp kdist (nec dni)))
-- end


-- lemma dual_equiv1 {φ : form} : ft.ax ((□φ) ↔ (¬(◇(¬φ)))) :=
-- begin
-- exact ft.mp (ft.mp (ft.p4 _ _) (cut (contrapos.ft.mp (ft.mp ft.p6 box_dn)) dni)) 
--  (cut dne (contrapos.ft.mp (ft.mp (ft.p5 _ _) box_dn)))
-- end


-- lemma dual_equiv2 {φ : form} : ft.ax ((¬(□¬φ)) ↔ (◇φ)) :=
-- begin
-- exact ft.mp (ft.mp (ft.p4 _ _) iden) iden,
-- end

-- New
-- double_imp
-- ft.ax ((φ ~> (φ ~> ψ)) ~> (φ ~> ψ)) :=


-- lemma imp_imp_iff_imp {form: Type} {ft: formula form} {θ φ ψ : form} : 
--  ft.ax (θ ~> (φ ~> (φ ~> ψ))) ↔ ft.ax (θ ~> (φ ~> ψ)) :=

-- lemma imp_and_imp {φ ψ χ : form} : 
--  ft.ax (φ ~> ψ) → ft.ax ((χ & φ) ~> (χ & ψ)) :=

lemma and_iden {form: Type} {ft: formula form} {φ: form}:
-- ⊢ φ → (φ ∧ φ) 
 ft.ax (ft.imp φ (ft.and φ φ)) :=
begin
 have hdi: ft.ax (ft.imp (ft.imp φ (ft.imp φ (ft.and φ φ))) (ft.imp φ (ft.and φ φ))), from double_imp,
 apply ft.mp _ _ hdi,
 exact (ft.p4 _ _),
end

lemma imp_and_iden {form: Type} {ft: formula form} {φ ψ : form}:
-- ⊢ φ → ψ ⇒ ⊢ φ → (φ ∧ ψ)
 ft.ax (ft.imp φ ψ) → ft.ax (ft.imp φ (ft.and φ ψ)) :=
begin
 intro h,
 have hab: ft.ax (ft.imp φ (ft.and φ φ)), from and_iden,
 have hbc: ft.ax (ft.imp (ft.and φ φ) (ft.and φ ψ)), from imp_and_imp h,
 exact cut hab hbc,
end

lemma and_ax {form: Type} {ft: formula form} {φ ψ: form}:
-- ⊢ φ ⇒ ⊢ ψ ⇒ ⊢ φ ∧ ψ
  ft.ax φ → ft.ax ψ → ft.ax (ft.and φ ψ) :=
begin
  intros hφ hψ,
  apply ft.mp,
  apply ft.mp,
  apply ft.p4,
  exact hφ,
  exact hψ,
end


lemma imp_imp_and {form: Type} {ft: formula form} {φ ψ χ: form}:
-- ⊢ (φ → ψ) ⇒ ⊢ (φ → χ) ⇒ ⊢ (φ  → (ψ ∧ χ)
  ft.ax (ft.imp φ ψ) → ft.ax (ft.imp φ χ) → ft.ax (ft.imp φ (ft.and ψ χ)) :=
begin
intros h1 h2,
apply cut,
{ exact and_iden, },
{ exact imp_and_and_imp (and_ax h1 h2)},
end

lemma imp_and_r {form: Type} {ft: formula form} {φ ψ χ: form}:
-- ⊢ (φ → ψ) ⇒ ⊢ (χ ∧ φ) → ψ
  ft.ax (ft.imp φ ψ) → ft.ax (ft.imp (ft.and χ φ) ψ) :=
begin
  intro h,
  apply cut,
  exact ft.p6 _ _,
  exact h,
end

lemma imp_and_l {form: Type} {ft: formula form} {φ ψ χ: form}:
-- ⊢ (φ → ψ) ⇒ ⊢ (φ ∧ χ) → ψ
  ft.ax (ft.imp φ ψ) → ft.ax (ft.imp (ft.and φ χ) ψ) :=
begin
  intro h,
  apply cut,
  exact ft.p5 _ _,
  exact h,
end

lemma ax_bot_imp {form: Type} {ft: formula form} {φ: form}: 
-- ⊢ (⊤ → ⊥) ⇒ ⊢ (φ → ⊥) 
ft.ax (ft.imp ft.top ft.bot) → ft.ax (ft.imp φ ft.bot):=
begin
  intro hf,
  apply ft.mp,
  apply ft.mp,
  apply ft.p2,
  exact ft.top,
  apply ft.mp,
  exact ft.p1 _ _,
  exact hf,
  apply ft.mp,
  exact ft.p1 _ _,
  exact prtrue,
end

lemma iff_and_top {form: Type} {ft: formula form} {φ ψ: form}: 
-- ⊢ (φ ∧ ⊤) → ψ ⇔ ⊢ (φ → ψ) 
ft.ax (ft.imp (ft.and φ ft.top) ψ) ↔ ft.ax (ft.imp φ ψ):=
begin
split,
{
  intro h,
  apply cut,
  { exact ft.mp _ _ (ft.p6 _ _ ) phi_and_true', },
  { rw topnotbot at h, exact h,},
},
{
  intro h,
  apply cut,
  apply ft.p5,
  exact h,
}
end

lemma remove_and_imp {form: Type} {ft: formula form} {φ ψ χ: form}:
-- ⊢ (φ ∧ φ ∧ ψ) → χ ⇒ ⊢ (φ ∧ ψ) → χ
ft.ax (ft.imp (ft.and φ (ft.and φ (ψ))) χ) → ft.ax (ft.imp (ft.and φ (ψ)) χ) :=
begin
intro h,
apply cut,
{ exact imp_imp_and (ft.p5 _ _) (iden), },
{ exact h, },
end
