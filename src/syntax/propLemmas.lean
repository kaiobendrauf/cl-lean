/-
Copyright (c) 2021 Paula Neeley. All rights reserved.
Author: Paula Neeley
-/

import syntax.axiomsCL data.set.basic
local attribute [instance] classical.prop_decidable

open axCL

variables {agents : Type}


---------------------- Helper Lemmas ----------------------

lemma MP' {φ ψ : formCL agents} (hL: axCL φ) (hImp: axCL (φ ~> ψ)) : axCL (ψ) :=
begin
  apply MP,
  exact hImp,
  exact hL,
end

lemma iden {φ : formCL agents} :
  axCL (φ ~> φ) := 
begin
exact MP (MP (@Prop2 agents φ (φ ~> φ) φ) Prop1) Prop1
end


-- lemma prtrue : axCL ⊤ := iden

-- lemma weak {Γ : ctx} {φ ψ : form} :
--   prfK Γ φ → prfK (Γ ∪ ψ) φ :=

-- lemma weak {Γ : ctx} {φ ψ : formCL agents} :
--   axCL φ → axCL (Γ ∪ ψ) φ :=
-- begin
-- intro h,
-- induction h,
-- {apply ax, exact (set.mem_insert_of_mem _ h_h)},
-- {exact Prop1},
-- {exact Prop2},
-- {exact Prop3},
-- {exact Prop4},
-- {exact Prop5},
-- {exact Prop6},
-- {exact Prop7},
-- {exact kdist},
-- {apply MP,
--   {exact h_ih_hpq},
--   {exact h_ih_hp}},
-- {exact nec h_ih }
-- end


-- lemma pr {φ : formCL agents} :
--   axCL (∪ φ) φ :=
-- begin
-- apply ax;
-- apply or.intro_left;
-- simp
-- end


lemma cut {φ ψ χ : formCL agents} :
  axCL (φ ~> ψ) → axCL (ψ ~> χ) → axCL (φ ~> χ) :=
begin
intros h1 h2,
exact MP (MP Prop2 (MP Prop1 h2)) h1
end 


-- lemma conv_deduction {φ ψ : formCL agents} :
--   axCL (φ ~> ψ) → axCL (∪ φ) ψ :=
-- begin
-- intro h, 
-- exact MP (weak h) pr 
-- end


lemma hs1 {φ ψ χ : formCL agents} :
  axCL ((ψ ~> χ) ~> ((φ ~> ψ) ~> (φ ~> χ))) :=
begin
exact (MP (MP Prop2 (MP Prop1 Prop2)) Prop1)
end


lemma likeMP {φ ψ : formCL agents} : 
  axCL (φ ~> ((φ ~> ψ) ~> ψ)) :=
begin
exact (MP (MP hs1 (MP Prop2 iden)) Prop1)
end


lemma dne {φ : formCL agents} :
axCL ((¬¬φ) ~> φ) :=
begin
have h1 : axCL (φ ~> (φ ~> φ)), from Prop1,
exact (cut (cut Prop1 (cut Prop7 Prop7)) (MP likeMP h1))
end


lemma dni {φ : formCL agents} : axCL (φ ~> ¬¬φ) :=
begin
exact MP Prop7 dne
end


lemma imp_if_imp_imp {φ ψ χ : formCL agents} : axCL (φ ~> χ) → axCL (φ ~> (ψ ~> χ)) :=
begin
intro h1,
exact MP (MP Prop2 (MP Prop1 Prop1)) h1
end


lemma cut1 {φ ψ χ θ : formCL agents} :
  axCL (θ ~> (φ ~> ψ)) → axCL (ψ ~> χ) → axCL (θ ~> (φ ~> χ)) :=
begin
intros h1 h2,
exact cut h1 (MP Prop2 (MP Prop1 h2))
end


lemma imp_switch {φ ψ χ : formCL agents} : axCL (φ ~> (ψ ~> χ)) → axCL (ψ ~> (φ ~> χ)) :=
begin
intro h1,
exact MP (MP Prop2 (MP Prop1 (MP Prop2 h1))) Prop1
end


lemma l2 {φ ψ χ : formCL agents} : axCL ((φ ~> (ψ ~> χ)) ~> (ψ ~> (φ ~> χ))) :=
begin
exact (MP (MP Prop2 (cut Prop2 hs1)) (MP Prop1 Prop1))
end


lemma hs2 {φ ψ χ : formCL agents} :
  axCL ((φ ~> ψ) ~> ((ψ ~> χ) ~> (φ ~> χ))) :=
begin
exact (MP l2 hs1)
end


lemma cut2 {φ ψ χ θ : formCL agents} :
  axCL (φ ~> ψ) → axCL (θ ~> (ψ ~> χ)) → axCL (θ ~> (φ ~> χ)) :=
begin
intros h1 h2,
exact imp_switch (cut h1 (imp_switch h2))
end


lemma double_imp {φ ψ : formCL agents} :
  axCL ((φ ~> (φ ~> ψ)) ~> (φ ~> ψ)) :=
begin
exact MP Prop2 (imp_switch iden)
end


lemma imp_imp_iff_imp {θ φ ψ : formCL agents} : 
  axCL (θ ~> (φ ~> (φ ~> ψ))) ↔ axCL (θ ~> (φ ~> ψ)) :=
begin
split,
{intro h1,
exact cut h1 double_imp},
{intro h1,
exact cut h1 Prop1}
end


lemma imp_shift {θ φ ψ χ : formCL agents} : 
  axCL (θ ~> (φ ~> (ψ ~> χ))) ↔ axCL (θ ~> (ψ ~> (φ ~> χ))) :=
begin
split,
repeat {intro h1, exact cut h1 (cut2 Prop1 Prop2)}
end


lemma left_and_imp {φ ψ χ : formCL agents} :
  axCL (ψ ~> ((φ & ψ) ~> χ)) → axCL ((φ & ψ) ~> χ) :=
begin
intro h1,
exact MP double_imp (cut Prop6 h1)
end


lemma and_right_imp {φ ψ χ : formCL agents} : 
  axCL ((φ & ψ) ~> χ) ↔ axCL (ψ ~> (φ ~> χ)) :=
begin
split, 
{intro h1,
exact MP (cut2 Prop1 Prop2) (cut1 Prop4 h1)},
intro h1,
exact left_and_imp (cut2 Prop5 h1)
end


lemma not_and_subst {φ ψ χ : formCL agents} : 
  axCL (φ ↔ ψ) → (axCL ¬(χ & φ) ↔ axCL ¬(χ & ψ)) :=
begin
intro h1, split, 
{intro h2,
exact MP (MP Prop3 (MP Prop1 h2)) (cut dne (MP double_imp (cut2 (cut Prop6 (MP Prop6 h1)) 
  (cut Prop5 Prop4))))},
{intro h2,
exact MP (MP Prop3 (MP Prop1 h2)) (cut dne (MP double_imp (cut2 (cut Prop6 (MP Prop5 h1)) 
  (cut Prop5 Prop4))))},
end


lemma not_contra {φ : formCL agents} : 
  axCL ¬(φ & ¬φ) :=
begin
exact MP (MP Prop3 (cut dne Prop6)) (cut dne Prop5)
end


lemma phi_and_true {φ : formCL agents} : axCL ((φ&¬⊥) ↔ φ) :=
begin
exact (MP (MP Prop4 Prop5) (MP (imp_switch Prop4) iden))
end


lemma imp_and_and_imp {φ ψ χ θ : formCL agents} : 
  axCL (((φ ~> ψ) & (χ ~> θ))) → axCL (((φ & χ) ~> (ψ & θ))) :=
begin
intro h,
exact (MP double_imp (cut (cut Prop5 (MP Prop5 h)) (cut2 (cut Prop6 (MP Prop6 h)) Prop4)))
end


lemma not_contra_equiv_true {φ : formCL agents} : 
  axCL (¬(φ & ¬φ) ↔ ⊤) :=
begin
exact (MP (MP Prop4 (MP Prop1 iden)) (MP Prop1 not_contra))
end


lemma contrapos {φ ψ : formCL agents} :
  axCL ((¬ψ) ~> (¬φ)) ↔ axCL (φ ~> ψ) :=
begin
split,
intro h1,
exact MP Prop7 h1,
intro h1,
exact MP (cut (cut (MP hs1 dni) (MP hs2 dne)) Prop7) h1,
end


lemma iff_not {φ ψ : formCL agents} :
  axCL (φ ↔ ψ) → axCL (¬ψ ↔ ¬φ) :=
begin
intro h1,
have h2 : axCL (φ ~> ψ), from MP Prop5 h1,
have h3 : axCL (ψ ~> φ), from MP Prop6 h1,
rw ←contrapos at h2,
rw ←contrapos at h3,
exact (MP (MP Prop4 h2) h3)
end


lemma contra_equiv_false {φ : formCL agents} : 
  axCL ((φ & ¬φ) ↔ ⊥) :=
begin
have h1 := iff_not not_contra_equiv_true,
exact (MP (MP Prop4 (cut dni (cut (MP Prop6 h1) dne))) (cut dni (cut (MP Prop5 h1) dne)))
end


lemma and_switch {φ ψ : formCL agents} : axCL ((φ & ψ) ↔ (ψ & φ)) :=
begin
exact (MP (MP Prop4 (MP double_imp (cut Prop5 (imp_switch (cut Prop6 Prop4))))) 
(MP double_imp (cut Prop5 (imp_switch (cut Prop6 Prop4)))))
end


lemma and_commute {φ ψ χ : formCL agents} : axCL (((φ & ψ) & χ) ↔ (φ & (ψ & χ))) :=
begin
exact MP (MP Prop4 (MP double_imp (imp_imp_iff_imp.mp 
  (cut (cut Prop5 Prop6) (cut2 Prop6 (cut1 Prop4 (imp_switch (cut (cut Prop5 Prop5) Prop4)))))))) 
  (MP double_imp (imp_imp_iff_imp.mp (cut (cut Prop6 Prop5) 
  (imp_switch (cut Prop5 (cut1 Prop4 (cut2 (cut Prop6 Prop6) Prop4)))))))
end


lemma imp_and_imp {φ ψ χ : formCL agents} : 
  axCL (φ ~> ψ) → axCL ((χ & φ) ~> (χ & ψ)) :=
begin
intros h1,
exact imp_and_and_imp (MP (MP Prop4 iden) h1)
end


lemma demorgans {φ ψ : formCL agents} : axCL (¬(φ & ψ)) ↔ axCL (φ ~> ¬ψ) :=
begin
split,
intro h1,
exact (and_right_imp.mp (MP (contrapos.mpr (MP Prop5 and_switch)) h1)),
intro h1,
exact (MP (contrapos.mpr (MP Prop5 and_switch)) (and_right_imp.mpr h1))
end



-- lemma explosion {ψ : formCL agents} : axCL (⊥ ~> ψ) :=
-- begin
-- apply contrapos.MP, exact (MP Prop1 iden)
-- end


-- lemma exfalso {φ ψ : formCL agents} : axCL ((φ & ¬φ) ~> ψ) :=
-- begin
-- exact cut not_contra explosion
-- end


-- lemma box_dn {φ : formCL agents} : axCL ((¬□φ) ↔ ¬(□(¬¬φ))) :=
-- begin
-- exact MP (MP Prop4 (contrapos.MPr (MP kdist (nec dne)))) (contrapos.MPr (MP kdist (nec dni)))
-- end


-- lemma dual_equiv1 {φ : formCL agents} : axCL ((□φ) ↔ (¬(◇(¬φ)))) :=
-- begin
-- exact MP (MP Prop4 (cut (contrapos.MP (MP Prop6 box_dn)) dni)) 
--   (cut dne (contrapos.MP (MP Prop5 box_dn)))
-- end


-- lemma dual_equiv2 {φ : formCL agents} : axCL ((¬(□¬φ)) ↔ (◇φ)) :=
-- begin
-- exact MP (MP Prop4 iden) iden,
-- end

-- New
-- double_imp
--  axCL ((φ ~> (φ ~> ψ)) ~> (φ ~> ψ)) :=


-- lemma imp_imp_iff_imp {θ φ ψ : formCL agents} : 
--   axCL (θ ~> (φ ~> (φ ~> ψ))) ↔ axCL (θ ~> (φ ~> ψ)) :=

-- lemma imp_and_imp {φ ψ χ : formCL agents} : 
--   axCL (φ ~> ψ) → axCL ((χ & φ) ~> (χ & ψ)) :=

lemma and_iden {φ: formCL agents}:
  axCL (φ ~> (φ & φ)) :=
begin
  have hdi: axCL ((φ ~> (φ ~> (φ & φ))) ~> (φ ~> (φ & φ))), from double_imp,
  apply MP hdi,
  exact Prop4,
end


lemma imp_and {φ ψ : formCL agents}:
  axCL (φ ~> ψ) → axCL (φ ~> (φ & ψ))  :=
begin
  intro h,
  have hab: axCL (φ ~> (φ & φ)), from and_iden,
  have hbc: axCL ((φ & φ) ~> (φ & ψ)), from imp_and_imp h,
  exact cut hab hbc,
end