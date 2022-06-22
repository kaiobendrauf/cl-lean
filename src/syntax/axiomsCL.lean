import syntax.syntaxCL 
import data.set.basic

open set

variables {agents : Type}

---------------------- Proof System ----------------------


-- Proof system for coalition logic
/-
Prop1-Prop7 taken from :
Copyright (c) 2021 Paula Neeley. All rights reserved.
Author: Paula Neeley
-/
inductive axCL : formCL agents → Prop 
| Prop1 {φ ψ}                 : axCL (φ ~> (ψ ~> φ))
| Prop2 {φ ψ χ}               : axCL ((φ ~> (ψ ~> χ)) ~> ((φ ~> ψ) ~> (φ ~> χ)))
| Prop3 {φ ψ}                 : axCL (((¬φ) ~> (¬ψ)) ~> (((¬φ) ~> ψ) ~> φ))
| Prop4 {φ ψ}                 : axCL (φ ~> (ψ ~> (φ & ψ)))
| Prop5 {φ ψ}                 : axCL ((φ & ψ) ~> φ)
| Prop6 {φ ψ}                 : axCL ((φ & ψ) ~> ψ)
| Prop7 {φ ψ}                 : axCL (((¬ φ) ~> (¬ψ)) ~> (ψ ~> φ))
| Bot   {G}                   : axCL (¬ ([G] ⊥))
| Top   {G}                   : axCL ([G] ⊤)
| N     {φ}                   : axCL ((¬ ([∅] (¬ φ))) ~> [univ] φ)
| M     {φ ψ} {G}             : axCL (([G] (φ & ψ)) ~> [G] φ)
| S     {φ ψ} {G F} 
        (hInt: G ∩ F = ∅)     : axCL ((([G]φ) & ([F]ψ)) ~> [G ∪ F] (φ & ψ))
| MP    {φ ψ} (hImp: axCL (φ ~> ψ))
        (hL: axCL φ)          : axCL (ψ)
| Eq    {φ ψ} {G}
        (h: axCL (φ ↔ ψ))     : axCL (([G] φ) ↔ ([G] ψ))



structure formula (form: Type) :=
(bot : form)
(and : form → form → form)
(imp : form → form → form)
(top : form)
-- (top := imp bot bot)
(not : form → form)
(iff : form → form → form)
(ax  : form → Prop)
(p1 : ∀ φ ψ : form, ax (imp φ ( imp ψ φ)))
(p2 : ∀ φ ψ χ : form, ax (imp (imp φ (imp ψ χ)) (imp (imp φ ψ) (imp φ χ))))
(p3 : ∀ φ ψ : form, ax (imp (imp (not φ) (not ψ)) (imp (imp (not φ) ψ) φ)))
(p4 : ∀ φ ψ : form, ax (imp φ (imp ψ (and φ ψ))))
(p5 : ∀ φ ψ : form, ax (imp (and φ ψ) φ))
(p6 : ∀ φ ψ : form, ax (imp (and φ ψ) ψ))
(p7 : ∀ φ ψ : form, ax (imp (imp (not φ) (not ψ)) (imp ψ φ)))
(mp : ∀ φ ψ : form, ax (imp φ ψ) → ax φ → ax ψ)
(notdef: not = λ f, imp f bot)
(iffdef: iff = λ f g, and (imp f g) (imp g f))
(topdef: top = imp bot bot)

-- structure formula_prop_ax {form: Type} (ft: formula form) :=
-- (Prop1: form → form → )
-- -- (Prop1: λ φ ψ, ft.ax (ft.imp φ (ft.imp ψ φ)))


-- structure formula_agents (agents: Type) (form: Type) :=
-- (ft :  formula form)
-- (eff : set agents → form → form)

def formulaCL: formula (formCL agents) :=
{
  bot := ⊥,
  and := λ φ ψ, φ & ψ,
  imp := formCL.imp,
  not := λ φ, ¬ φ,
  iff := λ φ ψ, φ ↔ ψ,
  top := ⊤,
  ax  := axCL,
  p1 := assume φ ψ, @axCL.Prop1 agents φ ψ,
  p2 := assume φ ψ χ, @axCL.Prop2 agents φ ψ χ,
  p3 := assume φ ψ, @axCL.Prop3 agents φ ψ,
  p4 := assume φ ψ, @axCL.Prop4 agents φ ψ,
  p5 := assume φ ψ, @axCL.Prop5 agents φ ψ,
  p6 := assume φ ψ, @axCL.Prop6 agents φ ψ,
  p7 := assume φ ψ, @axCL.Prop7 agents φ ψ,
  mp := assume φ ψ, @axCL.MP agents φ ψ,
  notdef := by simp,
  iffdef := by simp,
  topdef := by simp,
}


-- def formulaCL_agents: formula_agents agents (formCL agents) :=
-- {
--    ft := {
--            bot := ⊥,
--            and := λ φ ψ, φ & ψ,
--            imp := formCL.imp,
--            top := ⊤,
--            ax  := axCL
--         },
--    eff := formCL.eff,
-- }

