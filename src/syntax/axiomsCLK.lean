import syntax.syntaxCLK 
import syntax.formula
open set

variables {agents : Type}

---------------------- Proof System ----------------------


-- Proof system for coalition logic
/-
Prop1-Prop7 taken from :
Copyright (c) 2021 Paula Neeley. All rights reserved.
Authors: Paula Neeley
-/
inductive axCLK : formCLK agents → Prop 
-- (Prop) Propositional tautologiess
| Prop1 {φ ψ}                 : axCLK (φ ~> (ψ ~> φ))
| Prop2 {φ ψ χ}               : axCLK ((φ ~> (ψ ~> χ)) ~> ((φ ~> ψ) ~> (φ ~> χ)))
| Prop3 {φ ψ}                 : axCLK (((¬φ) ~> (¬ψ)) ~> (((¬φ) ~> ψ) ~> φ))
| Prop4 {φ ψ}                 : axCLK (φ ~> (ψ ~> (φ & ψ)))
| Prop5 {φ ψ}                 : axCLK ((φ & ψ) ~> φ)
| Prop6 {φ ψ}                 : axCLK ((φ & ψ) ~> ψ)
| Prop7 {φ ψ}                 : axCLK (((¬ φ) ~> (¬ψ)) ~> (ψ ~> φ))
-- (⊥) ¬[G]⊥
| Bot   {G}                   : axCLK (¬ ([G] ⊥))
-- (⊤) [G]⊤
| Top   {G}                   : axCLK ([G] ⊤)
-- (N) (¬[∅]¬φ → [N]φ)
| N     {φ}                   : axCLK ((¬ ([∅] (¬ φ))) ~> [univ] φ)
-- (M) [G](φ ∧ ψ) → [G]φ
| M     {φ ψ} {G}             : axCLK (([G] (φ & ψ)) ~> [G] φ)
-- (S) ([G]φ ∧ [F]ψ) → [G ∪ F](φ ∧ ψ), when G ∩ F = ∅
| S     {φ ψ} {G F} 
        (hInt: G ∩ F = ∅)     : axCLK ((([G]φ) & ([F]ψ)) ~> [G ∪ F] (φ & ψ))
-- (MP) ⊢ φ, φ → ψ ⇒⊢ ψ
| MP    {φ ψ} 
        (hImp: axCLK (φ ~> ψ))
        (hL: axCLK φ)          : axCLK (ψ)
-- (Eq) ⊢ φ ↔ ψ ⇒⊢ [G]φ ↔ [G]ψ
| Eq    {φ ψ} {G}
        (h: axCLK (φ ↔ ψ))     : axCLK (([G] φ) ↔ ([G] ψ))

| K     {φ ψ} {i}              : axCLK ((K' i (φ ~> ψ)) ~> ((K' i φ) ~> (K' i ψ)))
| T     {φ} {i}                : axCLK ((K' i φ) ~> φ)
| Four  {φ} {i}                : axCLK ((K' i φ) ~> (K' i (K' i φ)))
| Five  {φ} {i}                : axCLK ((¬ (K' i (φ))) ~> (¬(K' i (K' i φ))))
| RN    {φ} {i}
        (h: axCLK φ)           : axCLK (K' i φ)


instance formulaCLK: formula (formCLK agents) :=
{ bot := formCLK.bot,
  and := formCLK.and,
  imp := formCLK.imp,
  not := λ φ, ¬ φ,
  iff := λ φ ψ, φ ↔ ψ,
  top := ⊤,
  notdef := by simp,
  iffdef := by simp,
  topdef := by simp,
  ax := axCLK,
  p1 := @axCLK.Prop1 agents,
  p2 := @axCLK.Prop2 agents,
  p3 := @axCLK.Prop3 agents,
  p4 := @axCLK.Prop4 agents,
  p5 := @axCLK.Prop5 agents,
  p6 := @axCLK.Prop6 agents,
  p7 := @axCLK.Prop7 agents,
  mp := @axCLK.MP agents, }

instance CLformulaCLK: CLformula agents (formCLK agents) :=
{ eff:= λ G φ, [G] φ,
  Bot:= @axCLK.Bot agents,
  Top:= @axCLK.Top agents,
  N  := @axCLK.N agents,
  M  := @axCLK.M agents,
  S  := @axCLK.S agents,
  Eq := @axCLK.Eq agents, }


