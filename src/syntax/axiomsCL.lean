/-
Authors : Kai Obendrauf
Following the paper "A Modal Logic for Coalitional Power in Games" by Mark Pauly 
and the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley
-/

import syntax.syntaxCL 
import syntax.formula 
import semantics.semanticsCL

open set

variables {agents : Type}

---------------------- Proof System ----------------------

instance formulaCLC {agents : Type} : formula (formCL agents) :=
{ bot := ⊥,
  and := formCL.and,
  imp := formCL.imp,
  not := λ φ, ¬ φ,
  iff := λ φ ψ, φ ↔ ψ,
  top := ⊤,
  notdef := by simp,
  iffdef := by simp,
  topdef := by simp
}

-- Proof system for coalition logic
inductive axCL : formCL agents → Prop 
-- (Prop) Propositional tautologies
| Prop1 {φ ψ}                 : axCL (φ ~> (ψ ~> φ))
| Prop2 {φ ψ χ}               : axCL ((φ ~> (ψ ~> χ)) ~> ((φ ~> ψ) ~> (φ ~> χ)))
| Prop3 {φ ψ}                 : axCL (((¬φ) ~> (¬ψ)) ~> (((¬φ) ~> ψ) ~> φ))
| Prop4 {φ ψ}                 : axCL (φ ~> (ψ ~> (φ & ψ)))
| Prop5 {φ ψ}                 : axCL ((φ & ψ) ~> φ)
| Prop6 {φ ψ}                 : axCL ((φ & ψ) ~> ψ)
| Prop7 {φ ψ}                 : axCL (((¬ φ) ~> (¬ψ)) ~> (ψ ~> φ))
-- (⊥) ¬[G]⊥
| Bot   {G}                   : axCL (¬ ([G] ⊥))
-- (⊤) [G]⊤
| Top   {G}                   : axCL ([G] ⊤)
-- (N) (¬[∅]¬φ → [N]φ)
| N     {φ}                   : axCL ((¬ ([∅] (¬ φ))) ~> [univ] φ)
-- (M) [G](φ ∧ ψ) → [G]φ
| M     {φ ψ} {G}             : axCL (([G] (φ & ψ)) ~> [G] φ)
-- (S) ([G]φ ∧ [F]ψ) → [G ∪ F](φ ∧ ψ), when G ∩ F = ∅
| S     {φ ψ} {G F} 
        (hInt : G ∩ F = ∅)    : axCL ((([G]φ) & ([F]ψ)) ~> [G ∪ F] (φ & ψ))
-- (MP) ⊢ φ, φ → ψ ⇒⊢ ψ
| MP    {φ ψ} 
        (hImp : axCL (φ ~> ψ))
        (hL : axCL φ)         : axCL (ψ)
-- (Eq) ⊢ φ ↔ ψ ⇒⊢ [G]φ ↔ [G]ψ
| Eq    {φ ψ} {G}
        (h : axCL (φ ↔ ψ))    : axCL (([G] φ) ↔ ([G] ψ))


instance formula_axCL: formula_ax (formCL agents) :=
{ ax := axCL,
  p1 := @axCL.Prop1 agents,
  p2 := @axCL.Prop2 agents,
  p3 := @axCL.Prop3 agents,
  p4 := @axCL.Prop4 agents,
  p5 := @axCL.Prop5 agents,
  p6 := @axCL.Prop6 agents,
  p7 := @axCL.Prop7 agents,
  mp := @axCL.MP agents, }


instance CLformulaCL: CLformula agents (formCL agents) :=
{ eff := λ G φ, [G] φ,
  Bot := @axCL.Bot agents,
  Top := @axCL.Top agents,
  N   := @axCL.N agents,
  M   := @axCL.M agents,
  S   := @axCL.S agents,
  Eq  := @axCL.Eq agents, }
