/-
Authors : Kai Obendrauf
Following the paper "A Modal Logic for Coalitional Power in Games" by Mark Pauly 
and the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley

This file contains the inductive type formCL and its notation, 
as well as the axioms for CL and instances of the differenct applicaple formula classes
(Pformula, Pformula_ax, and CLformula) for CL.
-/

import syntax.formula

open set

----------------------------------------------------------
-- Syntax
----------------------------------------------------------
inductive formCL (agents : Type) : Type
-- φ := ⊥ | p | φ → φ| φ ∧ φ | [G]φ
  | bot                                  : formCL
  | var  (n   : nat)                     : formCL
  | and  (φ ψ : formCL)                  : formCL
  | imp  (φ ψ : formCL)                  : formCL
  | eff  (G   : set agents) (φ : formCL) : formCL


notation `'⊥`       : 80   := formCL.bot
prefix   `'p`       : 80   := formCL.var
infix    `'∧`       : 79   := formCL.and
infixr    `'→`      : 78   := formCL.imp
notation `'¬`       : 80 φ :=  φ '→ '⊥
notation `'[` G `]` : 80 φ := formCL.eff G φ
notation `'⊤`       : 80   := '¬ ('⊥)
notation φ `'∨` ψ   : 79   := '¬ (('¬ φ) '∧ ('¬ ψ))
notation φ `'↔` ψ   : 78   := (φ '→ ψ) '∧ (ψ '→ φ)

----------------------------------------------------------
-- Axioms
----------------------------------------------------------
-- Proof system for coalition logic
inductive axCL {agents : Type} : formCL agents → Prop 
-- (Prop) Propositional tautologies
| Prop1 {φ ψ}                 : axCL (φ '→ (ψ '→ φ))
| Prop2 {φ ψ χ}               : axCL ((φ '→ (ψ '→ χ)) '→ ((φ '→ ψ) '→ (φ '→ χ)))
| Prop3 {φ ψ}                 : axCL ((('¬φ) '→ ('¬ψ)) '→ ((('¬φ) '→ ψ) '→ φ))
| Prop4 {φ ψ}                 : axCL (φ '→ (ψ '→ (φ '∧ ψ)))
| Prop5 {φ ψ}                 : axCL ((φ '∧ ψ) '→ φ)
| Prop6 {φ ψ}                 : axCL ((φ '∧ ψ) '→ ψ)
| Prop7 {φ ψ}                 : axCL ((('¬ φ) '→ ('¬ψ)) '→ (ψ '→ φ))
-- (⊥) ¬[G]⊥
| Bot   {G}                   : axCL ('¬ ('[G] '⊥))
-- (⊤) [G]⊤
| Top   {G}                   : axCL ('[G] '⊤)
-- (N) (¬[∅]¬φ → [N]φ)
| N     {φ}                   : axCL (('¬ ('[∅] ('¬ φ))) '→ '[univ] φ)
-- (M) [G](φ ∧ ψ) → [G]φ
| M     {φ ψ} {G}             : axCL (('[G] (φ '∧ ψ)) '→ '[G] φ)
-- (S) ([G]φ ∧ [F]ψ) → [G ∪ F](φ ∧ ψ), when G ∩ F = ∅
| S     {φ ψ} {G F} 
        (hInt : G ∩ F = ∅)    : axCL ((('[G]φ) '∧ ('[F]ψ)) '→ '[G ∪ F] (φ '∧ ψ))
-- (MP) ⊢ φ, φ → ψ ⇒ ⊢ ψ
| MP    {φ ψ} 
        (hImp : axCL (φ '→ ψ))
        (hL : axCL φ)         : axCL (ψ)
-- (Eq) ⊢ φ ↔ ψ ⇒ ⊢ [G]φ ↔ [G]ψ
| Eq    {φ ψ} {G}
        (h : axCL (φ '↔ ψ))   : axCL (('[G] φ) '↔ ('[G] ψ))

prefix `'⊢` : 70 := axCL

----------------------------------------------------------
-- Class Instances
----------------------------------------------------------
instance formulaCL {agents : Type} : Pformula (formCL agents) :=
{ bot := formCL.bot,
  var := formCL.var,
  and := formCL.and,
  imp := formCL.imp, }


instance formula_axCL {agents : Type} : Pformula_ax (formCL agents) :=
{ ax := axCL,
  p1 := @axCL.Prop1 agents,
  p2 := @axCL.Prop2 agents,
  p3 := @axCL.Prop3 agents,
  p4 := @axCL.Prop4 agents,
  p5 := @axCL.Prop5 agents,
  p6 := @axCL.Prop6 agents,
  p7 := @axCL.Prop7 agents,
  mp := @axCL.MP agents, }


instance CLformulaCL {agents : Type} : CLformula agents (formCL agents) :=
{ eff := λ G φ, '[G] φ,
  Bot := @axCL.Bot agents,
  Top := @axCL.Top agents,
  N   := @axCL.N agents,
  M   := @axCL.M agents,
  S   := @axCL.S agents,
  Eq  := @axCL.Eq agents, }


