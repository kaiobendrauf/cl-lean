/-
Authors: Kai Obendrauf
Following the paper "A Modal Logic for Coalitional Power in Games" by Mark Pauly 
and the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley

This file contains the inductive type formCL and its notation
as well as the axioms for CL and instances of the differenct applicaple formula classes
(Pformula, Pformula_ax, and CLformula) for CL.
-/

import CLLean.Syntax.formula

open Logic Set

----------------------------------------------------------
-- Syntax
----------------------------------------------------------
inductive formCL (agents : Type) : Type
-- φ := ⊥ | p | φ → φ| φ ∧ φ | [G]φ
  | bot                                         : formCL agents
  | var  (n   : Nat)                            : formCL agents
  | and  (φ ψ : formCL agents)                  : formCL agents
  | imp  (φ ψ : formCL agents)                  : formCL agents
  | eff  (G   : Set agents) (φ : formCL agents) : formCL agents

notation    "_⊥"         => formCL.bot
prefix:80   "_p"         => formCL.var
infix:79    "_∧"         => formCL.and
infixr:78   "_→"         => formCL.imp
notation:80 "_¬"       φ =>  φ _→ _⊥
notation:80 "_[" G "]" φ => formCL.eff G φ
notation:80 "_⊤"         => _¬ (_⊥)
notation:79 φ "_∨" ψ     => _¬ ((_¬ φ) _∧ (_¬ ψ))
notation:78 φ "_↔" ψ     => (φ _→ ψ) _∧ (ψ _→ φ)

----------------------------------------------------------
-- Axioms
----------------------------------------------------------
-- Proof system for coalition logic
inductive axCL {agents : Type} : formCL agents → Prop 
-- (Prop) Propositional tautologies
| Prop1 {φ ψ}                 : axCL (φ _→ (ψ _→ φ))
| Prop2 {φ ψ χ}               : axCL ((φ _→ (ψ _→ χ)) _→ ((φ _→ ψ) _→ (φ _→ χ)))
| Prop3 {φ ψ}                 : axCL (((_¬φ) _→ (_¬ψ)) _→ (((_¬φ) _→ ψ) _→ φ))
| Prop4 {φ ψ}                 : axCL (φ _→ (ψ _→ (φ _∧ ψ)))
| Prop5 {φ ψ}                 : axCL ((φ _∧ ψ) _→ φ)
| Prop6 {φ ψ}                 : axCL ((φ _∧ ψ) _→ ψ)
| Prop7 {φ ψ}                 : axCL (((_¬ φ) _→ (_¬ψ)) _→ (ψ _→ φ))
-- (⊥) ¬[G]⊥
| Bot   {G}                   : axCL (_¬ (_[G] _⊥))
-- (⊤) [G]⊤
| Top   {G}                   : axCL (_[G] _⊤)
-- (N) (¬[∅]¬φ → [N]φ)
| N     {φ}                   : axCL ((_¬ (_[∅] (_¬ φ))) _→ _[univ] φ)
-- (M) [G](φ ∧ ψ) → [G]φ
| M     {φ ψ} {G}             : axCL ((_[G] (φ _∧ ψ)) _→ _[G] φ)
-- (S) ([G]φ ∧ [F]ψ) → [G ∪ F](φ ∧ ψ), when G ∩ F = ∅
| S     {φ ψ} {G F} 
        (hInt : G ∩ F = ∅)    : axCL (((_[G]φ) _∧ (_[F]ψ)) _→ _[G ∪ F] (φ _∧ ψ))
-- (MP) ⊢ φ, φ → ψ ⇒ ⊢ ψ
| MP    {φ ψ} 
        (hImp : axCL (φ _→ ψ))
        (hL : axCL φ)         : axCL (ψ)
-- (Eq) ⊢ φ ↔ ψ ⇒ ⊢ [G]φ ↔ [G]ψ
| Eq    {φ ψ} {G}
        (h : axCL (φ _↔ ψ))   : axCL ((_[G] φ) _↔ (_[G] ψ))

prefix:70 "_⊢" => axCL

----------------------------------------------------------
-- Class Instances
----------------------------------------------------------
instance formulaCL {agents : Type} : Pformula (formCL agents) :=
{ bot := formCL.bot
  var := formCL.var
  and := formCL.and
  imp := formCL.imp, }


instance formula_axCL {agents : Type} : Pformula_ax (formCL agents) :=
{ ax := axCL
  p1 := @axCL.Prop1 agents
  p2 := @axCL.Prop2 agents
  p3 := @axCL.Prop3 agents
  p4 := @axCL.Prop4 agents
  p5 := @axCL.Prop5 agents
  p6 := @axCL.Prop6 agents
  p7 := @axCL.Prop7 agents
  mp := @axCL.MP agents, }


instance CLformulaCL {agents : Type} : CLformula agents (formCL agents) :=
{ eff := λ G φ => _[G] φ
  Bot := @axCL.Bot agents
  Top := @axCL.Top agents
  N   := @axCL.N agents
  M   := @axCL.M agents
  S   := @axCL.S agents
  Eq  := @axCL.Eq agents, }
