/-
Authors: Kai Obendrauf
Following the paper "Coalition Logic with Individual, Distributed and Common Knowledge 
by Thomas Ågotnes and Natasha Alechina,
and the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley

This file contains the inductive type formCLK and its notation, 
as well as the axioms for CLK and instances of the differenct applicaple formula classes
(Pformula, Pformula_ax, CLformula, Kformula and Cformula) for CLK.
-/

import CLLean.Syntax.formula

open set

----------------------------------------------------------
-- Syntax
----------------------------------------------------------
inductive formCLK (agents : Type) : Type
-- φ := ⊥ | p | φ → φ| φ ∧ φ | [G]φ | K i φ | C G φ
  | bot                                   : formCLK
  | var  (n   : nat)                      : formCLK
  | and  (φ ψ : formCLK)                  : formCLK
  | imp  (φ ψ : formCLK)                  : formCLK
  | eff  (G   : set agents) (φ : formCLK) : formCLK
  | K    (a   : agents)     (φ : formCLK) : formCLK

-- Pformula Instance
instance formulaCLK {agents : Type} : Pformula (formCLK agents) :=
{ bot := formCLK.bot,
  var := formCLK.var,
  and := formCLK.and,
  imp := formCLK.imp, }

-- Notation
notation `'⊥`       : 80   := formCLK.bot
prefix   `'p`       : 80   := formCLK.var
infix    `'∧`       : 79   := formCLK.and
infixr    `'→`      : 78   := formCLK.imp
notation `'¬`       : 80 φ :=  φ '→ '⊥
notation `'[` G `]` : 80 φ := formCLK.eff G φ
notation `'⊤`       : 80   := '¬ ('⊥)
notation φ `'∨` ψ   : 79   := '¬ (('¬ φ) '∧ ('¬ ψ))
notation φ `'↔` ψ   : 78   := (φ '→ ψ) '∧ (ψ '→ φ)
notation `'K`       : 77   := formCLK.K 
notation `'E`       : 77   := λ G φ, (finite_conjunction (list.map (λ i, 'K i φ) 
                               (finset.to_list (finite.to_finset (finite.of_fintype G)))))


-- ----------------------------------------------------------
-- -- Axioms
-- ----------------------------------------------------------
-- Proof system for CLK
inductive axCLK {agents : Type} : formCLK agents → Prop 
-- (Prop) Propositional tautologies
| Prop1 {φ ψ}                 : axCLK (φ '→ (ψ '→ φ))
| Prop2 {φ ψ χ}               : axCLK ((φ '→ (ψ '→ χ)) '→ ((φ '→ ψ) '→ (φ '→ χ)))
| Prop3 {φ ψ}                 : axCLK ((('¬φ) '→ ('¬ψ)) '→ ((('¬φ) '→ ψ) '→ φ))
| Prop4 {φ ψ}                 : axCLK (φ '→ (ψ '→ (φ '∧ ψ)))
| Prop5 {φ ψ}                 : axCLK ((φ '∧ ψ) '→ φ)
| Prop6 {φ ψ}                 : axCLK ((φ '∧ ψ) '→ ψ)
| Prop7 {φ ψ}                 : axCLK ((('¬ φ) '→ ('¬ψ)) '→ (ψ '→ φ))
-- (⊥) ¬[G]⊥
| Bot   {G}                   : axCLK ('¬ ('[G] '⊥))
-- (⊤) [G]⊤
| Top   {G}                   : axCLK ('[G] '⊤)
-- (N) (¬[∅]¬φ → [N]φ)
| N     {φ}                   : axCLK (('¬ ('[∅] ('¬ φ))) '→ '[univ] φ)
-- (M) [G](φ ∧ ψ) → [G]φ
| M     {φ ψ} {G}             : axCLK (('[G] (φ '∧ ψ)) '→ '[G] φ)
-- (S) ([G]φ ∧ [F]ψ) → [G ∪ F](φ ∧ ψ), when G ∩ F = ∅
| S     {φ ψ} {G F} 
        (hInt : G ∩ F = ∅)    : axCLK ((('[G]φ) '∧ ('[F]ψ)) '→ '[G ∪ F] (φ '∧ ψ))
-- (MP) ⊢ φ, φ → ψ ⇒ ⊢ ψ
| MP    {φ ψ} 
        (hImp : axCLK (φ '→ ψ))
        (hL : axCLK φ)        : axCLK (ψ)
-- (Eq) ⊢ φ ↔ ψ ⇒ ⊢ [G]φ ↔ [G]ψ
| Eq    {φ ψ} {G}
        (h : axCLK (φ '↔ ψ))  : axCLK (('[G] φ) '↔ ('[G] ψ))
-- (K) Ki(φ → ψ) → (Kiφ → Kiψ)
| K     {φ ψ} {i}             : axCLK (('K i (φ '→ ψ)) '→ (('K i φ) '→ ('K i ψ)))
-- (T) Kiφ → φ
| T     {φ} {i}               : axCLK (('K i φ) '→ φ)
-- (4) Kiφ → KiKiφ
| Four  {φ} {i}               : axCLK (('K i φ) '→ ('K i ('K i φ)))
-- (5) ¬Kiφ → Ki¬Kiφ
| Five  {φ} {i}               : axCLK (('¬ 'K i (φ)) '→ (('K i ('¬ 'K i φ))))
-- (RN) ⊢ φ ⇒⊢ Kiφ
| RN    {φ} {i} (h: axCLK φ)  : axCLK ('K i φ)

prefix `'⊢` : 70 := axCLK

----------------------------------------------------------
-- Class Instances
----------------------------------------------------------
instance formula_axCLK {agents : Type} : Pformula_ax (formCLK agents) :=
{ ax := axCLK,
  p1 := @axCLK.Prop1 agents,
  p2 := @axCLK.Prop2 agents,
  p3 := @axCLK.Prop3 agents,
  p4 := @axCLK.Prop4 agents,
  p5 := @axCLK.Prop5 agents,
  p6 := @axCLK.Prop6 agents,
  p7 := @axCLK.Prop7 agents,
  mp := @axCLK.MP agents, }

instance CLformulaCLK {agents : Type} : CLformula agents (formCLK agents) :=
{ eff := λ G φ, '[G] φ,
  Bot := @axCLK.Bot agents,
  Top := @axCLK.Top agents,
  N   := @axCLK.N agents,
  M   := @axCLK.M agents,
  S   := @axCLK.S agents,
  Eq  := @axCLK.Eq agents, }

instance KformulaCLK {agents : Type} : Kformula agents (formCLK agents) :=
{ knows := 'K,
  K     := @axCLK.K agents,
  T     := @axCLK.T agents,
  Four  := @axCLK.Four agents,
  Five  := @axCLK.Five agents,
  RN    := @axCLK.RN agents, }
