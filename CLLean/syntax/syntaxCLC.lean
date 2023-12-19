/-
Authors: Kai Obendrauf
Following the paper "Coalition Logic with Individual, Distributed and Common Knowledge 
by Thomas Ågotnes and Natasha Alechina,
and the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley

This file contains the inductive type formCLC and its notation, 
as well as the axioms for CLC and instances of the differenct applicaple formula classes
(Pformula, Pformula_ax, CLformula, Kformula and Cformula) for CLC.
-/

import syntax.formula

open set

----------------------------------------------------------
-- Syntax
----------------------------------------------------------
inductive formCLC (agents : Type) : Type
-- φ := ⊥ | p | φ → φ| φ ∧ φ | [G]φ | K i φ | C G φ
  | bot                                   : formCLC
  | var  (n   : nat)                      : formCLC
  | and  (φ ψ : formCLC)                  : formCLC
  | imp  (φ ψ : formCLC)                  : formCLC
  | eff  (G   : set agents) (φ : formCLC) : formCLC
  | K    (a   : agents)     (φ : formCLC) : formCLC
  | C    (G   : set agents) (φ : formCLC) : formCLC

-- Pformula Instance
instance formulaCLC {agents : Type} : Pformula (formCLC agents) :=
{ bot := formCLC.bot,
  var := formCLC.var,
  and := formCLC.and,
  imp := formCLC.imp, }

-- Notation
notation `'⊥`       : 80   := formCLC.bot
prefix   `'p`       : 80   := formCLC.var
infix    `'∧`       : 79   := formCLC.and
infixr    `'→`      : 78   := formCLC.imp
notation `'¬`       : 80 φ :=  φ '→ '⊥
notation `'[` G `]` : 80 φ := formCLC.eff G φ
notation `'⊤`       : 80   := '¬ ('⊥)
notation φ `'∨` ψ   : 79   := '¬ (('¬ φ) '∧ ('¬ ψ))
notation φ `'↔` ψ   : 78   := (φ '→ ψ) '∧ (ψ '→ φ)
notation `'K`       : 77   := formCLC.K 
notation `'E`       : 77   := λ G φ, (finite_conjunction (list.map (λ i, 'K i φ) 
                               (finset.to_list (finite.to_finset (finite.of_fintype G)))))
notation `'C`       : 77  := formCLC.C 


-- ----------------------------------------------------------
-- -- Axioms
-- ----------------------------------------------------------
-- Proof system for CLC
inductive axCLC {agents : Type} [hN : fintype agents] : formCLC agents → Prop 
-- (Prop) Propositional tautologies
| Prop1 {φ ψ}                 : axCLC (φ '→ (ψ '→ φ))
| Prop2 {φ ψ χ}               : axCLC ((φ '→ (ψ '→ χ)) '→ ((φ '→ ψ) '→ (φ '→ χ)))
| Prop3 {φ ψ}                 : axCLC ((('¬φ) '→ ('¬ψ)) '→ ((('¬φ) '→ ψ) '→ φ))
| Prop4 {φ ψ}                 : axCLC (φ '→ (ψ '→ (φ '∧ ψ)))
| Prop5 {φ ψ}                 : axCLC ((φ '∧ ψ) '→ φ)
| Prop6 {φ ψ}                 : axCLC ((φ '∧ ψ) '→ ψ)
| Prop7 {φ ψ}                 : axCLC ((('¬ φ) '→ ('¬ψ)) '→ (ψ '→ φ))
-- (⊥) ¬[G]⊥
| Bot   {G}                   : axCLC ('¬ ('[G] '⊥))
-- (⊤) [G]⊤
| Top   {G}                   : axCLC ('[G] '⊤)
-- (N) (¬[∅]¬φ → [N]φ)
| N     {φ}                   : axCLC (('¬ ('[∅] ('¬ φ))) '→ '[univ] φ)
-- (M) [G](φ ∧ ψ) → [G]φ
| M     {φ ψ} {G}             : axCLC (('[G] (φ '∧ ψ)) '→ '[G] φ)
-- (S) ([G]φ ∧ [F]ψ) → [G ∪ F](φ ∧ ψ), when G ∩ F = ∅
| S     {φ ψ} {G F} 
        (hInt : G ∩ F = ∅)    : axCLC ((('[G]φ) '∧ ('[F]ψ)) '→ '[G ∪ F] (φ '∧ ψ))
-- (MP) ⊢ φ, φ → ψ ⇒ ⊢ ψ
| MP    {φ ψ} 
        (hImp : axCLC (φ '→ ψ))
        (hL : axCLC φ)        : axCLC (ψ)
-- (Eq) ⊢ φ ↔ ψ ⇒ ⊢ [G]φ ↔ [G]ψ
| Eq    {φ ψ} {G}
        (h : axCLC (φ '↔ ψ))  : axCLC (('[G] φ) '↔ ('[G] ψ))
-- (K) Ki(φ → ψ) → (Kiφ → Kiψ)
| K     {φ ψ} {i}             : axCLC (('K i (φ '→ ψ)) '→ (('K i φ) '→ ('K i ψ)))
-- (T) Kiφ → φ
| T     {φ} {i}               : axCLC (('K i φ) '→ φ)
-- (4) Kiφ → KiKiφ
| Four  {φ} {i}               : axCLC (('K i φ) '→ ('K i ('K i φ)))
-- (5) ¬Kiφ → Ki¬Kiφ
| Five  {φ} {i}               : axCLC (('¬ 'K i (φ)) '→ (('K i ('¬ 'K i φ))))
-- (C) CGφ → EG(φ ∧ CGφ))
| C     {φ} {G}               : axCLC (('C G φ) '→ ('E G (φ '∧ ('C G φ))))
-- (RN) ⊢ φ ⇒⊢ Kiφ
| RN    {φ} {i} (h: axCLC φ)  : axCLC ('K i φ)
-- (RC) ⊢ ψ → EG(φ ∧ ψ) ⇒⊢ ψ → CGφ
| RC    {φ ψ} {G} 
        (h: axCLC (ψ '→ ('E G (φ '∧  ψ))))             
                             : axCLC (ψ '→ ('C G φ))

prefix `'⊢` : 70 := axCLC

----------------------------------------------------------
-- Class Instances
----------------------------------------------------------
instance formula_axCLC {agents : Type} [hN : fintype agents] : Pformula_ax (formCLC agents) :=
{ ax := axCLC,
  p1 := @axCLC.Prop1 agents hN,
  p2 := @axCLC.Prop2 agents hN,
  p3 := @axCLC.Prop3 agents hN,
  p4 := @axCLC.Prop4 agents hN,
  p5 := @axCLC.Prop5 agents hN,
  p6 := @axCLC.Prop6 agents hN,
  p7 := @axCLC.Prop7 agents hN,
  mp := @axCLC.MP agents hN, }

instance CLformulaCLC {agents : Type} [hN : fintype agents] : CLformula agents (formCLC agents) :=
{ eff := λ G φ, '[G] φ,
  Bot := @axCLC.Bot agents hN,
  Top := @axCLC.Top agents hN,
  N   := @axCLC.N agents hN,
  M   := @axCLC.M agents hN,
  S   := @axCLC.S agents hN,
  Eq  := @axCLC.Eq agents hN, }

instance KformulaCLC {agents : Type} [hN : fintype agents] : Kformula agents (formCLC agents) :=
{ knows := 'K,
  K     := @axCLC.K agents hN,
  T     := @axCLC.T agents hN,
  Four  := @axCLC.Four agents hN,
  Five  := @axCLC.Five agents hN,
  RN    := @axCLC.RN agents hN, }

instance CformulaCLC {agents : Type} [hN : fintype agents] : Cformula agents (formCLC agents) :=
{ common_know := formCLC.C,
  C  := @axCLC.C agents hN,
  RC := @axCLC.RC agents hN, }