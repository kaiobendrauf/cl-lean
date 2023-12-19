/-
Authors: Kai Obendrauf
Following the paper "Coalition Logic with Individual, Distributed and Common Knowledge 
by Thomas Ågotnes and Natasha Alechina
and the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley

This file contains the inductive type formCLK and its notation
as well as the axioms for CLK and instances of the differenct applicaple formula classes
(Pformula, Pformula_ax, CLformula, Kformula and Cformula) for CLK.
-/

import CLLean.Syntax.formula

open Set

namespace Logic

----------------------------------------------------------
-- Syntax
----------------------------------------------------------
inductive formCLK (agents : Type) : Type
-- φ := ⊥ | p | φ → φ| φ ∧ φ | [G]φ | K i φ | C G φ
  | bot                                          : formCLK agents
  | var  (n   : Nat)                             : formCLK agents
  | and  (φ ψ : formCLK agents)                  : formCLK agents
  | imp  (φ ψ : formCLK agents)                  : formCLK agents
  | eff  (G   : Set agents) (φ : formCLK agents) : formCLK agents
  | K    (a   : agents)     (φ : formCLK agents) : formCLK agents

-- Pformula Instance
instance formulaCLK {agents : Type} : Pformula (formCLK agents) :=
{ bot := formCLK.bot
  var := formCLK.var
  and := formCLK.and
  imp := formCLK.imp, }

-- Notation
notation    "_⊥"         => formCLK.bot
prefix:80   "_p"         => formCLK.var
infix:79    "_∧"         => formCLK.and
infixr:78   "_→"         => formCLK.imp
notation:80 "_¬"       φ =>  φ _→ _⊥
notation:80 "_[" G "]" φ => formCLK.eff G φ
notation:80 "_⊤"         => _¬ (_⊥)
notation:79 φ "_∨" ψ     => _¬ ((_¬ φ) _∧ (_¬ ψ))
notation:78 φ "_↔" ψ     => (φ _→ ψ) _∧ (ψ _→ φ)
notation:1024 "_K"       => λ i φ => formCLK.K i φ
notation:1024 "_E"       => λ G φ => (finite_conjunction (List.map (λ i => _K i φ)
                               (Finset.toList (Finite.toFinset (Set.toFinite G)))))


-- ----------------------------------------------------------
-- -- Axioms
-- ----------------------------------------------------------
-- Proof system for CLK
inductive axCLK {agents : Type} : formCLK agents → Prop 
-- (Prop) Propositional tautologies
| Prop1 {φ ψ}                 : axCLK (φ _→ (ψ _→ φ))
| Prop2 {φ ψ χ}               : axCLK ((φ _→ (ψ _→ χ)) _→ ((φ _→ ψ) _→ (φ _→ χ)))
| Prop3 {φ ψ}                 : axCLK (((_¬φ) _→ (_¬ψ)) _→ (((_¬φ) _→ ψ) _→ φ))
| Prop4 {φ ψ}                 : axCLK (φ _→ (ψ _→ (φ _∧ ψ)))
| Prop5 {φ ψ}                 : axCLK ((φ _∧ ψ) _→ φ)
| Prop6 {φ ψ}                 : axCLK ((φ _∧ ψ) _→ ψ)
| Prop7 {φ ψ}                 : axCLK (((_¬ φ) _→ (_¬ψ)) _→ (ψ _→ φ))
-- (⊥) ¬[G]⊥
| Bot   {G}                   : axCLK (_¬ (_[G] _⊥))
-- (⊤) [G]⊤
| Top   {G}                   : axCLK (_[G] _⊤)
-- (N) (¬[∅]¬φ → [N]φ)
| N     {φ}                   : axCLK ((_¬ (_[∅] (_¬ φ))) _→ _[univ] φ)
-- (M) [G](φ ∧ ψ) → [G]φ
| M     {φ ψ} {G}             : axCLK ((_[G] (φ _∧ ψ)) _→ _[G] φ)
-- (S) ([G]φ ∧ [F]ψ) → [G ∪ F](φ ∧ ψ), when G ∩ F = ∅
| S     {φ ψ} {G F} 
        (hInt : G ∩ F = ∅)    : axCLK (((_[G]φ) _∧ (_[F]ψ)) _→ _[G ∪ F] (φ _∧ ψ))
-- (MP) ⊢ φ, φ → ψ ⇒ ⊢ ψ
| MP    {φ ψ} 
        (hImp : axCLK (φ _→ ψ))
        (hL : axCLK φ)        : axCLK (ψ)
-- (Eq) ⊢ φ ↔ ψ ⇒ ⊢ [G]φ ↔ [G]ψ
| Eq    {φ ψ} {G}
        (h : axCLK (φ _↔ ψ))  : axCLK ((_[G] φ) _↔ (_[G] ψ))
-- (K) Ki(φ → ψ) → (Kiφ → Kiψ)
| K     {φ ψ} {i}             : axCLK ((_K i (φ _→ ψ)) _→ ((_K i φ) _→ (_K i ψ)))
-- (T) Kiφ → φ
| T     {φ} {i}               : axCLK ((_K i φ) _→ φ)
-- (4) Kiφ → KiKiφ
| Four  {φ} {i}               : axCLK ((_K i φ) _→ (_K i (_K i φ)))
-- (5) ¬Kiφ → Ki¬Kiφ
| Five  {φ} {i}               : axCLK ((_¬ _K i (φ)) _→ ((_K i (_¬ _K i φ))))
-- (RN) ⊢ φ ⇒⊢ Kiφ
| RN    {φ} {i} (h: axCLK φ)  : axCLK (_K i φ)

prefix:70 "_⊢" => axCLK

----------------------------------------------------------
-- Class Instances
----------------------------------------------------------
instance formula_axCLK {agents : Type} : Pformula_ax (formCLK agents) :=
{ ax := axCLK
  p1 := @axCLK.Prop1 agents
  p2 := @axCLK.Prop2 agents
  p3 := @axCLK.Prop3 agents
  p4 := @axCLK.Prop4 agents
  p5 := @axCLK.Prop5 agents
  p6 := @axCLK.Prop6 agents
  p7 := @axCLK.Prop7 agents
  mp := @axCLK.MP agents, }

instance CLformulaCLK {agents : Type} : CLformula agents (formCLK agents) :=
{ eff := λ G φ => _[G] φ
  Bot := @axCLK.Bot agents
  Top := @axCLK.Top agents
  N   := @axCLK.N agents
  M   := @axCLK.M agents
  S   := @axCLK.S agents
  Eq  := @axCLK.Eq agents, }

instance KformulaCLK {agents : Type} : Kformula agents (formCLK agents) :=
{ knows := _K
  K     := @axCLK.K agents
  T     := @axCLK.T agents
  Four  := @axCLK.Four agents
  Five  := @axCLK.Five agents
  RN    := @axCLK.RN agents, }

end Logic
