/-
Authors: Kai Obendrauf
Following the paper "Coalition Logic with Individual, Distributed and Common Knowledge
by Thomas Ågotnes and Natasha Alechina
and the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley

This file contains the inductive type formCLC and its notation
as well as the axioms for CLC and instances of the differenct applicaple formula classes
(Pformula, Pformula_ax, CLformula, Kformula and Cformula) for CLC.
-/

import CLLean.Syntax.formula

open Logic Set

----------------------------------------------------------
-- Syntax
----------------------------------------------------------
inductive formCLC (agents : Type) : Type
-- φ := ⊥ | p | φ → φ| φ ∧ φ | [G]φ | K i φ | C G φ
  | bot                                          : formCLC agents
  | var  (n   : Nat)                             : formCLC agents
  | and  (φ ψ : formCLC agents)                  : formCLC agents
  | imp  (φ ψ : formCLC agents)                  : formCLC agents
  | eff  (G   : Set agents) (φ : formCLC agents) : formCLC agents
  | K    (a   : agents)     (φ : formCLC agents) : formCLC agents
  | C    (G   : Set agents) (φ : formCLC agents) : formCLC agents

-- Pformula Instance
instance formulaCLC {agents : Type} : Pformula (formCLC agents) :=
{ bot := formCLC.bot
  var := formCLC.var
  and := formCLC.and
  imp := formCLC.imp, }

-- Notation
notation    "_⊥"         => formCLC.bot
prefix:80   "_p"         => formCLC.var
infix:79    "_∧"         => formCLC.and
infixr:78   "_→"         => formCLC.imp
notation:80 "_¬"       φ =>  φ _→ _⊥
notation:80 "_[" G "]" φ => formCLC.eff G φ
notation:80 "_⊤"         => _¬ (_⊥)
notation:79 φ "_∨" ψ     => _¬ ((_¬ φ) _∧ (_¬ ψ))
notation:78 φ "_↔" ψ     => (φ _→ ψ) _∧ (ψ _→ φ)
notation:1024 "_K"       => λ i φ => formCLC.K i φ
notation:1024 "_E"       => λ G φ => (finite_conjunction (List.map (λ i => _K i φ)
                               (Finset.toList (Finite.toFinset (Set.toFinite G)))))
notation:1024 "_C"       => formCLC.C


-- ----------------------------------------------------------
-- -- Axioms
-- ----------------------------------------------------------
-- Proof system for CLC
inductive axCLC {agents : Type} [hN : Fintype agents] : formCLC agents → Prop
-- (Prop) Propositional tautologies
| Prop1 {φ ψ}                 : axCLC (φ _→ (ψ _→ φ))
| Prop2 {φ ψ χ}               : axCLC ((φ _→ (ψ _→ χ)) _→ ((φ _→ ψ) _→ (φ _→ χ)))
| Prop3 {φ ψ}                 : axCLC (((_¬φ) _→ (_¬ψ)) _→ (((_¬φ) _→ ψ) _→ φ))
| Prop4 {φ ψ}                 : axCLC (φ _→ (ψ _→ (φ _∧ ψ)))
| Prop5 {φ ψ}                 : axCLC ((φ _∧ ψ) _→ φ)
| Prop6 {φ ψ}                 : axCLC ((φ _∧ ψ) _→ ψ)
| Prop7 {φ ψ}                 : axCLC (((_¬ φ) _→ (_¬ψ)) _→ (ψ _→ φ))
-- (⊥) ¬[G]⊥
| Bot   {G}                   : axCLC (_¬ (_[G] _⊥))
-- (⊤) [G]⊤
| Top   {G}                   : axCLC (_[G] _⊤)
-- (N) (¬[∅]¬φ → [N]φ)
| N     {φ}                   : axCLC ((_¬ (_[∅] (_¬ φ))) _→ _[univ] φ)
-- (M) [G](φ ∧ ψ) → [G]φ
| M     {φ ψ} {G}             : axCLC ((_[G] (φ _∧ ψ)) _→ _[G] φ)
-- (S) ([G]φ ∧ [F]ψ) → [G ∪ F](φ ∧ ψ), when G ∩ F = ∅
| S     {φ ψ} {G F}
        (hInt : G ∩ F = ∅)    : axCLC (((_[G]φ) _∧ (_[F]ψ)) _→ _[G ∪ F] (φ _∧ ψ))
-- (MP) ⊢ φ, φ → ψ ⇒ ⊢ ψ
| MP    {φ ψ}
        (hImp : axCLC (φ _→ ψ))
        (hL : axCLC φ)        : axCLC (ψ)
-- (Eq) ⊢ φ ↔ ψ ⇒ ⊢ [G]φ ↔ [G]ψ
| Eq    {φ ψ} {G}
        (h : axCLC (φ _↔ ψ))  : axCLC ((_[G] φ) _↔ (_[G] ψ))
-- (K) Ki(φ → ψ) → (Kiφ → Kiψ)
| K     {φ ψ} {i}             : axCLC ((_K i (φ _→ ψ)) _→ ((_K i φ) _→ (_K i ψ)))
-- (T) Kiφ → φ
| T     {φ} {i}               : axCLC ((_K i φ) _→ φ)
-- (4) Kiφ → KiKiφ
| Four  {φ} {i}               : axCLC ((_K i φ) _→ (_K i (_K i φ)))
-- (5) ¬Kiφ → Ki¬Kiφ
| Five  {φ} {i}               : axCLC ((_¬ _K i (φ)) _→ ((_K i (_¬ _K i φ))))
-- (C) CGφ → EG(φ ∧ CGφ))
| C     {φ} {G}               : axCLC ((_C G φ) _→ (_E G (φ _∧ (_C G φ))))
-- (RN) ⊢ φ ⇒⊢ Kiφ
| RN    {φ} {i} (h: axCLC φ)  : axCLC (_K i φ)
-- (RC) ⊢ ψ → EG(φ ∧ ψ) ⇒⊢ ψ → CGφ
| RC    {φ ψ} {G}
        (h: axCLC (ψ _→ (_E G (φ _∧  ψ))))
                             : axCLC (ψ _→ (_C G φ))

prefix:70 "_⊢" => axCLC

----------------------------------------------------------
-- Class Instances
----------------------------------------------------------
instance formula_axCLC {agents : Type} [hN : Fintype agents] : Pformula_ax (formCLC agents) :=
{ ax := axCLC
  p1 := @axCLC.Prop1 agents hN
  p2 := @axCLC.Prop2 agents hN
  p3 := @axCLC.Prop3 agents hN
  p4 := @axCLC.Prop4 agents hN
  p5 := @axCLC.Prop5 agents hN
  p6 := @axCLC.Prop6 agents hN
  p7 := @axCLC.Prop7 agents hN
  mp := @axCLC.MP agents hN, }

instance CLformulaCLC {agents : Type} [hN : Fintype agents] : CLformula agents (formCLC agents) :=
{ eff := λ G φ => _[G] φ
  Bot := @axCLC.Bot agents hN
  Top := @axCLC.Top agents hN
  N   := @axCLC.N agents hN
  M   := @axCLC.M agents hN
  S   := @axCLC.S agents hN
  Eq  := @axCLC.Eq agents hN, }

instance KformulaCLC {agents : Type} [hN : Fintype agents] : Kformula agents (formCLC agents) :=
{ knows := _K
  K     := @axCLC.K agents hN
  T     := @axCLC.T agents hN
  Four  := @axCLC.Four agents hN
  Five  := @axCLC.Five agents hN
  RN    := @axCLC.RN agents hN, }

instance CformulaCLC {agents : Type} [hN : Fintype agents] : Cformula agents (formCLC agents) :=
{ common_know := formCLC.C
  C  := @axCLC.C agents hN
  RC := @axCLC.RC agents hN, }
