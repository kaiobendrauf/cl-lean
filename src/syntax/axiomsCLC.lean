import syntax.syntaxCLC 
import syntax.formula
-- import data.fintype.basic
open set

---------------------- Proof System ----------------------


-- Proof system for coalition logic
/-
Prop1-Prop7 taken from :
Copyright (c) 2021 Paula Neeley. All rights reserved.
Author: Paula Neeley
-/
inductive axCLC {agents  : Type} : formCLC agents → Prop 
-- (Prop) Propositional tautologiess
| Prop1 {φ ψ}                 : axCLC (φ ~> (ψ ~> φ))
| Prop2 {φ ψ χ}               : axCLC ((φ ~> (ψ ~> χ)) ~> ((φ ~> ψ) ~> (φ ~> χ)))
| Prop3 {φ ψ}                 : axCLC (((¬φ) ~> (¬ψ)) ~> (((¬φ) ~> ψ) ~> φ))
| Prop4 {φ ψ}                 : axCLC (φ ~> (ψ ~> (φ & ψ)))
| Prop5 {φ ψ}                 : axCLC ((φ & ψ) ~> φ)
| Prop6 {φ ψ}                 : axCLC ((φ & ψ) ~> ψ)
| Prop7 {φ ψ}                 : axCLC (((¬φ) ~> (¬ψ)) ~> (ψ ~> φ))
-- (⊥) ¬[G]⊥
| Bot   {G}                   : axCLC (¬([G] ⊥))
-- (⊤) [G]⊤
| Top   {G}                   : axCLC ([G] ⊤)
-- (N) (¬[∅]¬φ → [N]φ)
| N     {φ}                   : axCLC ((¬([∅] (¬φ))) ~> [univ] φ)
-- (M) [G](φ ∧ ψ) → [G]φ
| M     {φ ψ} {G}             : axCLC (([G] (φ & ψ)) ~> [G] φ)
-- (S) ([G]φ ∧ [F]ψ) → [G ∪ F](φ ∧ ψ), when G ∩ F = ∅
| S     {φ ψ} {G F} 
        (hInt: G ∩ F = ∅)     : axCLC ((([G]φ) & ([F]ψ)) ~> [G ∪ F] (φ & ψ))
-- (MP) ⊢ φ, φ → ψ ⇒⊢ ψ
| MP    {φ ψ} 
        (hImp: axCLC (φ ~> ψ))
        (hL: axCLC φ)          : axCLC (ψ)
-- (Eq) ⊢ φ ↔ ψ ⇒⊢ [G]φ ↔ [G]ψ
| Eq    {φ ψ} {G}
        (h: axCLC (φ <~> ψ))    : axCLC (([G] φ) <~> ([G] ψ))

| K     {φ ψ} {i}              : axCLC ((k i (φ ~> ψ)) ~> ((k i φ) ~> (k i ψ)))
| T     {φ} {i}                : axCLC ((k i φ) ~> φ)
| Four  {φ} {i}                : axCLC ((k i φ) ~> (k i (k i φ)))
| Five  {φ} {i}                : axCLC ((¬(k i (φ))) ~> (¬(k i (k i φ))))
| C     {φ} {G}                : axCLC ((c G φ) ~> (e G (φ & (c G φ))))
| RN    {φ} {i}
        (h: axCLC φ)           : axCLC (k i φ)
| RC    {φ ψ} {G} 
        (h: axCLC (ψ ~> (e G (φ & ψ))))             
                                : axCLC (ψ ~> (c G φ))


instance formulaCLC {agents : Type} : formula (formCLC agents) :=
{ bot := ⊥,
  and := formCLC.and,
  imp := formCLC.imp,
  not := λ φ, ¬ φ,
  iff := λ φ ψ, φ <~> ψ,
  top := ⊤,
  notdef := by simp,
  iffdef := by simp,
  topdef := by simp,

  ax  := axCLC,
  p1 := @axCLC.Prop1 agents,
  p2 := @axCLC.Prop2 agents,
  p3 := @axCLC.Prop3 agents,
  p4 := @axCLC.Prop4 agents,
  p5 := @axCLC.Prop5 agents,
  p6 := @axCLC.Prop6 agents,
  p7 := @axCLC.Prop7 agents,
  mp := @axCLC.MP    agents, }

instance CLformulaCLC {agents : Type} : CLformula agents (formCLC agents) :=
{ eff := λ G φ, [G] φ,
  Bot := @axCLC.Bot agents,
  Top := @axCLC.Top agents,
  N   := @axCLC.N   agents,
  M   := @axCLC.M   agents,
  S   := @axCLC.S   agents,
  Eq  := @axCLC.Eq agents, }

instance KformulaCLC {agents : Type} : Kformula agents (formCLC agents) :=
{ knows := formCLC.K,
  everyone_knows := formCLC.E,
  K := @axCLC.K agents,
  T := @axCLC.T agents,
  Four := @axCLC.Four agents,
  Five := @axCLC.Five agents,
  RN := @axCLC.RN agents, }

instance CformulaCLC {agents : Type} : Cformula agents (formCLC agents) :=
{ common_know := formCLC.C,
  C := @axCLC.C agents,
  RC := @axCLC.RC agents, }
