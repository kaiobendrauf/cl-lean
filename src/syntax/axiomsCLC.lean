import syntax.syntaxCLC 
import syntax.formula
open set

variables {agents : Type}

---------------------- Proof System ----------------------


-- Proof system for coalition logic
/-
Prop1-Prop7 taken from :
Copyright (c) 2021 Paula Neeley. All rights reserved.
Author: Paula Neeley
-/
inductive axCLC : formCLC agents → Prop 
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
        (h: axCLC (φ ↔ ψ))     : axCLC (([G] φ) ↔ ([G] ψ))

| K     {φ ψ} {i}              : axCLC ((K' i (φ ~> ψ)) ~> ((K' i φ) ~> (K' i ψ)))
| T     {φ} {i}                : axCLC ((K' i φ) ~> φ)
| Four  {φ} {i}                : axCLC ((K' i φ) ~> (K' i (K' i φ)))
| Five  {φ} {i}                : axCLC ((¬(K' i (φ))) ~> (¬(K' i (K' i φ))))
| C     {φ} {G}                : axCLC ((C' G φ) ~> (E' G (φ & C' G  φ)))
| RN    {φ} {i}
        (h: axCLC φ)           : axCLC (K' i φ)
| RC    {φ ψ} {G} 
        (h: axCLC (ψ ~> (E' G (φ & ψ))))             
                                : axCLC (ψ ~> (C' G φ))


instance formulaCLC: formula (formCLC agents) :=
{ bot := ⊥,
  and := formCLC.and,
  imp := formCLC.imp,
  not := λ φ, ¬ φ,
  iff := λ φ ψ, φ ↔ ψ,
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
  mp := @axCLC.MP agents, }


instance CLformulaCL: CLformula agents (formCLC agents) :=

{ eff:= λ G φ, [G] φ,
  Bot:= @axCLC.Bot agents,
  Top:= @axCLC.Top agents,
  N  := @axCLC.N agents,
  M  := @axCLC.M agents,
  S  := @axCLC.S agents,
  Eq := @axCLC.Eq agents, }


