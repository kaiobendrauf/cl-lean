import syntax.syntaxCL 
import data.set.basic

open set

variables {agents : Type}

---------------------- Proof System ----------------------


-- Proof system for coalition logic
/-
Prop1-Prop7 taken from :
Copyright (c) 2021 Paula Neeley. All rights reserved.
Author: Paula Neeley
-/
inductive axCL : formCL agents  → Prop 
| Prop1 {φ ψ}                 : axCL (φ ~> (ψ ~> φ))
| Prop2 {φ ψ χ}               : axCL ((φ ~> (ψ ~> χ)) ~> ((φ ~> ψ) ~> (φ ~> χ)))
| Prop3 {φ ψ}                 : axCL (((¬φ) ~> (¬ψ)) ~> (((¬φ) ~> ψ) ~> φ))
| Prop4 {φ ψ}                 : axCL (φ ~> (ψ ~> (φ & ψ)))
| Prop5 {φ ψ}                 : axCL ((φ & ψ) ~> φ)
| Prop6 {φ ψ}                 : axCL ((φ & ψ) ~> ψ)
| Prop7 {φ ψ}                 : axCL (((¬ φ) ~> (¬ψ)) ~> (ψ ~> φ))
| Bot   {G}                   : axCL (¬ ([G] ⊥))
| Top   {G}                   : axCL ([G] ⊤)
| N     {φ}                   : axCL ((¬ ([∅] (¬ φ))) ~> [univ] φ)
| M     {φ ψ} {G}             : axCL (([G] (φ & ψ)) ~> [G] φ)
| S     {φ ψ} {G F} 
        (hInt: G ∩ F = ∅)     : axCL ((([G]φ) & ([F]ψ)) ~> [G ∪ F] (φ & ψ))
| MP    {φ ψ} (hL: axCL φ) 
        (hImp: axCL (φ ~> ψ)) : axCL (ψ)
| Eq    {φ ψ} {G}
        (h: axCL (φ ↔ ψ))     : axCL (([G] φ) ↔ ([G] ψ))

