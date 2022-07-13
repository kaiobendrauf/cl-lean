/-
Authors : Kai Obendrauf
Following the paper "A Modal Logic for Coalitional Power in Games" by Mark Pauly 
and the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley
-/

inductive formCL (agents : Type) : Type
-- φ := ⊥ | p | φ → φ| φ ∧ φ | [G]φ
  | bot                      : formCL
  | var  (n   : nat)         : formCL
  | and  (φ ψ : formCL)      : formCL
  | imp  (φ ψ : formCL)      : formCL
  | eff  (G   : set agents) 
         (φ   : formCL)      : formCL


-- form notation
notation `⊥`       : 80   := formCL.bot
prefix   `p`       : 80   := formCL.var
infix    `&`       : 25   := formCL.and
infix    `~>`      : 25   := formCL.imp
notation `¬`       : 80 φ :=  φ ~> ⊥
notation `[` G `]` : 90 φ := formCL.eff G φ
notation `⊤`       : 80   := ¬ (⊥)
notation φ `∨` ψ          := ¬ ((¬ φ) & (¬ ψ))
notation φ `↔` ψ          := (φ ~> ψ) & (ψ ~> φ)
