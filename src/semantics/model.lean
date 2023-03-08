/-
Authors : Kai Obendrauf
Following the paper "A Modal Logic for Coalitional Power in Games" by Mark Pauly 
and the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley

This file contains the structure definitions for frames and models for CL and CLK. 
Note that CLC uses CLK frames and models.
-/

import semantics.playability

structure frameCL (agents : Type) :=
(states : Type)
(hs     : nonempty states)
(E      : playable_effectivity_struct agents states)

structure modelCL (agents : Type) :=
(f : frameCL agents)
(v : ℕ → set f.states)

structure frameCLK (agents : Type)  
  extends frameCL agents :=
(rel   : agents → states → set states)
(rfl   : ∀ i s, s ∈ (rel i s))
(sym   : ∀ i s t, t ∈ (rel i s) → s ∈ (rel i t))
(trans : ∀ i s t u, t ∈ (rel i s) → u ∈ (rel i t) → u ∈ (rel i s))

structure modelCLK (agents : Type) :=
(f : frameCLK agents)
(v : ℕ → set f.states)