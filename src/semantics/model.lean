/-
Authors : Kai Obendrauf
Following the paper "A Modal Logic for Coalitional Power in Games" by Mark Pauly 
and the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley
-/

import semantics.playability 
local attribute [instance] classical.prop_decidable

structure frameCL (agents : Type) :=
(states : Type)
(hs     : nonempty states)
(ha     : nonempty agents)
(E      : playable_effectivity_struct states ha)

structure modelCL (agents : Type) :=
(f : frameCL agents)
(v : ℕ → set f.states)

