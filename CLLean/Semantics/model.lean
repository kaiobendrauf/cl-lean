/-
Authors: Kai Obendrauf
Following the paper "A Modal Logic for Coalitional Power in Games" by Mark Pauly
the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley
and the paper "Coalition Logic with Individual, Distributed and Common Knowledge 
by Thomas Ågotnes and Natasha Alechina.

This file contains the structure definitions for frames and models for CL and CLK. 
Note that CLC uses CLK frames and models.
-/

import CLLean.Semantics.playability
import Mathlib.Order.Filter.Basic

structure frameCL (agents : Type) :=
(states : Type)
(hs     : Nonempty states)
(E      : playable_effectivity_struct agents states)

structure modelCL (agents : Type) :=
(f : frameCL agents)
(v : ℕ → Set f.states)

structure frameECL (agents : Type) :=
(states    : Type)
(hs        : Nonempty states)
(E         : truly_playable_effectivity_struct agents states)
(rel       : agents → states → Set states)
(rfl       : ∀ i s, s ∈ (rel i s))
(sym       : ∀ i s t, t ∈ (rel i s) → s ∈ (rel i t))
(trans     : ∀ i s t u, t ∈ (rel i s) → u ∈ (rel i t) → u ∈ (rel i s))

structure modelECL (agents : Type) :=
(f : frameECL agents)
(v : ℕ → Set f.states)
