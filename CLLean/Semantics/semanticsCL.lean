/-
Authors: Kai Obendrauf
Following the paper "A Modal Logic for Coalitional Power in Games" by Mark Pauly
and the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley

This file contains the defintions of semantic entailment and validity for CL.
-/

import CLLean.Syntax.syntaxCL
import CLLean.Semantics.model

open Logic formCL Set

----------------------------------------------------------
-- Semantic Entailment
----------------------------------------------------------

-- Definition of semantic entailment
def s_entails_CL {agents : Type} (m : modelCL agents) (s : m.f.states) :
    formCL agents → Prop
  | _⊥       => false
  | (.var n) => s ∈ m.v n
  | (φ _→ ψ) => (s_entails_CL m s φ) → (s_entails_CL m s ψ)
  | (φ _∧ ψ) => (s_entails_CL m s φ) ∧ (s_entails_CL m s ψ)
  | (_[G] φ) => {t : m.f.states | s_entails_CL m t φ} ∈ m.f.E.E (s) (G)

notation m ";" s "_⊨" φ => s_entails_CL m s φ

lemma not_s_entails_imp {agents: Type} (m : modelCL agents) (s : m.f.states) (φ : formCL agents) :
    (¬ (m; s _⊨ φ)) ↔ (m; s _⊨ (_¬ φ)) := by
  constructor
  repeat
    intro h1 h2
    simp only [s_entails_CL] at *
    exact h1 h2

----------------------------------------------------------
-- Validity
----------------------------------------------------------

-- φ is valid in a model M = (f,v), if it is entailed by every state of the model
def valid_m {agents: Type} (m : modelCL agents) (φ : formCL agents) :=
  ∀ s : m.f.states, m; s _⊨ φ

notation m "_⊨" φ => valid_m m  φ

-- φ is globally valid, if it is valid in all models
def global_valid {agents: Type} (φ : formCL agents) :=
  ∀ m, valid_m m φ

notation "_⊨" φ => global_valid φ
