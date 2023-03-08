/-
Authors : Kai Obendrauf
Following the paper "A Modal Logic for Coalitional Power in Games" by Mark Pauly 
and the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley

This file contains the defintions of semantic entailment and validity for CL.
-/

import syntax.syntaxCL 
import semantics.playability 
import semantics.model
local attribute [instance] classical.prop_decidable

open formCL set

----------------------------------------------------------
-- Semantic Entailment
----------------------------------------------------------

-- Definition of semantic entailment
def s_entails_CL {agents : Type} (m : modelCL agents) :
  m.f.states → formCL agents → Prop
  | s bot      := false
  | s (var n)  := s ∈ m.v n
  | s (φ '→ ψ) := (s_entails_CL s φ) → (s_entails_CL s ψ)
  | s (φ '∧ ψ) := (s_entails_CL s φ) ∧ (s_entails_CL s ψ)
  | s ('[G] φ) := {t : m.f.states | s_entails_CL t φ} ∈ m.f.E.E (s) (G)

notation ⟨m, s⟩ `'⊨` φ := s_entails_CL m s φ

lemma not_s_entails_imp {agents: Type} (m : modelCL agents) (s : m.f.states) (φ : formCL agents) :
  (¬ (⟨m, s⟩ '⊨ φ)) ↔ (⟨m, s⟩ '⊨ ('¬ φ)) :=
begin
  split,
  repeat {intros h1 h2, exact h1 h2},
end

----------------------------------------------------------
-- Validity
----------------------------------------------------------

-- φ is valid in a model M = (f,v), if it is entailed by every state of the model
def valid_m {agents: Type} (m : modelCL agents) (φ : formCL agents) := 
  ∀ s, ⟨m, s⟩ '⊨ φ

notation m `'⊨` φ := valid_m m φ

-- φ is globally valid, if it is valid in all models
def global_valid {agents: Type} (φ : formCL agents) :=
  ∀ m, m '⊨ φ

notation `'⊨` φ := global_valid φ

