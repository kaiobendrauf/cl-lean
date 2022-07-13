/-
Authors : Kai Obendrauf
Following the paper "A Modal Logic for Coalitional Power in Games" by Mark Pauly 
and the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley
-/

import syntax.syntaxCL 
import semantics.playability 
import semantics.model
local attribute [instance] classical.prop_decidable

variable {agents : Type}

open formCL set

----------------------------------------------------------
-- Semantic Entailment
----------------------------------------------------------

-- Definition of semantic entailment
def s_entails_CL : ∀ m : modelCL agents,
  m.f.states → formCL agents → Prop
  | m s bot           := false
  | m s (var n)       := s ∈ m.v n
  | m s (imp φ ψ)     := (s_entails_CL m s φ) → (s_entails_CL m s ψ)
  | m s (and φ ψ)     := (s_entails_CL m s φ) ∧ (s_entails_CL m s ψ)
  | m s ([G] φ)       := {t : m.f.states | s_entails_CL m t φ} ∈ m.f.E.E (s) (G)


-- φ is valid in a model M = (f,v), if it is entailed by every state of the model
def valid_m (m : modelCL agents) (φ : formCL agents) := 
  ∀ s, s_entails_CL m s φ

-- φ is globally valid, if it is valid in all models
def global_valid (φ : formCL agents) :=
  ∀ m, valid_m m φ

lemma not_s_entails_imp (m : modelCL agents) : ∀ s φ, 
  (¬(s_entails_CL m s φ)) ↔ (s_entails_CL m s (¬ φ)) :=
begin
  intros s φ, split,
  repeat {intros h1 h2, exact h1 h2},
end

