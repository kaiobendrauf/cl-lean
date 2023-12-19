/-
Authors: Kai Obendrauf
Following the paper "Coalition Logic with Individual, Distributed and Common Knowledge 
by Thomas Ågotnes and Natasha Alechina
and the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley

This file contains the defintions of semantic entailment and validity for CL.
-/

import CLLean.Syntax.syntaxCLC 
import CLLean.Semantics.model
local attribute [instance] classical.prop_decidable

open formCLC Set

----------------------------------------------------------
-- Common Knowledge Path
----------------------------------------------------------
def C_path {agents : Type} {m : modelECL agents} : 
  List agents → List m.f.states →  m.f.states →  m.f.states → Prop
  | List.nil  _        s t := false
  | (i :: is) List.nil s t := t ∈ (m.f.rel i s)
  | (i :: is)(u :: us) s t := (u ∈ (m.f.rel i s) ∧ (C_path is us u t)) 

----------------------------------------------------------
-- Semantic Entailment
----------------------------------------------------------

def s_entails_CLC {agents : Type} (m : modelECL agents) : 
  m.f.states → formCLC agents → Prop
  | s bot       := false
  | s (var n)   := s ∈ m.v n
  | s (imp φ ψ) := (s_entails_CLC s φ) → (s_entails_CLC s ψ)
  | s (and φ ψ) := (s_entails_CLC s φ) ∧ (s_entails_CLC s ψ)
  | s ('[G] φ)   := {t : m.f.states | s_entails_CLC t φ} ∈ m.f.E.E (s) (G)
  | s ('K i φ)   := ∀ t : m.f.states, t ∈ (m.f.rel i s) → s_entails_CLC t φ
  | s ('C G φ)   := ∀ t : m.f.states, (∃ la, (∀ a ∈ la, a ∈ G) ∧ ∃ ls, C_path la ls s t) → 
                    s_entails_CLC t φ

notation m `;` s `'⊨` φ := s_entails_CLC m s φ

lemma not_s_entails_imp {agents: Type} (m : modelECL agents) (s : m.f.states) (φ : formCLC agents) :
  (¬ (m; s '⊨ φ)) ↔ (m; s '⊨ ('¬ φ)) :=
begin
  split
  repeat {intro h1 h2, exact h1 h2}
end

lemma s_entails_CLC_conjunction {agents : Type} {m : modelECL agents} {s : m.f.states} 
  {φs : List (formCLC agents)} : 
  (m; s '⊨ (finite_conjunction φs)) ↔ ∀ φ ∈ φs, m; s '⊨ φ :=
begin
  induction φs with φ φs ih
  { simp only [finite_conjunction, List.not_mem_nil, forall_false_left, implies_true_iff, iff_true]
    show s_entails_CLC m s '⊤
      simp only [s_entails_CLC, forall_false_left], }
  { unfold finite_conjunction
    show s_entails_CLC m s (φ '∧ finite_conjunction φs) ↔ _
      simp [s_entails_CLC, List.mem_cons_iff, forall_eq_or_imp, and.congr_right_iff]
      intro h
      exact ih, }
end

----------------------------------------------------------
-- Validity
----------------------------------------------------------

-- φ is valid in a model M = (f,v), if it is entailed by every state of the model
def valid_m {agents : Type} (m: modelECL agents) (φ : formCLC agents) := 
  ∀ s : m.f.states, m; s '⊨ φ

notation m `'⊨` φ := valid_m m φ

-- φ is globally valid, if it is valid in all models
def global_valid {agents : Type} (φ : formCLC agents) :=
  ∀ m : modelECL agents, m '⊨ φ

notation `'⊨` φ := global_valid φ
