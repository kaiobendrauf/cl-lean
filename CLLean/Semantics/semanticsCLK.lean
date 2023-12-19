/-
Authors: Kai Obendrauf
Following the paper "Coalition Logic with Individual, Distributed and Common Knowledge 
by Thomas Ågotnes and Natasha Alechina
and the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley

This file contains the defintions of semantic entailment and validity for CL.
-/

import CLLean.Syntax.syntaxCLK 
import CLLean.Semantics.model
local attribute [instance] classical.prop_decidable

open formCLK Set

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

def s_entails_CLK {agents : Type} (m : modelECL agents) : 
  m.f.states → formCLK agents → Prop
  | s bot       := false
  | s (var n)   := s ∈ m.v n
  | s (imp φ ψ) := (s_entails_CLK s φ) → (s_entails_CLK s ψ)
  | s (and φ ψ) := (s_entails_CLK s φ) ∧ (s_entails_CLK s ψ)
  | s ('[G] φ)   := {t : m.f.states | s_entails_CLK t φ} ∈ m.f.E.E (s) (G)
  | s ('K i φ)   := ∀ t : m.f.states, t ∈ (m.f.rel i s) → s_entails_CLK t φ

notation m `;` s `'⊨` φ := s_entails_CLK m s φ

lemma not_s_entails_imp {agents: Type} (m : modelECL agents) (s : m.f.states) (φ : formCLK agents) :
  (¬ (m; s '⊨ φ)) ↔ (m; s '⊨ ('¬ φ)) :=
begin
  split
  repeat {intro h1 h2, exact h1 h2}
end

lemma s_entails_CLK_conjunction {agents : Type} {m : modelECL agents} {s : m.f.states} 
  {φs : List (formCLK agents)} : 
  (m; s '⊨ (finite_conjunction φs)) ↔ ∀ φ ∈ φs, m; s '⊨ φ :=
begin
  induction φs with φ φs ih
  { simp only [finite_conjunction, List.not_mem_nil, forall_false_left, implies_true_iff, iff_true]
    show s_entails_CLK m s '⊤
      simp only [s_entails_CLK, forall_false_left], }
  { unfold finite_conjunction
    show s_entails_CLK m s (φ '∧ finite_conjunction φs) ↔ _
      simp [s_entails_CLK, List.mem_cons_iff, forall_eq_or_imp, and.congr_right_iff]
      intro h
      exact ih, }
end

----------------------------------------------------------
-- Validity
----------------------------------------------------------

-- φ is valid in a model M = (f,v), if it is entailed by every state of the model
def valid_m {agents : Type} (m: modelECL agents) (φ : formCLK agents) := 
  ∀ s : m.f.states, m; s '⊨ φ

notation m `'⊨` φ := valid_m m φ

-- φ is globally valid, if it is valid in all models
def global_valid {agents : Type} (φ : formCLK agents) :=
  ∀ m : modelECL agents, m '⊨ φ

notation `'⊨` φ := global_valid φ
