/-
Authors: Kai Obendrauf
Following the paper "Coalition Logic with Individual, Distributed and Common Knowledge
by Thomas Ågotnes and Natasha Alechina
and the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley

This file contains the defintions of semantic entailment and validity for CL.
-/

import CLLean.Syntax.syntaxCLK
import CLLean.Semantics.model

open Logic formCLK Set

----------------------------------------------------------
-- Common Knowledge Path
----------------------------------------------------------
def C_path {agents : Type} {m : modelECL agents} :
  List agents → List m.f.states →  m.f.states →  m.f.states → Prop
  | List.nil,  _,         s, t => false
  | (i :: is), List.nil,  s, t => t ∈ (m.f.rel i s)
  | (i :: is), (u :: us), s, t => (u ∈ (m.f.rel i s) ∧ (C_path is us u t))

----------------------------------------------------------
-- Semantic Entailment
----------------------------------------------------------

def s_entails_CLK {agents : Type} (m : modelECL agents) :
  m.f.states → formCLK agents → Prop
  | s, bot       => false
  | s, (var n)   => s ∈ m.v n
  | s, (imp φ ψ) => (s_entails_CLK m s φ) → (s_entails_CLK m s ψ)
  | s, (.and φ ψ) => (s_entails_CLK m s φ) ∧ (s_entails_CLK m s ψ)
  | s, (_[G] φ)   => {t : m.f.states | s_entails_CLK m t φ} ∈ m.f.E.E (s) (G)
  | s, (.K i φ)   => ∀ t : m.f.states, t ∈ (m.f.rel i s) → s_entails_CLK m t φ

notation m ";" s "_⊨" φ => s_entails_CLK m s φ

lemma not_s_entails_imp {agents: Type} (m : modelECL agents) (s : m.f.states) (φ : formCLK agents) :
  (¬ (m; s _⊨ φ)) ↔ (m; s _⊨ (_¬ φ)) := by
  constructor
  repeat
    intro h1 h2
    simp only [s_entails_CLK] at *
    exact h1 h2

lemma s_entails_CLK_conjunction {agents : Type} {m : modelECL agents} {s : m.f.states}
  {φs : List (formCLK agents)} :
  (m; s _⊨ (finite_conjunction φs)) ↔ ∀ φ ∈ φs, m; s _⊨ φ := by
  induction φs
  case nil =>
    simp only [finite_conjunction, List.not_mem_nil, IsEmpty.forall_iff, imp_true_iff, iff_true]
    change s_entails_CLK m s ⊤'
    simp only [s_entails_CLK, IsEmpty.forall_iff]
  case cons φ φs ih =>
    unfold finite_conjunction
    show s_entails_CLK m s (φ _∧ finite_conjunction φs) ↔ _
    simp [s_entails_CLK, List.mem_cons, forall_eq_or_imp]
    intro h
    exact ih

----------------------------------------------------------
-- Validity
----------------------------------------------------------

-- φ is valid in a model M = (f,v), if it is entailed by every state of the model
def valid_m {agents : Type} (m: modelECL agents) (φ : formCLK agents) :=
  ∀ s : m.f.states, m; s _⊨ φ

notation m "_⊨" φ => valid_m m φ

-- φ is globally valid, if it is valid in all models
def global_valid {agents : Type} (φ : formCLK agents) :=
  ∀ m : modelECL agents, m _⊨ φ

notation "_⊨" φ => global_valid φ
