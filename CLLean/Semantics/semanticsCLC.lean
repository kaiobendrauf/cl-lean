/-
Authors: Kai Obendrauf
Following the paper "Coalition Logic with Individual, Distributed and Common Knowledge
by Thomas Ågotnes and Natasha Alechina
and the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley

This file contains the defintions of semantic entailment and validity for CL.
-/

import CLLean.Syntax.syntaxCLC
import CLLean.Semantics.model

open Logic formCLC Set

----------------------------------------------------------
-- Common Knowledge Path
----------------------------------------------------------
def C_path {agents : Type} {m : modelECL agents} :
    List agents → List m.f.states →  m.f.states →  m.f.states → Prop
  | List.nil,  _,         s, t => false
  | (i :: is), List.nil,  s, t => t ∈ m.f.rel i s
  | (i :: is), (u :: us), s, t => u ∈ m.f.rel i s ∧ C_path is us u t

----------------------------------------------------------
-- Semantic Entailment
----------------------------------------------------------

def s_entails_CLC {agents : Type} (m : modelECL agents) (s : m.f.states) :
    formCLC agents → Prop
  | .bot       => false
  | (var n)    => s ∈ m.v n
  | (imp φ ψ)  => s_entails_CLC m s φ → s_entails_CLC m s ψ
  | (.and φ ψ) => s_entails_CLC m s φ ∧ s_entails_CLC m s )
  | (_[G] φ)   => {t : m.f.states | s_entails_CLC m t φ} ∈ m.f.E.E s G
  | (.K i φ)   => ∀ t : m.f.states, t ∈ m.f.rel i s → s_entails_CLC m t φ
  | (.C G φ)   => ∀ t : m.f.states, (∃ la, (∀ a ∈ la, a ∈ G) ∧ ∃ ls, C_path la ls s t) →
                    s_entails_CLC m t φ

notation m ";" s "_⊨" φ => s_entails_CLC m s φ

lemma not_s_entails_imp {agents: Type} (m : modelECL agents) (s : m.f.states) (φ : formCLC agents) :
  (¬ (m; s _⊨ φ)) ↔ (m; s _⊨ (_¬ φ)) := by
  constructor
  repeat
  · intro h1 h2
    simp only [s_entails_CLC] at *
    exact h1 h2

lemma s_entails_CLC_conjunction {agents : Type} {m : modelECL agents} {s : m.f.states}
  {φs : List (formCLC agents)} :
  (m; s _⊨ (finite_conjunction φs)) ↔ ∀ φ ∈ φs, m; s _⊨ φ := by
  induction φs
  case nil =>
    simp only [finite_conjunction, List.not_mem_nil, IsEmpty.forall_iff, imp_true_iff, iff_true]
    show (s_entails_CLC m s ⊤')
    simp only [s_entails_CLC, IsEmpty.forall_iff]
  case cons φ φs ih =>
    unfold finite_conjunction
    change s_entails_CLC m s (φ _∧ finite_conjunction φs) ↔ _
    simp only [s_entails_CLC, Bool.not_eq_true, List.mem_cons, forall_eq_or_imp,
      and_congr_right_iff]
    intro _
    exact ih

----------------------------------------------------------
-- Validity
----------------------------------------------------------

-- φ is valid in a model M = (f,v), if it is entailed by every state of the model
def valid_m {agents : Type} (m: modelECL agents) (φ : formCLC agents) :=
  ∀ s : m.f.states, m; s _⊨ φ

notation m "_⊨" φ => valid_m m φ

-- φ is globally valid, if it is valid in all models
def global_valid {agents : Type} (φ : formCLC agents) :=
  ∀ m : modelECL agents, m _⊨ φ

notation "_⊨" φ => global_valid φ
