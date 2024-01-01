/-
Authors: Kai Obendrauf

This file contains generic classes for the following types of formulas:
- Pformula    : contains propositional atomic Pformulas and operators.
- Pformula_ax : contains propositional axioms.
- CLformula   : contains the coalition operator and associated axioms.
- Kformula    : contains the K and E knowledge operators and associated axioms.
- Cformula    : contains the C knowledge operator (common knowledge) and associated axioms.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Finite

open Set

namespace Logic

----------------------------------------------------------
-- Propositional Logic
----------------------------------------------------------

-- propositional formula
class Pformula (form : Type) :=
(bot : form)
(var : ℕ → form)
(and : form → form → form)
(imp : form → form → form)

notation  "⊥'" => Pformula.bot
infix :79 "∧'" => Pformula.and
infixr:78 "→'" => Pformula.imp
prefix:80 "¬'" => λ φ => φ →' ⊥'
notation  "⊤'" => ¬' ⊥'
infix :79 "∨'" => λ φ ψ => (¬' φ) →' ψ
infix :78 "↔'" => λ φ ψ => (φ →' ψ) ∧' (ψ →' φ)

-- Finite conjunction of Pformulas
def finite_conjunction {form : Type} [Pformula form] : (List form) → form
  | []         => ⊤'
  | (φ :: φs)  => φ ∧' (finite_conjunction φs)

-- Finite disjunction of Pformulas
def finite_disjunction {form : Type} [Pformula form] : (List form) → form
  | []         => ⊥'
  | (φ :: φs)  => φ ∨' (finite_disjunction φs)

-- propositional axioms
class Pformula_ax (form : Type) extends Pformula form :=
(ax : form → Prop)
(p1 : ∀ φ ψ : form, ax (φ →' (ψ →' φ)))
(p2 : ∀ φ ψ χ : form, ax ((φ →' (ψ →' χ)) →' ((φ →' ψ) →' (φ →' χ))))
(p3 : ∀ φ ψ : form, ax (((¬' φ) →' (¬' ψ)) →' (((¬' φ) →' ψ) →' φ)))
(p4 : ∀ φ ψ : form, ax (φ →' (ψ →' (φ ∧' ψ))))
(p5 : ∀ φ ψ : form, ax ((φ ∧' ψ) →' φ))
(p6 : ∀ φ ψ : form, ax ((φ ∧' ψ) →' ψ))
(p7 : ∀ φ ψ : form, ax (((¬' φ) →' (¬' ψ)) →' (ψ →' φ)))
(mp : ∀ φ ψ : form, ax (φ →' ψ) → ax φ → ax ψ)

def p1  {form : Type} [pax : Pformula_ax form] := pax.p1
def p2  {form : Type} [pax : Pformula_ax form] := pax.p2
def p3  {form : Type} [pax : Pformula_ax form] := pax.p3
def p4  {form : Type} [pax : Pformula_ax form] := pax.p4
def p5  {form : Type} [pax : Pformula_ax form] := pax.p5
def p6  {form : Type} [pax : Pformula_ax form] := pax.p6
def p7  {form : Type} [pax : Pformula_ax form] := pax.p7
def mp  {form : Type} [pax : Pformula_ax form] := pax.mp

prefix:70 "⊢'" => Pformula_ax.ax

----------------------------------------------------------
-- Coalition Logic
----------------------------------------------------------

class CLformula (agents : outParam Type) (form : Type) [Pformula_ax form] :=
(eff : Set agents → form → form)
(Bot : ∀ G, ⊢' (¬' (eff G ⊥')))
(Top : ∀ G, ⊢' (eff G ⊤'))
(N : ∀ φ : form, ⊢' ((¬' (eff ∅ (¬' φ))) →' (eff univ φ)))
(M : ∀ φ ψ G, ⊢' ((eff G (φ ∧' ψ)) →' (eff G φ)))
(S : ∀ φ ψ G F, G ∩ F = ∅ → ⊢' (((eff G φ) ∧' (eff F ψ)) →' (eff (G ∪ F) (φ ∧' ψ))))
(Eq : ∀ φ ψ G, ⊢' (φ ↔' ψ) → ⊢' ((eff G φ) ↔' (eff G ψ)))

def Bot {agents : Type} {form : Type} [Pformula_ax form] [clf : CLformula agents form] :=
  clf.Bot
def Top {agents : Type} {form : Type} [Pformula_ax form] [clf : CLformula agents form] :=
  clf.Top
def N   {agents : Type} {form : Type} [Pformula_ax form] [clf : CLformula agents form] :=
  clf.N
def M   {agents : Type} {form : Type} [Pformula_ax form] [clf : CLformula agents form] :=
  clf.M
def S   {agents : Type} {form : Type} [Pformula_ax form] [clf : CLformula agents form] :=
  clf.S
def Eq  {agents : Type} {form : Type} [Pformula_ax form] [clf : CLformula agents form] :=
  clf.Eq

notation "['" G "]" φ => CLformula.eff G φ

----------------------------------------------------------
-- Epistemic Logic
----------------------------------------------------------

-- Individial Knowledge
class Kformula (agents : outParam Type) (form : Type) [pf : Pformula_ax form] :=
(knows : agents → form → form)
(K : ∀ φ ψ i, ⊢' ((knows i (φ →' ψ)) →' ((knows i φ) →' (knows i ψ))))
(T : ∀ φ i, ⊢' ((knows i φ) →' φ))
(Four : ∀ φ i, ⊢' ((knows i φ) →' (knows i (knows i φ))))
(Five : ∀ φ i, ⊢' ((¬' (knows i (φ))) →' (knows i (¬' (knows i φ)))))
(RN : ∀ φ i, ⊢' φ → ⊢' (knows i φ))

def K    {agents : Type} {form : Type} [Pformula_ax form] [kf : Kformula agents form] :=
  kf.K
def T    {agents : Type} {form : Type} [Pformula_ax form] [kf : Kformula agents form] :=
  kf.T
def Four {agents : Type} {form : Type} [Pformula_ax form] [kf : Kformula agents form] :=
  kf.Four
def Five {agents : Type} {form : Type} [Pformula_ax form] [kf : Kformula agents form] :=
  kf.Five
def RN   {agents : Type} {form : Type} [Pformula_ax form] [kf : Kformula agents form] :=
  kf.RN

notation "K'" => Kformula.knows
notation "E'" => λ G φ => (finite_conjunction (List.map (λ i => K' i φ) (Finset.toList
                                     (Finite.toFinset (Set.toFinite G)))))

-- Common Knowledge
class Cformula (agents : outParam Type) [hN : Fintype agents] (form : Type)
  [pf : Pformula_ax form] [kf : Kformula agents form] :=
(common_know : (Set (agents)) → form → form)
(C : ∀ φ: form, ∀ G: Set (agents), ⊢' ((common_know G φ) →' (E' G (φ ∧' (common_know G φ)))))
(RC : ∀ φ ψ : form, ∀ G : Set (agents), ⊢' (ψ →' (E' G (φ ∧' ψ))) → ⊢' (ψ →' (common_know G φ)))

def C  {agents : Type} {form : Type} [Fintype agents] [Pformula_ax form]
  [Kformula agents form] [cf : Cformula agents form] := cf.C
def RC {agents : Type} {form : Type} [Fintype agents] [Pformula_ax form]
  [Kformula agents form] [cf : Cformula agents form] := cf.RC

notation "C'" => Cformula.common_know

end Logic
