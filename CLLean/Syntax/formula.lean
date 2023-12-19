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

open set

----------------------------------------------------------
-- Propositional Logic
----------------------------------------------------------

-- propositional formula
class Pformula (form : Type) :=
(bot : form)
(var : ℕ → form)
(and : form → form → form)
(imp : form → form → form)

notation `⊥'` : 80 := Pformula.bot 
infix    `∧'` : 79 := Pformula.and
infixr   `→'` : 78 := Pformula.imp
notation `¬'` : 80 := λ φ, φ →' ⊥'
notation `⊤'` : 80 := ¬' ⊥'
infix    `∨'` : 79 := λ φ ψ, (¬' φ) →' ψ
infix    `↔'` : 78 := λ φ ψ, (φ →' ψ) ∧' (ψ →' φ)

-- finite conjunction of Pformulas
def finite_conjunction {form : Type} [pf : Pformula form] : (list form) → form
  | []         := ⊤'
  | (φ :: φs)  := φ ∧' (finite_conjunction φs) 

-- finite disjunction of Pformulas
def finite_disjunction {form : Type} [pf : Pformula form] : (list form) → form
  | []         := ⊥'
  | (φ :: φs)  := φ ∨' (finite_disjunction φs)

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

prefix `⊢'` : 70 := Pformula_ax.ax

----------------------------------------------------------
-- Coalition Logic
----------------------------------------------------------

class CLformula (agents : out_param Type) (form : Type) [Pformula_ax form] :=
(eff : set agents → form → form)
(Bot : ∀ G, ⊢' (¬' (eff G ⊥')))
(Top : ∀ G, ⊢' (eff G ⊤'))
(N : ∀ φ : form, ⊢' ((¬' (eff ∅ (¬' φ))) →' (eff univ φ)))
(M : ∀ φ ψ G, ⊢' ((eff G (φ ∧' ψ)) →' (eff G φ)))
(S : ∀ φ ψ G F, G ∩ F = ∅ → ⊢' (((eff G φ) ∧' (eff F ψ)) →' (eff (G ∪ F) (φ ∧' ψ))))
(Eq : ∀ φ ψ G, ⊢' (φ ↔' ψ) → ⊢' ((eff G φ) ↔' (eff G ψ)))

def Bot {agents : Type} {form : Type} [pf : Pformula_ax form] [clf : CLformula agents form] := 
  clf.Bot
def Top {agents : Type} {form : Type} [pf : Pformula_ax form] [clf : CLformula agents form] := 
  clf.Top
def N   {agents : Type} {form : Type} [pf : Pformula_ax form] [clf : CLformula agents form] := 
  clf.N
def M   {agents : Type} {form : Type} [pf : Pformula_ax form] [clf : CLformula agents form] := 
  clf.M
def S   {agents : Type} {form : Type} [pf : Pformula_ax form] [clf : CLformula agents form] := 
  clf.S
def Eq  {agents : Type} {form : Type} [pf : Pformula_ax form] [clf : CLformula agents form] := 
  clf.Eq

notation `['` G `]` : 80 φ := CLformula.eff G φ

----------------------------------------------------------
-- Epistemic Logic
----------------------------------------------------------

-- Individial Knowledge
class Kformula (agents : out_param Type) (form : Type) [pf : Pformula_ax form] :=
(knows : agents → form → form)
(K : ∀ φ ψ i, ⊢' ((knows i (φ →' ψ)) →' ((knows i φ) →' (knows i ψ))))
(T : ∀ φ i, ⊢' ((knows i φ) →' φ))
(Four : ∀ φ i, ⊢' ((knows i φ) →' (knows i (knows i φ))))
(Five : ∀ φ i, ⊢' ((¬' (knows i (φ))) →' (knows i (¬' (knows i φ)))))
(RN : ∀ φ i, ⊢' φ → ⊢' (knows i φ))

def K    {agents : Type} {form : Type} [pf : Pformula_ax form] [kf : Kformula agents form] := 
  kf.K
def T    {agents : Type} {form : Type} [pf : Pformula_ax form] [kf : Kformula agents form] := 
  kf.T
def Four {agents : Type} {form : Type} [pf : Pformula_ax form] [kf : Kformula agents form] := 
  kf.Four
def Five {agents : Type} {form : Type} [pf : Pformula_ax form] [kf : Kformula agents form] := 
  kf.Five
def RN   {agents : Type} {form : Type} [pf : Pformula_ax form] [kf : Kformula agents form] := 
  kf.RN

notation `K'` : 77         := Kformula.knows
notation `E'` : 77         := λ G φ, (finite_conjunction (list.map (λ i, K' i φ) (finset.to_list 
                                     (finite.to_finset (finite.of_fintype G)))))

-- Common Knowledge
class Cformula (agents : out_param Type) [hN : fintype agents] (form : Type) 
  [pf : Pformula_ax form] [kf : Kformula agents form] :=
(common_know : (set (agents)) → form → form)
(C : ∀ φ: form, ∀ G: set (agents), ⊢' ((common_know G φ) →' (E' G (φ ∧' (common_know G φ)))))
(RC : ∀ φ ψ : form, ∀ G : set (agents), ⊢' (ψ →' (E' G (φ ∧' ψ))) → ⊢' (ψ →' (common_know G φ)))

def C  {agents : Type} {form : Type} [hN : fintype agents] [pf : Pformula_ax form] 
  [kf : Kformula agents form] [cf : Cformula agents form] := cf.C
def RC {agents : Type} {form : Type} [hN : fintype agents] [pf : Pformula_ax form] 
  [kf : Kformula agents form] [cf : Cformula agents form] := cf.RC

notation `C'` : 77 := Cformula.common_know
