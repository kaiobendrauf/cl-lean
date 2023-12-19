/-
Authors: Kai Obendrauf
Adapted from the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley

This file contains proofs for a variety of propositional lemmas.
-/

import CLLean.Syntax.formula
import Mathlib.Tactic

open Logic

----------------------------------------------------------
-- Simple Rules
----------------------------------------------------------

lemma MP' {form : Type} [pf : Pformula_ax form] {φ ψ : form} 
-- ⊢ φ ⇒  ⊢ φ → ψ ⇒  ⊢ ψ 
  (hL : ⊢' φ) (hImp : ⊢' (φ →' ψ)) : ⊢' (ψ) := 
mp _ _ hImp hL

lemma cut {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} : 
-- ⊢ (φ → ψ) ⇒  ⊢ (ψ → χ) ⇒  ⊢ (φ → χ)
  ⊢' (φ →' ψ) → ⊢' (ψ →' χ) → ⊢' (φ →' χ) := 
λ h1 h2 => mp _ _ (mp _ _ (p2 _ ψ _) (mp _ _ (p1 _ _) h2)) h1

----------------------------------------------------------
-- SKI
----------------------------------------------------------
def combS {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} 
  (x : ⊢' (φ →' ψ →' χ)) (y : ⊢' (φ →' ψ))
  : ⊢' (φ →' χ) :=
mp _ _ (mp _ _ (p2 _ _ _) x) y

def combS2 {form : Type} [pf : Pformula_ax form] {φ ψ χ ω : form} 
  (x : ⊢' (φ →' ψ →' χ →' ω)) (y : ⊢' (φ →' ψ)) (z : ⊢' (φ →' χ))
  : ⊢' (φ →' ω) :=
combS (combS x y) z

def propS {φ ψ χ : Type} (x : φ → ψ → χ) (y : φ → ψ) : (φ → χ) := λ z => (x z) (y z)
def propS2 {φ ψ χ ω : Type} (x : φ → ψ → χ → ω) (y : φ → ψ) (z : φ → χ) : (φ → ω) := 
  λ w => (x w) (y w) (z w)

def combK {form : Type} [pf : Pformula_ax form] {φ ψ : form} (x : ⊢' φ) : ⊢' (ψ →' φ) :=
mp _ _ (p1 _ _) x

def propK {φ ψ : Type} (x : φ) : ψ → φ := λ _ => x

def combI {form : Type} [pf : Pformula_ax form] {φ : form} : ⊢' (φ →' φ) :=
mp _ _ (mp _ _ (p2 φ (φ →' φ) φ) (p1 _ _)) (p1 _ _)

def propI {φ : Type} : φ → φ :=
id

----------------------------------------------------------
-- Implication
----------------------------------------------------------
lemma iden {form : Type} [pf : Pformula_ax form] {φ : form} : 
-- ⊢ φ → φ 
  ⊢' (φ →' φ) := 
combI

lemma hs1 {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} : 
-- ⊢ (ψ → χ) → ((φ → ψ) → (φ → χ))
  ⊢' ((ψ →' χ) →' ((φ →' ψ) →' (φ →' χ))) :=
(mp _ _ (mp _ _ (p2 _ _ _) (mp _ _ (p1 _ _) (p2 _ _ _))) (p1 _ _))

lemma likemp {form : Type} [pf : Pformula_ax form] {φ ψ : form} : 
-- ⊢ φ → ((φ → ψ) → ψ)
  ⊢' (φ →' ((φ →' ψ) →' ψ)) :=
(mp _ _ (mp _ _ hs1 (mp _ _ (p2 _ _ _) iden)) (p1 _ _))

lemma imp_if_imp_imp {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} : 
-- ⊢ (φ → χ) ⇒  ⊢ φ → (ψ → χ)
  ⊢' (φ →' χ) → ⊢' (φ →' (ψ →' χ)) :=
λ h1 => mp _ _ (mp _ _ (p2 _ _ _) (mp _ _ (p1 _ _) (p1 _ _))) h1

lemma imp_switch {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} : 
-- ⊢ φ → (ψ → χ) ⇒  ⊢ ψ → (φ → χ)
  ⊢' (φ →' (ψ →' χ)) → ⊢' (ψ →' (φ →' χ)) :=
λ h1 => mp _ _ (mp _ _ (p2 _ _ _ ) (mp _ _ (p1 _ _) (mp _ _ (p2 _ _ _) h1))) (p1 _ _)

-- ⊢ (φ → (ψ → χ)) → (ψ → (φ → χ))
lemma l2 {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} : 
  ⊢' ((φ →' (ψ →' χ)) →' (ψ →' (φ →' χ))) :=
(mp _ _ (mp _ _ (p2 _ _ _) (cut (p2 _ _ _) hs1)) (mp _ _ (p1 _ _) (p1 _ _)))

-- ⊢ (φ → ψ) → ((ψ → χ) → (φ → χ))
lemma hs2 {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} : 
  ⊢' ((φ →' ψ) →' ((ψ →' χ) →' (φ →' χ))) :=
(mp _ _ l2 hs1)

-- ⊢ (φ → (φ → ψ)) → (φ → ψ)
lemma double_imp {form : Type} [pf : Pformula_ax form] {φ ψ : form} : 
  ⊢' ((φ →' (φ →' ψ)) →' (φ →' ψ)) :=
mp _ _ (p2 _ _ _) (imp_switch iden)

lemma imp_imp_iff_imp {form : Type} [pf : Pformula_ax form] {θ φ ψ : form} : 
-- ⊢ θ → (φ → (φ → ψ)) ⇔ ⊢ θ → (φ → ψ)
  ⊢' (θ →' (φ →' (φ →' ψ))) ↔ ⊢' (θ →' (φ →' ψ)) := by
  constructor
  · intro h1
    exact cut h1 double_imp
  · intro h1
    exact cut h1 (p1 _ _)

lemma imp_shift {form : Type} [pf : Pformula_ax form] {θ φ ψ χ : form} : 
-- ⊢ θ → (φ → (ψ → χ)) ⇔ ⊢ θ → (ψ → (φ → χ))
  ⊢' (θ →' (φ →' (ψ →' χ))) ↔ ⊢' (θ →' (ψ →' (φ →' χ))) := by
  constructor
  repeat
  · intro h1
    apply cut
    · exact h1
    · apply imp_switch (cut (p1 _ _ ) (imp_switch (p2 _ _ _)))


----------------------------------------------------------
-- Additional "Cuts"
----------------------------------------------------------

lemma cut1 {form : Type} [pf : Pformula_ax form] {φ ψ χ θ : form} : 
-- ⊢ θ → (φ → ψ) ⇒  ⊢ (ψ → χ) ⇒ ⊢ θ → (φ → χ)
  ⊢' (θ →' (φ →' ψ)) → ⊢' (ψ →' χ) → ⊢' (θ →' (φ →' χ)) :=
λ h1 h2 => cut h1 (mp _ _ (p2 _ _ _) (mp _ _ (p1 _ _ ) h2))

lemma cut2 {form : Type} [pf : Pformula_ax form] {φ ψ χ θ : form} : 
-- ⊢ (φ → ψ) ⇒  ⊢ θ → (ψ → χ) ⇒ ⊢ θ → (φ → χ)
  ⊢' (φ →' ψ) → ⊢' (θ →' (ψ →' χ)) → ⊢' (θ →' (φ →' χ)) :=
λ h1 h2 => imp_switch (cut h1 (imp_switch h2))


----------------------------------------------------------
-- Iff
----------------------------------------------------------
lemma iff_l {form : Type} [pf : Pformula_ax form] {φ ψ : form} : 
-- ⊢ φ ↔ ψ ⇒ ⊢ φ → ψ
  ⊢' (φ ↔' ψ) → ⊢' (φ →' ψ) := 
mp _ _ (p5 _ _)

lemma iff_r {form : Type} [pf : Pformula_ax form] {φ ψ : form} : 
-- ⊢ φ ↔ ψ ⇒ ⊢ ψ → φ
  ⊢' (φ ↔' ψ) → ⊢' (ψ →' φ) := 
mp _ _ (p6 _ _)

lemma iff_iden {form : Type} [pf : Pformula_ax form] {φ : form} : 
-- ⊢ φ ↔ φ 
  ⊢' (φ ↔' φ) := 
mp _ _ (mp _ _ (p4 _ _) iden) iden

-- Motivation: corresponds to Lean's `iff.intro`
lemma ax_iff_intro {form : Type} [pf : Pformula_ax form] {φ ψ : form}
  (h1 : ⊢' (φ →' ψ)) (h2 : ⊢' (ψ →' φ)) : ⊢' (φ ↔' ψ) := by
  apply MP' h2
  apply MP' h1
  exact p4 _ _

lemma iff_cut {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} : 
-- ⊢ φ ↔ ψ ⇒ ⊢ ψ ↔ χ ⇒ ⊢ φ ↔ χ
  ⊢' (φ ↔' ψ) → ⊢' (ψ ↔' χ) → ⊢' (φ ↔' χ)  := by
  intro h1 h2
  apply ax_iff_intro
  · apply cut
    exact iff_l h1
    exact iff_l h2
  · apply cut
    exact iff_r h2
    exact iff_r h1

/-- `φ` is provable iff `ψ` is, if it's provable `φ` and `ψ` are equivalent.

If we have the deduction theorem, the converse is also true: 
Pformulas are provably equivalent iff their provability is equivalent. -/
-- Motivation: allows rewriting after proving equivalence
lemma ax_iff_mp {form : Type} [pf : Pformula_ax form] {φ ψ : form} (hiff : ⊢' (φ ↔' ψ)) :
  ⊢' φ ↔ ⊢' ψ :=
⟨mp _ _ (iff_l hiff), mp _ _ (iff_r hiff)⟩


----------------------------------------------------------
-- Top and Bot
----------------------------------------------------------
lemma prtrue {form : Type} [pf : Pformula_ax form] : 
-- ⊢ ⊤
  ⊢' (⊤' : form) := iden

lemma pr_iff_true {form : Type} [pf : Pformula_ax form] {φ : form} 
    (h : ⊢' φ ) : 
-- ⊢ φ ⇒ ⊢ φ ↔ ⊤
  ⊢' φ ↔' ⊤' := ax_iff_intro (mp _ _ (p1 _ _) iden) (mp _ _ (p1 _ _) h)

----------------------------------------------------------
-- Negation
----------------------------------------------------------
lemma dne {form : Type} [pf : Pformula_ax form] {φ : form} : 
-- ⊢ ¬ ¬ φ → φ
  ⊢' ((¬' (¬' φ)) →' φ) :=
cut (cut (p1 _ _) (cut (p7 _ _) (p7 _ _))) (mp _ _ likemp (p1 φ φ))

lemma dni {form : Type} [pf : Pformula_ax form] {φ : form} : 
-- ⊢ φ → ¬ ¬ φ
  ⊢' (φ →' (¬' (¬' φ))) := 
mp _ _ (p7 _ _) dne

lemma nnn_bot {form : Type} [pf : Pformula_ax form] : 
-- ⊢ ¬ ¬ ¬ ⊤
  ⊢' (¬' (¬' (¬' ⊥')) : form) := 
mp _ _ dni prtrue

lemma iff_dne {form : Type} [pf : Pformula_ax form] {φ : form} : 
-- ⊢ ¬ ¬ φ ↔ φ
  ⊢' ((¬' (¬' φ)) ↔' φ) :=
mp _ _ (mp _ _ (p4 _ _) dne) dni

lemma iff_dni {form : Type} [pf : Pformula_ax form] {φ : form} : 
-- ⊢ φ ↔ ¬ ¬ φ
  ⊢' (φ ↔' (¬' (¬' φ))) :=
mp _ _ (mp _ _ (p4 _ _) dni) dne

lemma not_contra {form : Type} [pf : Pformula_ax form] {φ : form} : 
-- ⊢ ¬ (φ ∧ ¬ φ) 
  ⊢' (¬' (φ ∧' (¬' φ))) :=
mp _ _ (mp _ _ (p3 _ _) (cut dne (p6 _ _))) (cut dne (p5 _ _))

lemma not_contra_equiv_true {form : Type} [pf : Pformula_ax form] {φ : form} : 
-- ⊢ ¬ (φ ∧ ¬ φ) ↔' ¬ ⊥
  ⊢' ((¬' (φ ∧' (¬' φ))) ↔' (¬' ⊥') ) := by
  exact (mp _ _ (mp _ _ (p4 _ _) (mp _ _ (p1 _ _) iden)) (mp _ _ (p1 _ _) not_contra))

lemma not_and_subst {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} : 
-- ⊢ (φ ↔' ψ) ⇒ (⊢ ¬ (χ ∧ φ) ⇔ ⊢ ¬ (χ ∧ ψ))
  ⊢' (φ ↔' ψ) → (⊢' (¬' (χ ∧' φ)) ↔ ⊢' (¬' (χ ∧' ψ))) := by
  intro h1
  constructor
  · intro h2
    exact mp _ _ (mp _ _ (p3 _ _) (mp _ _ (p1 _ _) h2))
      (cut dne (mp _ _ double_imp (cut2
        (cut (p6 _ _) (mp _ _ (p6 _ _) h1))
        (cut (p5 _ _) (p4 _ _)))))
  · intro h2
    exact mp _ _ (mp _ _ (p3 _ _) (mp _ _ (p1 _ _) h2))
      (cut dne (mp _ _ double_imp (cut2
        (cut (p6 _ _) (mp _ _ (p5 _ _) h1))
        (cut (p5 _ _) (p4 _ _)))))

lemma contrapos {form : Type} [pf : Pformula_ax form] {φ ψ : form} : 
-- ⊢ ¬ ψ → ¬ φ ⇔ ⊢ φ → ψ
  ⊢' ((¬' ψ) →' (¬' φ)) ↔ ⊢' (φ →' ψ) := by
  constructor
  intro h1
  exact mp _ _ (p7 _ _) h1
  intro h1
  exact mp _ _ (cut (cut (mp _ _ hs1 dni) (mp _ _ hs2 dne)) (p7 _ _)) h1

lemma iff_not {form : Type} [pf : Pformula_ax form] {φ ψ : form} : 
-- ⊢ φ ↔' ψ ⇒ ⊢ ¬ φ ↔' ¬ ψ
  ⊢' (φ ↔' ψ) → ⊢' ((¬' ψ) ↔' (¬' φ)) := by
  intro h1
  have h2 : ⊢' (φ →' ψ):= mp _ _ (p5 _ _) h1
  have h3 : ⊢' (ψ →' φ):= mp _ _ (p6 _ _) h1
  rw [←contrapos] at h2
  rw [←contrapos] at h3
  exact (mp _ _ (mp _ _ (p4 _ _) h2) h3)

lemma contra_equiv_false {form : Type} [pf : Pformula_ax form] {φ : form} : 
-- ⊢ (φ ∧ ¬ φ) ↔' ⊥
  ⊢' ((φ ∧' (¬' φ)) ↔' ⊥') := by
  have h1 := iff_not (not_contra_equiv_true (φ := φ))
  exact (mp _ _ (mp _ _ (p4 _ _) (cut dni (cut (mp _ _ (p6 _ _) h1) dne))) 
    (cut dni (cut (mp _ _ (p5 _ _) h1) dne)))

lemma contra_imp_imp_false {form : Type} [pf : Pformula_ax form] {φ : form} : 
-- ⊢ ¬ φ → φ → ⊥
  ⊢' ((¬' φ) →' (φ →' ⊥')) := iden

lemma contra_not_imp_false_ax {form : Type} [pf : Pformula_ax form] {φ : form} : 
-- ⊢ ¬ φ → ⊥ ⇒ ⊢ φ
  ⊢' ((¬' (φ)) →' ⊥') → ⊢' φ := by
  intro h
  apply mp
  exact dne
  exact h

lemma contra_imp_false_not_ax {form : Type} [pf : Pformula_ax form] {φ : form} : 
-- ⊢  φ → ⊥ ⇒ ⊢ ¬ φ
  ⊢' (φ →' ⊥') → ⊢' (¬' (φ)) := by simp

lemma contra_imp_imp_false' {form : Type} [pf : Pformula_ax form] {φ : form} : 
-- ⊢ φ → ¬ φ → ⊥
  ⊢' ((φ) →' (¬' φ →' ⊥')) := dni

lemma contra_iff_false_ax_not {form : Type} [pf : Pformula_ax form] {φ : form} : 
-- ⊢ ¬ φ ↔ ⊢ φ → ⊥
  ⊢' (¬' φ) ↔ ⊢' (φ →' ⊥') := 
by simp

lemma by_contra_ax {form : Type} [pf : Pformula_ax form] {φ ψ : form} : 
-- ⊢ φ → ψ → ⊥ ⇒ ⊢ φ → ¬ ψ
 ⊢' (φ →' (ψ →' ⊥')) → ⊢' (φ →' (¬' ψ)) :=
by simp


----------------------------------------------------------
-- By contradiction
----------------------------------------------------------
@[simp] lemma explosion {form : Type} [pf : Pformula_ax form] {φ : form} : 
-- ⊢ ⊥ → φ 
  ⊢' (⊥' →' φ) := by
  apply contrapos.mp
  exact (mp _ _ (p1 _ _) iden)


@[simp] lemma contra_explosion {form : Type} [pf : Pformula_ax form] {φ ψ : form} : 
-- ⊢ φ → ¬ φ → ψ 
  ⊢' (φ →' (¬' φ) →' ψ) := by
  apply cut1
  exact contra_imp_imp_false'
  exact explosion

lemma ax_bot_imp {form : Type} [pf : Pformula_ax form] {φ : form} : 
-- ⊢ (⊤ → ⊥) ⇒ ⊢ (φ → ⊥) 
  ⊢' (⊤' →' ⊥' : form) → ⊢' (φ →' ⊥') := by
  intro hf
  apply mp
  apply mp
  apply p2
  exact ⊤'
  apply mp
  exact p1 _ _
  exact hf
  apply mp
  exact p1 _ _
  exact prtrue

/-- If there is any formula that cannot be proven, the theory is consistent. -/
-- Motivation: a lot of places assume `¬ ⊢ ⊥'` so it's worth trying to reduce these assumptions.
lemma consistent_of_not_ax {form : Type} [pf : Pformula_ax form] {φ : form}
  (hφ : ¬ ⊢' φ) : ¬ ⊢' (⊥' : form) :=
mt (mp _ _ explosion) hφ

----------------------------------------------------------
-- And
----------------------------------------------------------

-- Motivation: easier to prove Lean's `and` than in `ax`
lemma ax_and {form : Type} [pf : Pformula_ax form] {φ ψ : form} :
  ⊢' (φ ∧' ψ) ↔ ⊢' φ ∧ ⊢' ψ :=
⟨λ h => ⟨mp _ _ (p5 _ _) h, mp _ _ (p6 _ _) h⟩,
 λ ⟨h1, h2⟩ => mp _ _ (mp _ _ (p4 _ _) h1) h2⟩

@[simp] lemma ax_and_split {form : Type} [pf : Pformula_ax form] 
 {φ ψ : form} (hl : ⊢' φ ) (hr : ⊢' ψ) : ⊢' (φ ∧' ψ) :=
ax_and.mpr ⟨hl, hr⟩

lemma and_switch {form : Type} [pf : Pformula_ax form] {φ ψ : form} : 
-- ⊢ (φ ∧ ψ) ↔ (ψ ∧ φ)
  ⊢' ((φ ∧' ψ) ↔' (ψ ∧' φ)) := by
  exact (mp _ _ (mp _ _ (p4 _ _) (mp _ _ double_imp (cut (p5 _ _) 
    (imp_switch (cut (p6 _ _) (p4 _ _)))))) 
    (mp _ _ double_imp (cut (p5 _ _) (imp_switch (cut (p6 _ _) (p4 _ _))))))

lemma left_and_imp {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} : 
-- ⊢ ψ → ((φ ∧ ψ) → χ ) ⇒ ⊢ (φ ∧ ψ) → χ
  ⊢' (ψ →' ((φ ∧' ψ) →' χ)) → ⊢' ((φ ∧' ψ) →' χ) :=
λ h1 => mp _ _ double_imp (cut (p6 _ _) h1)

lemma and_right_imp {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} : 
-- ⊢ (φ ∧ ψ) → χ  ⇔ ⊢  ψ → (φ → χ)
  ⊢' ((φ ∧' ψ) →' χ) ↔ ⊢' (ψ →' (φ →' χ)) := by
  constructor
  · intro h1
    exact mp _ _ (cut2 (p1 _ _) (p2 _ _ _)) (cut1 (p4 _ _) h1)
  · intro h1
    exact left_and_imp (cut2 (p5 _ _) h1)

lemma phi_and_true {form : Type} [pf : Pformula_ax form] {φ : form} : 
-- ⊢  (φ ∧ ⊤) ↔' φ 
  ⊢' ((φ ∧' (¬' ⊥')) ↔' φ) :=
  (mp _ _ (mp _ _ (p4 _ _) (p5 _ _)) (mp _ _ (imp_switch (p4 _ _)) iden))

lemma true_and_phi {form : Type} [pf : Pformula_ax form] {φ : form} : 
-- ⊢  (⊤ ∧ φ) ↔ φ 
  ⊢' (((¬' ⊥') ∧' φ) ↔' φ) := by
  exact mp _ _
    (mp _ _ (p4 _ _) (cut (iff_l and_switch) (iff_l phi_and_true)))
    (mp _ _ (p4 _ _) iden)

lemma imp_and_and_imp {form : Type} [pf : Pformula_ax form] {φ ψ χ θ : form} : 
-- ⊢ (φ → ψ) ∧ (χ → θ)⇒ ⊢ (φ ∧ χ) → (ψ ∧ θ)
  ⊢' (((φ →' ψ) ∧' (χ →' θ))) → ⊢' (((φ ∧' χ) →' (ψ ∧' θ))) := by
  intro h
  exact (mp _ _ double_imp (cut (cut (p5 _ _) (mp _ _ (p5 _ _) h)) 
    (cut2 (cut (p6 _ _) (mp _ _ (p6 _ _) h)) (p4 _ _))))

lemma imp_and_and_and_imp {form : Type} [pf : Pformula_ax form] {a b c d e f : form} : 
-- ⊢ (φ → ψ →) ∧ (χ → θ)⇒ ⊢ (φ ∧ χ) → (ψ ∧ θ) → (φ ∧ χ)
  ⊢' (((a →' b →' c) ∧' (d →' e →' f))) → ⊢' (((a ∧' d) →' (b ∧' e) →' (c ∧' f))) := by
  intro h
  apply cut (imp_and_and_imp h)
  apply mp
  apply double_imp
  apply cut2 (p5 _ _)
  apply cut (p6 _ _)
  apply imp_shift.mp
  apply imp_switch
  apply mp
  apply double_imp
  apply cut2 (p5 _ _)
  apply cut (p6 _ _)
  apply imp_shift.mp
  apply cut1
  apply likemp
  apply imp_switch
  apply imp_shift.mp
  apply cut1
  apply likemp
  exact p4 _ _

lemma and_switch_ax {form : Type} [pf : Pformula_ax form] {φ ψ : form} : 
-- ⊢ (φ ∧ ψ) ⇔ ⊢ (ψ ∧ φ)
  (⊢' (φ ∧' ψ)) ↔ (⊢' (ψ ∧' φ)) := by
  constructor
  repeat
  · exact λ h => mp _ _ (mp _ _ (p5 _ _) and_switch) h

lemma and_commute {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} : 
-- ⊢ ((φ ∧ ψ) ∧ χ) ↔' (φ ∧ (ψ ∧ χ))
  ⊢' (((φ ∧' ψ) ∧' χ) ↔' (φ ∧' (ψ ∧' χ))) := by
  exact mp _ _ (mp _ _ (p4 _ _) (mp _ _ double_imp (imp_imp_iff_imp.mp 
    (cut (cut (p5 _ _) (p6 _ _)) (cut2 (p6 _ _) (cut1 (p4 _ _) 
      (imp_switch (cut (cut (p5 _ _) (p5 _ _)) (p4 _ _))))))))) 
    (mp _ _ double_imp (imp_imp_iff_imp.mp (cut (cut (p6 _ _) (p5 _ _)) 
    (imp_switch (cut (p5 _ _) (cut1 (p4 _ _) (cut2 (cut (p6 _ _) (p6 _ _)) (p4 _ _))))))))

lemma imp_and_imp {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} : 
-- ⊢ φ → ψ ⇒ ⊢ (χ ∧ φ) → (χ ∧ ψ)
  ⊢' (φ →' ψ) → ⊢' ((χ ∧' φ) →' (χ ∧' ψ)) := by
  intro h1
  exact imp_and_and_imp (mp _ _ (mp _ _ (p4 _ _) iden) h1)

lemma and_iden {form : Type} [pf : Pformula_ax form] {φ : form} : 
-- ⊢ φ → (φ ∧ φ) 
  ⊢' (φ →' (φ ∧' φ)) := by
  have hdi : ⊢' ((φ →' (φ →' (φ ∧' φ))) →' (φ →' (φ ∧' φ))):= double_imp
  apply mp _ _ hdi
  exact (p4 _ _)

lemma imp_and_iden {form : Type} [pf : Pformula_ax form] {φ ψ : form} : 
-- ⊢ φ → ψ ⇒ ⊢ φ → (φ ∧ ψ)
  ⊢' (φ →' ψ) → ⊢' (φ →' (φ ∧' ψ)) := by
  intro h
  have hab : ⊢' (φ →' (φ ∧' φ)):= and_iden
  have hbc : ⊢' ((φ ∧' φ) →' (φ ∧' ψ)):= imp_and_imp h
  exact cut hab hbc


lemma imp_imp_and {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} : 
-- ⊢ (φ → ψ) ⇒ ⊢ (φ → χ) ⇒ ⊢ φ → (ψ ∧ χ)
  ⊢' (φ →' ψ) → ⊢' (φ →' χ) → ⊢' (φ →' (ψ ∧' χ)) := by
  intro h1 h2
  apply cut
  · exact and_iden
  · apply imp_and_and_imp
    apply ax_and.mpr
    constructor
    · exact h1
    · exact h2

lemma imp_and_r {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} : 
-- ⊢ (φ → ψ) ⇒ ⊢ (χ ∧ φ) → ψ
  ⊢' (φ →' ψ) → ⊢' ((χ ∧' φ) →' ψ) := by
  intro h
  apply cut
  exact p6 _ _
  exact h

lemma imp_and_l {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} : 
-- ⊢ (φ → ψ) ⇒ ⊢ (φ ∧ χ) → ψ
  ⊢' (φ →' ψ) → ⊢' ((φ ∧' χ) →' ψ) := by
  intro h
  apply cut
  exact p5 _ _
  exact h

lemma iff_and_top {form : Type} [pf : Pformula_ax form] {φ ψ : form} : 
-- ⊢ (φ ∧ ⊤) → ψ ⇔ ⊢ (φ → ψ) 
  ⊢' ((φ ∧' ⊤') →' ψ) ↔ ⊢' (φ →' ψ) := by
  split
  { intro h
    apply cut
    { exact mp _ _ (p6 _ _ ) phi_and_true, }
    { exact h,} }
  { intro h
    apply cut
    apply p5
    exact h, }

lemma remove_and_imp {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} : 
-- ⊢ (φ ∧ φ ∧ ψ) → χ ⇒ ⊢ (φ ∧ ψ) → χ
  ⊢' ((φ ∧' (φ ∧' (ψ))) →' χ) → ⊢' ((φ ∧' (ψ)) →' χ) := by
  intro h
  apply cut
  { exact imp_imp_and (p5 _ _) (iden), }
  { exact h, }

lemma imp_and {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} :
-- ⊢ (φ → (ψ ∧ χ)) → (φ → ψ)
  ⊢' ((φ →' (ψ ∧' χ)) →' (φ →' ψ)) := by
  apply mp
  apply p2
  apply mp
  apply p1
  apply p5

lemma and_cut_l {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} :
-- ⊢ ((φ ↔ χ) ⇒ ⊢ ((φ ∧ ψ) ↔ (χ ∧ ψ))
  ⊢' (φ ↔' χ) → ⊢' ((φ ∧' ψ) ↔' (χ ∧' ψ)) := by
  intro hl
  refine ax_iff_intro _ _
  { apply imp_imp_and
    { apply cut
      apply p5
      apply iff_l
      exact hl, }
    { exact p6 _ _, }, }
  { apply imp_imp_and
    { apply cut
      apply p5
      apply iff_r
      exact hl, }
    { exact p6 _ _, }, }

lemma and_cut_r {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} :
-- ⊢ ((ψ ↔ χ) ⇒ ⊢ ((φ ∧ ψ) ↔ (φ ∧ χ))
  ⊢' (ψ ↔' χ) → ⊢' ((φ ∧' ψ) ↔' (φ ∧' χ)) := by
  intro hr
  refine ax_iff_intro _ _
  { apply imp_imp_and
    { exact p5 _ _, }
    { apply cut
      apply p6
      apply iff_l
      exact hr, }, }
  { apply imp_imp_and
    { exact p5 _ _, }
    { apply cut
      apply p6
      apply iff_r
      exact hr, }, }

-- Motivation: for simplication in combination with `ax_iff_mp`
@[simp] lemma ax_and_top_iff {form : Type} [pf : Pformula_ax form] {φ : form} :
  ⊢' ((φ ∧' ⊤') ↔' φ) :=
by simpa using @phi_and_true _ _ φ

----------------------------------------------------------
-- Simplification Rules
----------------------------------------------------------

-- Motivation: corresponds more or less to Lean's `imp_congr`
@[simp] lemma ax_imp_congr_left {form : Type} [pf : Pformula_ax form] {φ φ' ψ : form}
  (hl : ⊢' (φ ↔' φ')) : ⊢' ((φ →' ψ) ↔' (φ' →' ψ)) :=
ax_iff_intro
  (mp _ _ (imp_switch hs1) (iff_r hl))
  (mp _ _ (imp_switch hs1) (iff_l hl))

-- Motivation: for simplication in combination with `ax_iff_mp`
@[simp] lemma ax_top_imp_iff {form : Type} [pf : Pformula_ax form] (φ : form) :
  ⊢' ((⊤' →' φ) ↔' φ) :=
ax_iff_intro
  (combS combI (combK prtrue)) -- λ h, h prtrue
  (p1 _ _)

    -- Motivation: for simplication in combination with `ax_iff_mp`
@[simp] lemma ax_not_bot_imp_iff {form : Type} [pf : Pformula_ax form] (φ : form) :
  ⊢' (((¬' ⊥' ) →' φ) ↔' φ) :=
ax_top_imp_iff φ

-- Motivation: useful simplification lemma
@[simp] lemma ax_top_imp {form : Type} [pf : Pformula_ax form] {φ : form} :
  ⊢' (⊤' →' φ) ↔ ⊢' φ := 
ax_iff_mp (ax_top_imp_iff φ)

@[simp] lemma ax_not_bot_imp {form : Type} [pf : Pformula_ax form] {φ : form} :
  ⊢' ((¬' ⊥' ) →' φ) ↔ ⊢' φ := ax_top_imp


----------------------------------------------------------
-- Demorgans 
----------------------------------------------------------
lemma demorgans {form : Type} [pf : Pformula_ax form] {φ ψ : form} : 
-- ⊢ ¬ (φ ∧ ψ) ⇔ ⊢ φ → ¬ ψ
  ⊢' (¬' (φ ∧' ψ)) ↔ ⊢' (φ →' (¬' ψ)) := by
  split
  { intro h1
    apply and_right_imp.mp
    apply cut
    { exact mp _ _ (p5 _ _) and_switch, }
    { exact h1, }, }
  { intro h1
    apply (mp _ _ (contrapos.mpr (mp _ _ (p5 _ _) and_switch)))
    exact(and_right_imp.mpr h1), }

lemma demorgans' {form : Type} [pf : Pformula_ax form] {φ ψ : form} : 
-- ⊢ (¬ φ → ψ) → ¬ (¬ φ ∧ ¬ ψ)
  ⊢' (((¬' φ) →' ψ) →' ¬' (¬' φ ∧' ¬' ψ)) :=
combS2 (combK (p2 _ _ _)) (combK (combS (combK (p6 _ _)) combI)) 
  (combS2 (combK (p2 _ _ _)) (combS (combK (p1 _ _)) combI) (combK (combS (combK (p5 _ _)) combI)))


lemma demorgans'' {form : Type} [pf : Pformula_ax form] {φ ψ : form} : 
  ⊢' (¬' (φ →' ¬' ψ) →' φ ∧' ψ) := by
  rw ←contrapos
  apply cut _ dni
  apply imp_switch
  rw imp_shift
  apply cut1
  apply p4
  exact likemp

lemma demorgans''' {form : Type} [pf : Pformula_ax form] {φ ψ : form} : 
  ⊢' (¬' (φ ∧' ψ) ↔' (φ →' (¬' ψ))) := by
  apply ax_iff_intro
  { refine and_right_imp.mp _
    refine by_contra_ax _
    refine and_right_imp.mp _
    apply cut
    apply iff_r
    apply and_commute
    refine and_right_imp.mpr _
    refine imp_switch _
    apply cut
    apply iff_l
    apply and_switch
    exact contra_explosion, }
  { refine contrapos.mp _
    apply cut
    apply dne
    apply cut
    apply iff_l
    apply and_switch
    refine and_right_imp.mpr _
    apply imp_shift.mpr
    exact likemp, }

lemma demorgans'''' {form : Type} [pf : Pformula_ax form] {φ ψ : form} : 
  ⊢' (¬' (φ →' ψ) ↔' (φ ∧' ¬' ψ)) := by
  apply ax_iff_intro
  { apply contrapos.mp
    apply cut (iff_l demorgans''')
    apply @cut _ _ _ (φ →' ψ)
    refine imp_switch _
    apply cut1
    exact likemp
    exact dne
    exact dni, }
  { apply @cut _ _ _ ((φ→' ψ) →' ⊥')
    { apply imp_switch
      refine imp_imp_iff_imp.mp _
      apply imp_switch
      apply cut (p5 _ _)
      apply cut1 likemp
      apply cut2 (p6 _ _)
      exact contra_explosion, }
    { exact iden, }, }

----------------------------------------------------------
-- Or
----------------------------------------------------------
lemma or_cases {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} : 
-- ⊢ (φ → χ) ⇒  ⊢ (ψ → χ) ⇒ ⊢ (¬ φ → ψ) → χ 
  ⊢' (φ →' χ) → ⊢' (ψ →' χ) → ⊢' ((¬' φ →' ψ) →' χ) := by
  intro h1 h2
  have h1' := contrapos.mpr h1
  have h2' := contrapos.mpr h2
  have h3 := imp_imp_and h1' h2'
  rw ←contrapos
  apply by_contra_ax
  apply cut h3
  apply @cut _ _ _ (¬' (¬' φ →' ψ)) _
  { refine contrapos.mp _
    apply cut
    apply dne
    exact demorgans', }
  exact contra_imp_imp_false

lemma or_inl {form : Type} [pf : Pformula_ax form] {φ ψ : form} : 
--  ⇒  ⊢ (φ) → (¬ φ → ψ)
  ⊢' ((φ) →' ((¬' φ) →' ψ)) := by
  apply cut1
  exact contra_imp_imp_false'
  exact explosion

lemma or_inr {form : Type} [pf : Pformula_ax form] {φ ψ : form} : 
--  ⇒  ⊢ (φ) → ⊢ (¬ φ → χ)
  ⊢' ((ψ) →' ((¬' φ) →' ψ)) := p1 ψ (¬' φ)

lemma disjunct_rw_iff {form : Type} [pf : Pformula_ax form] {φ ψ : form} : 
  ⊢' (((¬' φ) →' ψ) ↔' (finite_disjunction (φ :: [ψ]))) := by
  apply ax_iff_intro
  { simp [finite_disjunction]
    apply imp_switch
    apply cut1
    exact likemp
    exact contra_explosion, }
  { simp [finite_disjunction]
    apply imp_switch
    apply cut1
    exact likemp
    apply @cut _ _ _ (¬' (¬' ψ))
    exact iden
    exact dne, }

lemma or_switch {form : Type} [pf : Pformula_ax form] {φ ψ : form} :
  ⊢' ((¬' φ →' ψ) ↔' (¬' ψ →' φ)) := by
  refine ax_iff_intro _ _
  repeat 
  { apply or_cases
    exact p1 _ _
    exact or_inl, }

-- ⊢ ((φ ↔ z) ⇒ ⊢ ((φ ∨ y) ↔ (z ∨ y))
lemma or_cut_l {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} (hl : ⊢' (φ ↔' χ)) :
  ⊢' ((¬' φ →' ψ) ↔' (¬' χ →' ψ)) := by
  refine ax_iff_intro _ _
  { apply or_cases
    { apply cut
      apply iff_l hl
      exact or_inl, }
    { exact p1 _ _, }, }
  { apply or_cases
    { apply cut
      apply iff_r hl
      exact or_inl, }
    { exact p1 _ _, }, }

-- ⊢ ((ψ ↔ z) ⇒ ⊢ ((φ ∨ y) ↔ (φ ∨ z))
lemma or_cut_r {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} (hr : ⊢' (ψ ↔' χ)) :
  ⊢' ((¬' φ →' ψ) ↔' (¬' φ →' χ)) := by
  apply iff_cut
  exact or_switch
  apply iff_cut
  exact or_cut_l hr
  exact or_switch

-- ⊢ ((φ ∧ ψ) ∨ (φ ∧ χ)) ↔ (φ ∧ (ψ ∨ χ))
lemma distr_or_and {form : Type} [pf : Pformula_ax form] {φ ψ χ : form} :
  ⊢' (((¬' (φ ∧' ψ)) →' (φ ∧' χ)) ↔' (φ ∧' ((¬' ψ) →' χ))) := by
  apply ax_iff_intro
  { apply or_cases
    { apply imp_and_imp
      exact contra_explosion, }
    { apply imp_and_imp
      exact p1 _ _, }, }
  { apply and_right_imp.mpr
    refine imp_shift.mp _
    apply imp_switch
    apply cut
    apply iff_l
    apply demorgans'''
    apply imp_shift.mp
    refine imp_imp_iff_imp.mp _
    apply imp_switch
    apply cut1
    exact likemp
    apply imp_switch
    apply imp_shift.mp
    apply imp_switch
    apply imp_shift.mp
    apply imp_switch
    apply cut1
    exact likemp
    apply imp_switch
    exact p4 _ _, }



----------------------------------------------------------
-- Finite Conjunction
----------------------------------------------------------
-- empty conjunction = ⊤
@[simp] lemma finite_conjunction_nil {form : Type} [pf : Pformula_ax form] :
  finite_conjunction ([] : List form) = ⊤' := rfl

--  finite_conjunction (φ :: φs) = φ ∧ (finite_conjunction φs)
@[simp] lemma finite_conjunction_cons {form : Type} [pf : Pformula_ax form] 
  (φ : form) (φs : List form) : finite_conjunction (φ :: φs) = φ ∧' finite_conjunction φs := rfl

lemma fin_conj_simp {form : Type} [pf : Pformula_ax form] (φ : form) : 
-- ⊢ ¬ finite_conjunction [φ, ¬ φ]
  ⊢' (¬' (finite_conjunction ([φ, ¬' φ]))) := by
  simp [finite_conjunction]
  rw not_and_subst
  exact not_contra
  exact phi_and_true

lemma imp_conj_imp_imp {form : Type} [pf : Pformula_ax form] 
  {φ ψ : form} {φs : List (form)} :
--  ⊢ finite_conjunction (φ :: φs) → ψ ⇔  ⊢ (finite_conjunction φs) → (φ → ψ)
  ⊢' ((finite_conjunction (φ :: φs)) →' ψ) ↔  ⊢' ((finite_conjunction φs) →' (φ →' ψ)) := by
  split
  { intro h
    simp at h
    exact and_right_imp.mp h, }
  { intro h
    simp
    exact and_right_imp.mpr h, }

lemma fin_conj_s_imp {form : Type} [pf : Pformula_ax form] 
  {φ ψ : form } {φs : List form} :
--  ⊢ finite_conjunction (φ :: φs) → (φ → ψ) ⇒  ⊢ (finite_conjunction φs) → (φ → ψ)
  ⊢' ((finite_conjunction (φ :: φs)) →' (φ →' ψ)) →  ⊢' ((finite_conjunction φs) →' (φ →' ψ)) :=
λ h, imp_imp_iff_imp.mp (imp_conj_imp_imp.mp h)


lemma fin_conj_append {form : Type} [pf : Pformula_ax form] {φs φs' : List (form)} :
--  ⊢ finite_conjunction φs' ∧ finite_conjunction φs ↔ finite_conjunction (φs' ++ φs)
  ⊢' (((finite_conjunction φs') ∧' (finite_conjunction φs)) ↔' (finite_conjunction (φs' ++ φs))) := by
  induction φs', rw finite_conjunction
  exact (mp _ _ (mp _ _ (p4 _ _) (cut (mp _ _ (p6 _ _) and_switch) (mp _ _ (p5 _ _) phi_and_true)))
    (cut (mp _ _ (p6 _ _) phi_and_true) (mp _ _ (p5 _ _) and_switch)))
  exact mp _ _ (mp _ _ (p4 _ _) (cut (mp _ _ (p5 _ _) and_commute) 
    (imp_and_imp (mp _ _ (p5 _ _) φs'_ih))))
    (cut iden (cut (imp_and_imp (mp _ _ (p6 _ _) φs'_ih)) (mp _ _ (p6 _ _) and_commute)))

lemma fin_conj_repeat {form : Type} [pf : Pformula_ax form] 
  {φ : form} {φs : List form} :
-- ⊢ φ → finite_conjunction [φ, φ, ...]
  (∀ ψ ∈ φs, ψ = φ) →  ⊢' (φ →' (finite_conjunction φs)) := by
  intro h1, induction φs
  simp[finite_conjunction]
  exact mp _ _ (p1 _ _) prtrue
  rw finite_conjunction, simp at *
  cases h1 with h1 h2
  subst h1
  exact cut (mp _ _ double_imp (p4 _ _)) 
    (imp_and_and_imp (mp _ _ (mp _ _ (p4 _ _) iden) (φs_ih h2)))

lemma neg_fin_conj_repeat {form : Type} [pf : Pformula_ax form] 
  {φ : form} {φs : List form} (hnpr : ¬ ( ⊢' (⊥' : form))) :
-- ⊢ [¬φ, ¬φ, ...] ⇒ ⊢ φ
  (∀ ψ ∈ φs, ψ = ¬' φ) →  ⊢' (¬' (finite_conjunction φs)) →  ⊢' φ := by
  intro h1 h2, induction φs
  simp[finite_conjunction] at h2
  have hbot : ⊢' ⊥'
  { apply mp _ _ dne
    simp
    exact h2, }
  exact absurd hbot (hnpr)
  repeat {rw fin_conj at *}, simp at *
  cases h1 with h1 h3
  have h5 := contrapos.mpr (fin_conj_repeat h3)
  subst h1
  apply mp _ _ (mp _ _ (p3 _ _) (contrapos.mpr (cut h5 dne)))
  have h6 := iff_not and_switch
  apply contrapos.mpr (cut ((demorgans.mp) (mp _ _ (mp _ _ (p6 _ _) (h6)) h2)) dne)

lemma finite_conj_forall_iff {form : Type} [pf : Pformula_ax form] 
  {φs : List form} : (∀ φ ∈ φs, ⊢' φ) ↔ ⊢' (finite_conjunction φs) := by
  induction φs
  { simp [finite_conjunction], }
  { unfold finite_conjunction
    split
    { intro h
      rw ax_and
      split
      { apply h
        simp }
      { apply φs_ih.mp
        intro x hx
        apply h
        simp only [hx, List.mem_cons_iff, or_true], }, }
    { intro h x hx
      cases hx
      { simp only [hx, eq_self_iff_true, ax_and] at *
        exact h.left, }
      { rw ax_and at h
        apply φs_ih.mpr h.right
        exact hx, }, }, }

lemma finite_conj_forall_imp {form : Type} [pf : Pformula_ax form] {φs : List form} : 
  (∀ x ∈ φs, ⊢' ((finite_conjunction φs) →' x)) := by
  induction φs
  { simp only [List.not_mem_nil, forall_false_left, implies_true_iff], }
  { intro x hx
    unfold finite_conjunction
    cases hx
    { simp [hx] at *
      exact p5 _ _, }
    { apply cut
      { apply iff_l
        exact and_switch, }
      { refine imp_and_l _
        exact φs_ih x hx, }, }, }

lemma finite_conj_imp {form : Type} [pf : Pformula_ax form] {φs : List form} 
  {φ : form} (h : φ ∈ φs) : 
  ⊢' ((finite_conjunction φs) →' φ) := finite_conj_forall_imp φ h

lemma noin_imp_nfin_con {form : Type} [pf : Pformula_ax form] {φs : List form} 
  {φ : form} (h : φ ∈ φs) : 
  ⊢' ((¬' φ) →' ¬' (finite_conjunction φs)) := contrapos.mpr (finite_conj_imp h)

lemma demorans_fin_con {form : Type} [pf : Pformula_ax form] 
  {φs : List (form)} :
  ⊢' ((¬' (finite_conjunction φs)) ↔' ((finite_disjunction (List.map (¬') φs)))) := by
  induction φs with φ φs ih
  { apply ax_iff_intro
    apply dne
    apply dni, }
  { simp only [finite_disjunction, finite_conjunction]
    apply iff_cut demorgans'''
    apply ax_iff_intro
    { apply cut2 dne
      apply imp_switch
      apply cut1 likemp
      exact iff_l ih, }
    { apply cut2 dni
      apply imp_switch
      apply cut1 likemp
      exact iff_r ih, }, }

lemma contra_con_cons {form : Type} [pf : Pformula_ax form] 
  {fs gs : List (form)} {x y : form} (hax : ⊢' (y ↔' ¬' x)) (hx : x ∈ fs) (hy : y ∈ gs) :
  ⊢' (¬' ((finite_conjunction fs) ∧' (finite_conjunction gs))) := by
  induction' fs with f fs ihf
  { finish, }
  { induction gs with g gs ihg
    { finish, }
    { cases hx
      { cases hy
        { rw[←hx, ←hy]
          simp[finite_conjunction]
          apply cut (iff_r and_commute)
          apply imp_and_l
          apply cut (iff_l and_switch)
          apply cut (iff_r and_commute)
          apply imp_and_l
          rw ←contra_iff_false_ax_not
          rw demorgans
          apply iff_l
          exact hax, }
        { simp[finite_conjunction]
          apply cut (iff_r and_commute)
          apply cut (iff_l and_switch)
          apply cut (iff_r and_commute)
          apply imp_and_l
          apply cut (iff_l and_switch)
          rw ←contra_iff_false_ax_not
          apply ihg hy, }, }
      { apply cut (iff_l and_switch)
        apply cut (iff_r and_commute)
        apply cut (iff_l and_switch)
        apply cut (iff_r and_commute)
        apply imp_and_l
        specialize @ihf pf (g :: gs) x y hax hy hx
        exact ihf, }, }, }

----------------------------------------------------------
-- Finite Disjunction
----------------------------------------------------------
lemma ax_disjunct_rw_iff {form : Type} [pf : Pformula_ax form] {φ ψ : form} : 
  ⊢' ((¬' φ) →' ψ) ↔ ⊢' (finite_disjunction [φ, ψ]) := by
  refine ax_iff_mp _
  exact disjunct_rw_iff

lemma imp_finite_disjunction {form : Type} [pf : Pformula_ax form] 
  (ψ : form) (φs : List (form)) (h : ψ ∈ φs) :
  ⊢' (ψ →' finite_disjunction φs) := by
  induction φs with φ φs ih
  { by_contradiction, simp at *, exact h, }
  { simp [finite_disjunction] at *
    cases em (φ = ψ) with hf hf
    { rw hf at *
      rw ←and_right_imp
      apply cut
      { exact mp _ _ (p5 _ _) and_switch, }
      { apply cut
        { exact not_contra, }
        { exact explosion, }, }, }
    { cases h
    { exact false.rec _ (hf (eq.symm h)), }
    { exact imp_if_imp_imp (ih h), }, }, }

lemma imp_finite_disjunction_subset {form : Type} [pf : Pformula_ax form] 
  {φs φs': List (form)} (hsubset : φs ⊆ φs')  :
  ⊢' (finite_disjunction φs →' finite_disjunction φs')  := by
  induction φs with φ φs ih
  { simp[finite_disjunction], }
  { simp [finite_disjunction] at *
    cases hsubset with hφ hsubset
    specialize ih hsubset
    have hφs' := imp_finite_disjunction φ φs' hφ
    apply or_cases
    exact hφs'
    exact ih, }

lemma disjunct_of_disjuncts {form : Type} [pf : Pformula_ax form] (φs φs': List (form)) : 
  ⊢' ((finite_disjunction [(finite_disjunction φs), (finite_disjunction φs')]) ↔' 
      (finite_disjunction (φs ++ φs') )) := by
  apply ax_and.mpr
  split
  { rw finite_disjunction
    apply or_cases
    { apply imp_finite_disjunction_subset
      simp, }
    { simp [finite_disjunction]
      have hdne := @dne _ _ (finite_disjunction φs') 
      apply cut
      apply hdne
      apply imp_finite_disjunction_subset
      simp, }, }
  { induction' φs
    { simp [finite_disjunction] at *
      apply cut1
      apply p1
      apply dni, }
    { specialize @ih pf
      apply or_cases
      { rw finite_disjunction
        simp
        apply cut
        apply @imp_finite_disjunction form pf _ (hd :: φs)
        exact Set.mem_insert hd (λ (hd : form), List.mem hd φs)
        apply cut1
        apply contra_imp_imp_false'
        apply explosion, }
      { apply cut
        apply ih
        apply or_cases
        { apply @cut1 _ _ _ (⊥')
          apply cut
          apply @imp_finite_disjunction_subset form pf _ (hd :: φs)
          simp
          apply contra_imp_imp_false'
          apply explosion, }
        { unfold finite_disjunction
          apply p1, }, }, }, }

lemma disjunc_disjunct {form : Type} [pf : Pformula_ax form] 
  {φs φs' : List (form)} :
  ⊢' ((¬' (finite_disjunction φs) →' finite_disjunction φs')  
    →' finite_disjunction (φs ++ φs'))  := by
  apply or_cases
  apply imp_finite_disjunction_subset
  simp
  apply imp_finite_disjunction_subset
  simp

lemma ax_iff_disjunc_disjunct {form : Type} [pf : Pformula_ax form] 
  {φs φs' : List (form)} :
  ⊢' (¬' (finite_disjunction φs) →' finite_disjunction φs')↔ ⊢' (finite_disjunction (φs ++ φs')) := by
  split
  { intro h
    apply MP' h
    apply disjunc_disjunct, }
  { intro h
    rw ax_disjunct_rw_iff
    apply MP' h
    apply iff_r
    apply disjunct_of_disjuncts, }

lemma iff_disjunc_disjunct {form : Type} [pf : Pformula_ax form] 
  {φs φs' : List (form)} :
  ⊢' ((¬' (finite_disjunction φs) →' finite_disjunction φs')↔' (finite_disjunction (φs ++ φs'))) := by
  apply ax_iff_intro
  { apply disjunc_disjunct, }
  { apply cut
    apply iff_r
    apply disjunct_of_disjuncts
    apply iff_r
    exact disjunct_rw_iff, }

lemma demorans_fin_dis {form : Type} [pf : Pformula_ax form] 
  {φs : List (form)} :
  ⊢' ((¬' (finite_disjunction φs)) ↔' ((finite_conjunction (List.map (¬') φs)))) := by
  induction φs with φ φs ih
  { simp [finite_disjunction, finite_conjunction], }
  { simp only [finite_disjunction, finite_conjunction]
    apply iff_cut demorgans''''
    apply ax_iff_intro
    { apply imp_and_and_imp
      apply ax_and.mpr
      exact and.intro iden (iff_l ih), }
    { apply imp_and_and_imp
      apply ax_and.mpr
      exact and.intro iden (iff_r ih), }, }
