/-
Authors: Kai Obrauf
Following the paper "A Modal Logic for Coalitional Power in Games" by Mark Pauly

This file defines a canonical model for CL.
First we define the states in the model, then the effectivity structure.
Given these we prove semi playability and regularity, which suffices to prove playability.
-/

import CLLean.Syntax.consistency
import CLLean.Syntax.CLLemmas
import CLLean.Semantics.model
import Mathlib.Tactic

-- local instance classical.prop_decidable


open Set List Logic Classical

----------------------------------------------------------
-- Set Helper Functions
----------------------------------------------------------
lemma union_neq_univ_left {α : Type} {A B : Set α} (h : A ∪ B ⊂ univ) :
  A ≠ univ :=
ne_of_ssubset (ssubset_of_subset_of_ssubset (subset_union_left A B) h)

lemma union_neq_univ_right {α : Type} {A B : Set α} (h : A ∪ B ⊂ univ) :
  B ≠ univ :=
ne_of_ssubset (ssubset_of_subset_of_ssubset (subset_union_right A B) h)


----------------------------------------------------------
-- Canonical Frame Defintions and Lemmas
----------------------------------------------------------
namespace canonical

-- Define States
----------------------------------------------------------
-- S is the Set of all maximal CL-consistent Set of formulas
def states (form : Type) [Pformula_ax form] :=
{Γ : (Set (form)) // (max_ax_consistent Γ)}

/-- Allows us to write `φ ∈ s` instead of `φ ∈ s.val` -/
instance states.SetLike {form : Type} [Pformula_ax form] :
  SetLike (states form) form :=
{ coe := λ s => s.1
  coe_injective' := Subtype.coe_injective }

-- Tilde
def tilde {form : Type} (states : Type) [SetLike states form]
  (φ : form) : Set states :=
{s : states | φ ∈ s}

-- States is not empty
----------------------------------------------------------
lemma hs (form : Type) [pf : Pformula_ax form]
  (hnpr : ¬ ⊢' (⊥': form )) : Nonempty (states form) := by
  -- Set of formulas Σ′ ⊇ Σ,by Lindenbaum’s lemma
  unfold states
  rw [nonempty_subtype]
  exact max_ax_exists hnpr

-- Define E
----------------------------------------------------------
def E {agents form : Type} [Pformula_ax form] [CLformula agents form]
  (s : states form) (G : Set agents) :=
{X | ite (G = univ)
-- condition G = N
--  X ∈ E(s)(N) iff ∀ φ, φ˜ ⊆ Xᶜ → [∅]φ ∉ s, where φ˜ := {t ∈ S| φ ∈ t}
(∀ φ, tilde (states form) φ ⊆ Xᶜ → (['∅] φ) ∉ s)
-- condition G ≠ N
--  When G ≠ N : X ∈ E(s)(G) iff ∃φ, φ˜ ⊆ X ∧ [G]φ ∈ s
(∃ φ, tilde (states form) φ ⊆ X ∧ (['G] φ) ∈ s)}

-- Semi-liveness
----------------------------------------------------------
lemma semi_liveness {agents form : Type} [pf : Pformula_ax form] [clf : CLformula agents form]
  (s : states form) {G : Set agents} (hG : G ⊂ univ) : ∅ ∉ E (s) (G) := by
  -- Let G ⊂ N. Assume towards contradiction that ∅ ∈ E(s)(G)
  unfold E
  intro hf

  --  ∃φ˜ ⊆ ∅ : [G]φ ∈ s:= hf, by definition EC
  simp [ne_of_ssubset hG] at hf
  cases' hf with φ hφ

  -- consistent Set (by hf), so {φ} must be inconsistent.
  have hiffbot : ⊢' (φ ↔' ⊥'):= set_empty_iff_false hφ.left

  -- ⊢ [G]φ ↔ [G]⊥:= hiffbot, by axiom (Eq)
  have hiffGbot : ⊢' ((['G] φ) ↔' (['G] ⊥')):= Eq _ _ _ hiffbot

  -- [G]⊥ ∈ s:= hφ and hiffGbot.
  have h : (['G] ⊥') ∈ s := by
    apply max_ax_contains_by_set_proof s.2 hφ.right (iff_l hiffGbot)

  -- Contradiction from axiom (⊥) : ¬[G]⊥ and h
  have := ax_neg_contains_pr_false s.2 h (Bot _)
  simp at this


-- Semi-safety
----------------------------------------------------------
lemma semi_safety {agents form : Type}
  [pf : Pformula_ax form] [clf : CLformula agents form]
  (s : states form) {G : Set agents} (hG : G ⊂ univ) : univ ∈ E (s) (G) := by
  -- Let G ⊂ N
  unfold E
  have hG' : G ≠ univ:= ne_of_ssubset hG
  simp [hG'] at *
  clear hG'

  --  [G]⊤ ∈ s and ⊤˜ = S:= axiom (⊤) : [G]⊤, and definition S
  have hT : (['G] ⊤') ∈ s := by
    apply max_ax_contains_taut s.2 (Top _)

  --  ∃φ˜ ⊆ S : [G]φ ∈ s, where φ = ⊤ from hTop
  apply Exists.intro (⊤' : form)
  exact hT


-- Semi-monotonicity
----------------------------------------------------------
lemma semi_mono {agents form : Type}
  [pf : Pformula_ax form] [clf : CLformula agents form]
  (s : states form) {G : Set agents} {X Y : Set (states form)}
  (hG : G ⊂ univ) (hXY : X ⊆ Y) (hX : X ∈ E (s) (G)) : Y ∈ E (s) (G) := by
  unfold E at *
  -- Let G ⊂ N and X ⊆ Y ⊆ S, where X ∈ E(s)(G)
  -- ∃φ˜ ⊆ X : [G]φ ∈ s:= hX, by definition EC
  have hG' : G ≠ univ:= ne_of_ssubset hG
  simp [hG'] at *
  clear hG'

  -- φ ⊆ Y : [G]φ ∈ s, because ˜φ ⊆ X ⊆ Y
  cases' hX with φ hφ
  apply Exists.intro φ
  apply And.intro
  · exact Subset.trans hφ.left hXY
  · exact hφ.right

-- Semi-superadditivity
----------------------------------------------------------
lemma semi_superadd {agents form : Type}
  [pf : Pformula_ax form] [clf : CLformula agents form]
  (s : states form) {G F : Set agents} {X Y : Set (states form)}
  (hunion : G ∪ F ⊂ univ) (hX : X ∈ E (s) (G)) (hY : Y ∈ E (s) (F)) (hintGF : G ∩ F = ∅) :
  X ∩ Y ∈ E (s) (G ∪ F) := by
  unfold E at *
  -- Let G, F ⊆ N (where G ∩ F = ∅ and G ∪ F ⊂ N) and X, Y ⊆ S
  -- where X ∈ E(s)(G) and Y ∈ E(s)(F)
  -- ∃φ˜ ⊆ X and ∃ψ˜ ⊆ Y , such that [G]φ ∈ s and [F]ψ ∈ s:= 2.4.1, by definition EC
  have hunion' : G ∪ F ≠ univ:= ne_of_ssubset hunion
  simp [hunion', union_neq_univ_left hunion, union_neq_univ_right hunion] at *
  clear hunion'
  cases' hX with φ hX
  cases' hY with ψ hY
  apply Exists.intro (φ ∧' ψ)

  -- [G∪F](φ ∧ ψ) ∈ s:= hX_h.right and hY_h.right
  -- by axiom (S) : ([G]φ∧[F]ψ) → [G ∪ F](φ ∧ ψ)
  have hand : ((['G] φ) ∧' (['F] ψ)) ∈ s := by
    apply max_ax_contains_by_set_proof_2h s.2 hX.right hY.right (p4 _ _)
  have hunionand : ((['(G ∪ F)] (φ ∧' ψ)) ∈ s) := by
    apply max_ax_contains_by_set_proof s.2 hand ((S _ _ _ _) hintGF)

  -- (φ ∧ ψ)˜ ⊆ X ∩ Y : [G ∪ F](φ ∧ ψ) ∈ s:= hX_h.left and hY_h.left and hunionand
  apply And.intro
  · apply And.intro
    · have hsubset : tilde (states form) (φ ∧' ψ) ⊆ tilde (states form) φ:= by
        unfold tilde
        rw [Set.subset_def]
        intro t ht
        simp at *
        apply max_ax_contains_by_set_proof t.2 ht (p5 _ _)
      exact Subset.trans hsubset hX.left
    · have hsubset : tilde (states form) (φ ∧' ψ) ⊆ tilde (states form) ψ:= by
        unfold tilde
        rw [Set.subset_def]
        intro t ht
        simp at *
        apply max_ax_contains_by_set_proof t.2 ht (p6 _ _)
      exact Subset.trans hsubset hY.left
  · exact hunionand

-- Regularity
----------------------------------------------------------
lemma regularity {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  (s : states form) {G : Set agents} {X : Set (states form)}
  (h : X ∈ E (s) (G)) : (Xᶜ ∉ E (s) (Gᶜ)) := by
  unfold E at *
  cases' eq_or_ssubset_of_subset (subset_univ G) with hG hG
  · -- case : G = N
    -- by definition E and first order logic
    simp [hG, (ne_of_ssubset (empty_subset_univ ha))] at *
    exact h
  · cases' (Classical.em (G = ∅)) with h_em h_em
    · -- case : G = ∅
      -- by definition E and first order logic
      simp [(ne_of_ssubset hG), h_em, (ne_of_ssubset (empty_subset_univ ha))] at *
      exact h
    · -- case : G ̸= N and G ̸= N :
      -- Let X ⊆ S, where X ∈ E(s)(G). ∃φ˜ ⊆ X : [G]φ ∈ s, by definition EC
      simp [(ne_of_ssubset hG), h_em] at *
      cases' h with φ h
      cases' h with h_left h_right
      intro ψ hψ
      -- Assume by contradiction that Xᶜ ∈ E(s)(Gᶜ)
      by_contra hf
      -- [G ∪ Gᶜ = N](φ ∧ ψ) ∈ s:= h_right and hf
      -- by axiom S [G]φ ∧ [Gᶜ]ψ → [G ∪ Gᶜ = N](φ ∧ ψ) ∈ s
      have hS : (['(G ∪ Gᶜ)] (φ ∧' ψ)) ∈ s

      · have hand : ((['G] φ) ∧' (['Gᶜ] ψ)) ∈ s := by
          apply max_ax_contains_by_set_proof_2h s.2 h_right hf (p4 _ _)
        apply max_ax_contains_by_set_proof s.2 hand
        apply (S _ _ _ _)
        simp
      simp at hS
      -- (φ ∧ ψ)˜ = ∅, because X and Xᶜ are disjoint, meaning φ˜ and ψ˜ are disjoint
      have hemptyint : tilde (states form) φ ∩ tilde (states form) ψ = ∅ := by
          rw [Set.eq_empty_iff_forall_not_mem]
          intro t hf
          rw [Set.subset_def] at *
          cases' Classical.em (t ∈ X) with h h
          · simp at hψ hf
            apply hψ
            exact hf.right
            exact h
          · apply h
            apply h_left t hf.left
      have hempty : tilde (states form) (φ ∧' ψ) ⊆ ∅ := by
        intro t hf'
        simp[tilde, Set.subset_empty_iff, Set.eq_empty_iff_forall_not_mem] at hf'
        have hφ : φ ∈ t:= by apply max_ax_contains_by_set_proof t.2 hf' (p5 _ _)
        have hψ : ψ ∈ t:= by apply max_ax_contains_by_set_proof t.2 hf' (p6 _ _)
        rw [Set.eq_empty_iff_forall_not_mem] at hemptyint
        apply hemptyint t
        simp
        apply And.intro hφ hψ
      -- a maximally consistent Set (by 3.3.6), so {(φ ∧ ψ)} must be inconsistent.
      have hiffbot : ⊢' ((φ ∧' ψ) ↔' ⊥'):= set_empty_iff_false hempty
      -- ⊢ [N](φ ∧ ψ) ↔ [N]⊥:= 3.3.7, by axiom (Eq)
      have hiffNbot : ⊢' ((['univ] (φ ∧' ψ)) ↔' (['univ] ⊥')) :=
        (Eq _ _ _) hiffbot
      simp at *
      -- [N]⊥ ∈ s:= 3.3.7 and 3.3.5.
      have h : (['univ] ⊥') ∈ s:= by
        apply max_ax_contains_by_set_proof s.2 hS
        apply iff_l
        simp only [ax_and] at *
        apply hiffNbot
      -- Contradiction from axiom (⊥) : ¬[N]⊥ and 3.3.8
      have := ax_neg_contains_pr_false s.2 h (Bot _)
      simp at this


-- N maximality
----------------------------------------------------------
lemma N_maximality {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  (s : states form) {X : Set (states form)}
  (h : Xᶜ ∉ E (s) (∅)) : X ∈ E (s) (univ) := by
  unfold E at *
  simp [(ne_of_ssubset (empty_subset_univ ha))] at *
  intro φ hX
  exact h φ hX

----------------------------------------------------------
-- Canonical Frame and Model Constructions
----------------------------------------------------------

@[simps] def canonical_frame_CL (agents form : Type) [ha : Nonempty agents]
 [pf : Pformula_ax form] [clf : CLformula agents form]
 (hnpr : ¬ ⊢' (⊥' : form)) : frameCL agents :=
{ states := states form
  hs := hs form hnpr
  -- E is a playable Effectivity Function
  E := by
      --  Showing that an effectivity function E(s) is semi-playable
      -- regular and N-maximal, suffices to prove that E(s) is playable
      let semi : semi_playable_effectivity_struct agents (states form) :=
      { E             := E
        semi_liveness := semi_liveness
        semi_safety   := semi_safety
        semi_mono     := semi_mono
        semi_superadd := semi_superadd, }

      exact playable_from_semi_Nmax_reg (states form) semi N_maximality regularity }

/-- Allows us to write `φ ∈ s` instead of `φ ∈ s.val` -/
instance canonical_frame_CL.SetLike {agents form : Type} [Nonempty agents]
  [Pformula_ax form] [CLformula agents form]
  (hnpr : ¬ ⊢' (⊥' : form)) :
  SetLike (canonical_frame_CL agents form hnpr).states form :=
{ coe := λ s => s.1
  coe_injective' := Subtype.coe_injective }


def canonical_model_CL (agents form : Type) [Nonempty agents]
  [Pformula_ax form] [CLformula agents form]
  (hnpr : ¬ ⊢' (⊥' : form)) : modelCL agents :=
{ f := canonical_frame_CL agents form hnpr
  -- V is as usual, such that s ∈ V (p) iff p ∈ s
  v := λ n => {s | (Pformula.var n) ∈ s} }

instance canonical_model_CL.f.states.SetLike {agents form : Type}[Nonempty agents]
  [Pformula_ax form] [CLformula agents form]
  (hnpr : ¬ ⊢' (⊥' : form)) :
  SetLike (canonical_model_CL agents form hnpr).f.states form :=
{ coe := λ s => s.1
  coe_injective' := Subtype.coe_injective }

@[simp] lemma canonical_model_CL.f.states.val_eq_coe {agents form : Type} [Nonempty agents]
  [Pformula_ax form] [CLformula agents form]
  (hnpr : ¬ ⊢' (⊥' : form)) (s : (canonical_model_CL agents form hnpr).f.states) : s.1 = s :=
rfl

@[simp] lemma SetLike.set_of_mem {S A : Type*} [SetLike S A] (s : S) : {x | x ∈ s} = s := rfl

----------------------------------------------------------
-- Lemmas specific to the Canonical Model
----------------------------------------------------------

-- tilde ¬ ψ = (tilde ψ)ᶜ
lemma h_tilde_compl {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  (hnpr : ¬ ⊢' (⊥' : form)) (ψ : form) :
  (tilde ((canonical_model_CL agents form hnpr).f.states) (¬' ψ)) =
    (tilde ((canonical_model_CL agents form hnpr).f.states) ψ)ᶜ :=  by
  ext1 s
  apply Iff.intro
  · intro hs hf
    have := contra_contains_pr_false s.2 hf hs
    simp at this
  · intro hs
    exact not_in_from_notin s.2 hs

-- ⊢ ψ ↔ χ ⇒ tilde ψ = tilde χ
lemma tilde_ax_iff {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {ψ χ : form} (hax : ⊢' (ψ ↔' χ)) :
  tilde ((canonical_model_CL agents form hnpr).f.states) ψ =
    tilde ((canonical_model_CL agents form hnpr).f.states) χ := by
  ext1 s
  apply Iff.intro
  · intro hs
    apply max_ax_contains_by_set_proof s.2 hs (iff_l hax)
  · intro hs
    apply max_ax_contains_by_set_proof s.2 hs (iff_r hax)

 end canonical
