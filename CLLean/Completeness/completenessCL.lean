/-
Authors: Kai Obendrauf
Following the paper "A Modal Logic for Coalitional Power in Games" by Mark Pauly 
and the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley

This file contains the truth lemma for CL, and from that the proof of completeness for CL.
-/

import CLLean.Completeness.canonical
import CLLean.Soundness.soundnessCL
import Mathlib.Tactic

local attribute [instance] classical.prop_decidable

open Set List formCL axCL

namespace canonical
----------------------------------------------------------
-- Canonical Model CL
----------------------------------------------------------

def M_CL (agents : Type) [ha : Nonempty agents] : modelCL agents :=
canonical_model_CL agents (formCL agents) nprfalseCL

/-- Allows us to write `φ ∈ s` instead of `φ ∈ s` -/
instance M_CL.f.states.set_like {agents : Type} [ha : Nonempty agents] :
  set_like ((M_CL agents).f.states) (formCL agents) :=
{ coe := λ s, s.1
  coe_injective' := subtype.coe_injective }

----------------------------------------------------------
-- Truth Lemma
----------------------------------------------------------
lemma truth_lemma_CL {agents : Type} [ha : Nonempty agents] 
  (φ : formCL agents) (s : (M_CL agents).f.states) : 
  ((M_CL agents); s '⊨ φ) ↔ (φ ∈ s) := by
  let M := @M_CL agents ha
  -- This proof is by induction on φ.
  induction' φ with n φ ψ _ _ φ ψ _ _

  { -- case bot
    simp [s_entails_CL]
    exact @bot_not_mem_of_ax_consistent (formCL agents) _ s.1 s.2.1, }

  { -- case var
    simpa, }

  { -- case and
    simp [s_entails_CL, ih_φ, ih_ψ]
    split

    { intro h
      apply max_ax_contains_by_set_proof_2h s.2 h.left h.right Prop4, }

    { intro h
      split
      apply max_ax_contains_by_set_proof s.2 h Prop5
      apply max_ax_contains_by_set_proof s.2 h Prop6, }, }

  { -- case imp
    simp [s_entails_CL, ih_φ, ih_ψ]
    split

    { intro h
      exact max_ax_contains_imp_by_proof s.2 h, }

    { intro h hφ
      apply max_ax_contains_by_set_proof_2h s.2 hφ h likemp, }, }

  { -- case E
    let states := {Γ : (Set (formCL agents)) // (max_ax_consistent Γ)}
    have hE : (M).f.E.E = λ s, λ G : Set agents, _
      from rfl
    
    -- It is sufficient to consider the case when G ⊂ N, because ⊢ '[N]φ ↔ _¬ '[∅]_¬ φ
    cases Set.eq_or_ssubset_of_subset (Set.subset_univ G) with hG hG
    -- Case G = N 

    { -- ⊢ [N]φ ↔ ¬ [∅] ¬ φ
      have hempty : axCL (('[univ] φ) _↔ _¬ ('[∅](_¬ φ))):= 
        @univ_iff_empty agents (formCL agents) _ _ _
      simp [hG] at *, clear hG

      split

      { -- M s ⊨ [N] φ ⇒ '[N] φ ∈ s
        intro h
        simp [s_entails_CL, hE] at h
        have hnin : ('[∅] (_¬ φ)) ∉ s:= by
          apply h (_¬ φ)
          apply @eq.subset _ _ {t : (M_CL agents).f.states | (M_CL agents); t '⊨ φ}ᶜ
          simp [ih]
          exact complement_from_contra
        
        have hin : (_¬ '[∅]_¬ φ) ∈ s:= not_in_from_notin s.2 hnin

        apply max_ax_contains_by_set_proof s.2 hin (MP (Prop6) hempty), }

      { -- '[N] φ ∈ s ⇒ M s ⊨ '[N] φ
        intro h
        simp [s_entails_CL, hE, ih]
        intro ψ hsubseteq hf
  
        simp [Set.subset_def] at hsubseteq

        have himp : ∀ (x : M.f.states), ψ ∈ x → (_¬ φ) ∈ x:=
          λ t ht, not_in_from_notin t.2 (hsubseteq t ht)
      
        have hin : (_¬ '[∅] _¬ φ) ∈ s
          from by apply max_ax_contains_by_set_proof s.2 h (MP (Prop5) hempty)

        have hnin : ('[∅] _¬ φ) ∉ s:= 
          λ hf, contra_contains_pr_false s.2 hf hin

        have hax : axCL (ψ _→ (_¬ φ)):=
          ax_imp_from_ex himp

        have hin' : ('[∅] _¬ φ) ∈ s
        { apply max_ax_contains_by_set_proof s.2 hf
          apply @derived_monoticity_rule agents (formCL agents)
          exact hax, }

        exact hnin hin', }, }

    { -- Case G ⊂ N
      split
      -- M, s ⊨ '[G]φ ⇒ '[G]φ ∈ s, when G ⊂ N

      { -- Assume M, s ⊨ '[G]φ
        intro h
        -- {s ∈ S| M, s ⊨ φ} ∈ E(s)(G):= h, by definition ⊨
        simp [s_entails_CL] at h
        -- ∃ψ˜ ⊆ {t ∈ S| M, t ⊨ φ} : '[G]ψ ∈ s:= above, by definition E
        have huniv : G ≠ univ:= (Set.ssubset_iff_subset_ne.mp hG).right
        simp [hE, huniv] at h, clear huniv
        -- ∃ψ˜ ⊆ {t ∈ S| M, φ ∈ t} : '[G]ψ ∈ s:= above, by IH
        cases h with ψ hψ
        have hψih : ∀ (a : (M_CL agents).f.states), ψ ∈ ↑a → φ ∈ a:= by
            intro t ht
            apply (ih t).mp
            apply hψ.left
            exact ht
        -- ∃ψ˜ ⊆ φ˜ : '[G]ψ ∈ s:= hih, by definition ψ˜
        have hGψ : ('[G]ψ) ∈ s:= hψ.right
        -- ⊢ ψ → φ, since ψ˜ ⊆ φ˜ in hψih 
        have himp : axCL (ψ _→ φ):= ax_imp_from_ex hψih
        -- ⊢ '[G]ψ → '[G]φ:= himp, by the derived monoticity rule
        have hGimp : axCL (('[G] ψ) _→ ('[G] φ)):= 
          @derived_monoticity_rule agents (formCL agents) _ _ _ _ _ himp
        -- '[G]φ ∈ s:= hGimp and hGψ
        apply max_ax_contains_by_set_proof s.2 hGψ hGimp, }
      -- '[G]φ ∈ s ⇒ M, s ⊨ '[G]φ, when G ⊂ N

      { -- Assume '[G]φ ∈ s
        intro h
        -- ˜φ ⊆ {t ∈ S| φ ∈ t} : '[G]φ ∈ s:= 4.1
        simp [s_entails_CL]
        -- {t ∈ S| φ ∈ t} ∈ E (s)(G):= 4.2, by definition E(s)(G).
        simp [hE, (Set.ssubset_iff_subset_ne.mp hG).right]
        apply Exists.intro φ
        -- {t ∈ S | M, t ⊨ φ} ∈ E(s)(G):= 4.3, by IH
        split

        { intro t ht
          simp [ih]
          exact ht, }

        { exact h, }, }, }, }


----------------------------------------------------------
-- Completeness
----------------------------------------------------------
theorem completenessCL {agents : Type} [ha : Nonempty agents]
  (φ : formCL agents) : ('⊨ φ) → '⊢ φ := by
  -- Taking the contrapositive
  rw ←not_imp_not
  -- Assume ¬ ⊢ φ.
  intro hnax
  -- {¬φ} is a consistent Set:= hnax.
  obtain ⟨s, hmax, hnφ⟩ := @exists_max_ax_consistent_neg_mem (formCL agents) _ _ hnax
  -- Take the state s ∈ SC , where s = Σ.
  simp [global_valid]
  apply Exists.intro (M_CL agents)
  simp [valid_m]
  apply Exists.intro (subtype.mk s hmax)
  -- Assume towards a contradiction that M C s ⊨ φ.
  intro hf
  -- φ ∈ s, by the truth lemma:= hf
  have hφ:= (truth_lemma_CL φ (subtype.mk s hmax)).mp hf
  -- Contradiction from hφ & hnφ.
  apply contra_contains_pr_false hmax hφ hnφ
end

end canonical
