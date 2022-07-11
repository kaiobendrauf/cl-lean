import soundness.soundnessCL
import completeness.canonicalCL
import tactic.induction

local attribute [instance] classical.prop_decidable

open set list

variable {agents : Type}

namespace canonical

def canonical_model_CL (ha: nonempty agents) : modelCL agents :=

{ f := canonicalCL CLformulaCL ha (nprfalseCL ha),
  -- V is as usual, such that s ∈ V (p) iff p ∈ s
  v := λ  n, {s | (formCL.var n) ∈ s.1} }
lemma idenCL {agent: Type} {φ : formCL agents} :
--  ⊢ φ → φ s
 axCL (φ ~> φ) := @iden (formCL agents) (formulaCL) φ

----------------------------------------------------------
-- Truth Lemma
----------------------------------------------------------
lemma truth_lemma_CL {agents: Type} (ha: nonempty agents) (φ : formCL agents) 
(s: (canonical_model_CL ha).f.states): (s_entails_CL (canonical_model_CL ha) s φ) ↔ (φ ∈ s.1) :=
begin
  -- This proof is by induction on φ.
  induction' φ with n φ ψ _ _ φ ψ _ _,

  { -- case bot
    simp [s_entails_CL],
    exact @bot_not_mem_of_ax_consistent (formCL agents) formulaCL s.1 s.2.1, },

  { -- case var
    simpa, },

  { -- case and
    simp [s_entails_CL, ih_φ, ih_ψ],
    split,

    { intro h,
      exact max_ax_contains_by_set_proof_2h s.2 h.left h.right axCL.Prop4, },

    { intro h,
      split,
      exact max_ax_contains_by_set_proof s.2 h axCL.Prop5,
      exact max_ax_contains_by_set_proof s.2 h axCL.Prop6, }, },

  { -- case imp
    simp [s_entails_CL, ih_φ, ih_ψ],
    split,

    { intro h,
      exact max_ax_contains_imp_by_proof s.2 h, },

    { intros h hφ,
      exact max_ax_contains_by_set_proof_2h s.2 hφ h likemp, }, },

  { -- case E

    have hE : (canonical_model_CL ha).f.E.E = λ s G, {X | ite (G = univ) 
      -- condition G = N
      (∀ φ, ({t: (canonical_model_CL ha).f.states| φ ∈ (t.val)} ⊆ Xᶜ) → ([∅] φ) ∉ s.val)
      -- condition G ≠ N
      (∃ φ, {t: (canonical_model_CL ha).f.states| φ ∈ (t.val)} ⊆ X ∧ ( [G] φ) ∈ s.val)},
      from rfl,

    specialize ih ha,
    
    -- It is sufficient to consider the case when G ⊂ N, because ⊢ [N]φ ↔ ¬[∅]¬φ
    cases set.eq_or_ssubset_of_subset (set.subset_univ G) with hG hG,
    -- Case G = N 

    { -- ⊢ [N]φ ↔ ¬[∅]¬φ
      have hempty: axCL (([univ]φ) ↔ ¬([∅](¬φ))), from 
        @univ_iff_empty agents (formCL agents) CLformulaCL _,
      simp [hG] at *, clear hG,

      split,

      { -- M s ⊨ [N] φ ⇒ [N] φ ∈ s
        intro h,
        simp[s_entails_CL, hE] at h,

        have hnin: ([∅] (¬φ)) ∉ s.val, from
        begin
          apply h (¬ φ),
          apply @eq.subset (canonical_model_CL ha).f.states {t : (canonical_model_CL ha).f.states | (¬ φ) ∈ ↑t} {t : (canonical_model_CL ha).f.states | s_entails_CL (canonical_model_CL ha) t φ}ᶜ,
          simp[ih],
          exact complement_from_contra,
        end,
        simp at hnin,
        
        have hin:  (¬[∅]¬φ) ∈ s.val, from not_in_from_notin s.2 hnin,
        simp at hin,

        exact max_ax_contains_by_set_proof s.2 hin (axCL.MP (axCL.Prop6) hempty), },

      { -- [N] φ ∈ s ⇒ M s ⊨ [N] φ
        intro h,
        simp[s_entails_CL, hE, ih],
        intros ψ hsubseteq hf,
  
        simp[set.subset_def] at hsubseteq,

        have himp: ∀ (x : (canonical_model_CL ha).f.states), ψ ∈ x.1 → (¬ φ) ∈ x.1, from
          λ t ht, not_in_from_notin t.2 (hsubseteq t ht),
      
        have hin: (¬ [∅] ¬φ) ∈ s.val, 
          from max_ax_contains_by_set_proof s.2 h (axCL.MP (axCL.Prop5) hempty),

        have hnin: ([∅] ¬φ) ∉ s.val, from 
          λ hf, contra_containts_pr_false s.2 hf hin, 

        have hax: axCL (ψ ~> (¬φ)), from
          ax_imp_from_ex himp,

        have hin': ([∅]¬φ) ∈ s.val, from
          max_ax_contains_by_set_proof s.2 hf (derived_monoticity_rule hax),

        exact hnin hin', }, },

    { -- Case G ⊂ N
      split,
      -- M, s ⊨ [G]φ ⇒ [G]φ ∈ s, when G ⊂ N

      { -- Assume M, s ⊨ [G]φ
        intro h,
        -- {s ∈ S| M, s ⊨ φ} ∈ E(s)(G), from h, by definition ⊨
        simp[s_entails_CL] at h,
        -- ∃ψ˜ ⊆ {t ∈ S| M, t ⊨ φ} : [G]ψ ∈ s, from above, by definition E
        have huniv: G ≠ univ, from (set.ssubset_iff_subset_ne.mp hG).right,
        simp[hE, huniv] at h, clear huniv,
        -- ∃ψ˜ ⊆ {t ∈ S| M, φ ∈ t} : [G]ψ ∈ s, from above, by IH
        cases h with ψ hψ, 
        have hψih: ∀ (a : (canonical_model_CL ha).f.states), ψ ∈ ↑a → φ ∈ a.val, from
          begin
            intros t ht, 
            apply (ih t).mp, 
            apply hψ.left, 
            exact ht,
          end,
        -- ∃ψ˜ ⊆ φ˜ : [G]ψ ∈ s, from hih, by definition ψ˜
        have hGψ: ([G]ψ) ∈ s.val, from hψ.right,
        -- ⊢ ψ → φ, since ψ˜ ⊆ φ˜ in hψih 
        have himp: axCL (ψ ~> φ), from ax_imp_from_ex hψih,
        -- ⊢ [G]ψ → [G]φ, from himp, by the derived monoticity rule
        have hGimp: axCL (formulaCL.imp ([G] ψ) ([G] φ)), from 
          @derived_monoticity_rule agents (formCL agents) CLformulaCL _ _ _ himp,
        -- [G]φ ∈ s, from hGimp and hGψ
        exact max_ax_contains_by_set_proof s.2 hGψ hGimp, },
      -- [G]φ ∈ s ⇒ M, s ⊨ [G]φ, when G ⊂ N

      { -- Assume [G]φ ∈ s
        intro h,
        -- ˜φ ⊆ {t ∈ S| φ ∈ t} : [G]φ ∈ s, from 4.1
        simp[s_entails_CL],
        -- {t ∈ S| φ ∈ t} ∈ E (s)(G), from 4.2, by definition E(s)(G).
        simp[hE, (set.ssubset_iff_subset_ne.mp hG).right],
        apply exists.intro φ,
        -- {t ∈ S | M, t ⊨ φ} ∈ E(s)(G), from 4.3, by IH
        split,

        { intros t ht,
          simp[ih t],
          exact ht, },

        { exact h, }, }, }, },
end




----------------------------------------------------------
-- Completeness
----------------------------------------------------------

-- Completeness helper
-- ----------------------------------------------------------
-- lemma comphelper (φ : formCL agents) (ha: nonempty agents): 
--   ¬ axCL φ → ax_consistent (@formulaCL agents) {¬φ} :=
-- begin
--   intro h1, intros L h2,
--   simp[finite_ax_consistent],
--   induction L with hd tl ih,
--
--     simp[finite_conjunction],
--     by_contradiction h3,
--     have hbot: axCL (@formCL.bot agents), from
--       axCL.MP h3 (@prtrue (formCL agents) (formulaCL)),
--     exact (nprfalseCL ha) hbot,
--   },
--
--     -- intro hf,
--     let L := (hd :: tl),
--     have h4 : (∀ ψ ∈ L, ψ = (¬φ)) → axCL (¬ (finite_conjunction formulaCL L)) → axCL φ,from 
--       @fin_conj_repeat (formCL agents) (formulaCL) _ _ (nprfalseCL ha),
--     simp at *, 
--     cases h2 with h2 h3,
--     intro h6, apply h1, apply h4 h2, 
--     exact h3,
--     exact h6,
--   }
-- end 

-- Completeness
----------------------------------------------------------
theorem completenessCL (φ : formCL agents) (ha: nonempty agents): 
  global_valid φ → axCL φ :=
begin
  -- rw from mt
  rw ←not_imp_not, 
  -- assume ¬ ⊢ φ
  intro hnax,
  -- from ¬ ⊢ φ, have that {¬ φ} is a consistent set
  have hax := @comphelper agents (formCL agents) formulaCL φ (nprfalseCL ha) hnax,
  -- with Lindenbaum, extend {¬ φ} into a maximally consistent set
  have hmax := lindenbaum formulaCL {¬φ} hax,
  simp at *, 
  cases hmax with Γ' hmax, 
  cases hmax with hmax hnφ,
  -- show that φ is not globally valid, 
  -- by showing that there exists some model where φ is not valid.
  simp[global_valid],
  -- let that model be the canonical model
  apply exists.intro (canonical_model_CL ha),
  -- in the canonical model (M) there exists some state (s) where ¬ M s ⊨ φ
  simp[valid_m],
  -- let that state (s) be the maximally consistent set extended from {¬ φ}
  apply exists.intro (subtype.mk Γ' hmax),
  -- assume by contradiction that M s ⊨ φ
  intro hf,
  -- by the truth lemma s ∈ φ
  have hφ, from (truth_lemma_CL ha φ (subtype.mk Γ' hmax)).mp hf,
  -- in that state (s), φ ∈ ¬ s, so we do not have ¬ φ ∈ s (by consistency)
  apply contra_containts_pr_false hmax hφ hnφ,
end

end canonical
