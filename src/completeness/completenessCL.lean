import  semantics.consistency soundness.soundnessCL
import  syntax.CLLemmas
import tactic.induction
-- import basicmodal.semantics.consistesncy

local attribute [instance] classical.prop_decidable

-- open axCL 
open set 
open list


variable {agents : Type}
----------------------------------------------------------
-- Set Helper Functions
----------------------------------------------------------
def union_neq_univ_left {α: Type} {A B: set α} (h: A ∪ B ⊂ univ):
  A ≠ univ := 
ne_of_ssubset (ssubset_of_subset_of_ssubset (subset_union_left A B) h)

def union_neq_univ_right {α: Type} {A B: set α} (h: A ∪ B ⊂ univ):
  B ≠ univ := 
ne_of_ssubset (ssubset_of_subset_of_ssubset (subset_union_right A B) h)


----------------------------------------------------------
-- Canonical Model Construction
----------------------------------------------------------
namespace canonical

def canonicalCL (ha: nonempty agents) : frameCL agents := 
{ 
  -- S is the set of all maximal CL-consistent set of formulas
  states := {Γ : (set (formCL agents)) // (max_ax_consistent formulaCL Γ)},

  -- S is not empty  
  -- Any consistent set Σ (eg {⊤}) can be extended to the maximally CL-consistent set of formulas Σ′ ⊇ Σ,by Lindenbaum’s lemma
  hs := 
    begin
      rw nonempty_subtype,
      exact max_ax_exists formulaCL (nprfalseCL ha),
    end,
  
  -- non-empty set of agents
  ha := ha,

  -- E is a playable Effectivity Function
  E :=
    begin
      let states := {Γ : (set (formCL agents)) // (max_ax_consistent formulaCL Γ)},

      --  Showing that an effectivity function E(s) is semi-playable, regular and N-maximal, suffices to prove that E(s) is playable
      let semi: semi_playable_effectivity_fun states ha :=
      {
        -- Define E
        ----------------------------------------------------------
        E := λ s G, {X | ite (G = univ) 
          -- condition G = N
          --  X ∈ E(s)(N) iff ∀φ˜ ⊆ Xᶜ : [∅]φ /∈ s, where φ˜ := {t ∈ S| φ ∈ t}, and Xᶜ := S\X
          (∀ φ, ({t: states| φ ∈ (t.val)} ⊆ Xᶜ) → ([∅] φ) ∉ s.val)
          -- condition G ≠ N
          --  When G ̸= N: X ∈ E(s)(G) iff ∃φ˜ ⊆ X : [G]φ ∈ s
          (∃ φ, {t: states| φ ∈ (t.val)} ⊆ X ∧ ( [G] φ) ∈ s.val)},
        

        -- Semi-liveness
        ----------------------------------------------------------
        semi_liveness := 
          begin
          -- Let G ⊂ N. Assume towards contradiction that ∅ ∈ E(s)(G)
            intros s G hG hf,
            --  ∃φ˜ ⊆ ∅ : [G]φ ∈ s, from hf, by definition EC
            simp [ne_of_ssubset hG] at *,

            -- ⊢ φ ↔ ⊥, because {φ} cannot be extended into a maximally consistent set (by hf), so {φ} must be inconsistent.
            cases hf with φ hφ,
            have hiffbot : axCL (φ ↔ ⊥), from
              tilde_empty_iff_false hφ.left,

            -- ⊢ [G]φ ↔ [G]⊥, from hiffbot, by axiom (Eq)
            have hiffGbot: axCL (([G] φ) ↔ ([G] ⊥)), from axCL.Eq hiffbot,
              simp at *,

            -- [G]⊥ ∈ s, from 2.1.5 and 2.1.3.
            have h: ([G]⊥) ∈ s.1, from 
              max_ax_contains_by_set_proof s.2 hφ.right (axCL.MP (axCL.Prop5) hiffGbot),

            -- Contradiction from axiom (⊥): ¬[G]⊥ and h
            exact ax_neg_containts_pr_false s.2 h axCL.Bot,
          end,


        -- Semi-safety
        ----------------------------------------------------------
        semi_safety :=
          begin
            -- Let G ⊂ N
            intros s G hG,
            have hG': G ≠ univ, from ne_of_ssubset hG,
            simp [hG'] at *,
            clear hG',
            
            --  [G]⊤ ∈ s and ⊤˜ = S, from axiom (⊤): [G]⊤, and definition S
            have hTop: ([G] ⊤) ∈ s.val, from 
              max_ax_contains_by_empty_proof s.2 axCL.Top,

            --  ∃φ˜ ⊆ S: [G]φ ∈ s, where φ = ⊤ from hTop
            apply exists.intro (⊤: formCL agents),
            simp at hTop, exact hTop,
          end,


        -- Semi-monoticity
        ----------------------------------------------------------
        semi_monoticity :=
          begin
          -- Let G ⊂ N and X ⊆ Y ⊆ S, where X ∈ E(s)(G)
            intros s G X Y hG hXY hX,
            -- ∃φ˜ ⊆ X : [G]φ ∈ s, from hX, by definition EC
            have hG': G ≠ univ, from ne_of_ssubset hG,
            simp [hG'] at *,
            clear hG',

            -- φ ⊆ Y : [G]φ ∈ s, because ˜φ ⊆ X ⊆ Y
            cases hX with φ hφ,
            apply exists.intro φ,
            split,
            { exact subset.trans hφ.left hXY, },
            { exact hφ.right, },
          end,


        -- Semi-super-additivity
        ----------------------------------------------------------
        semi_superadd   :=
          begin
          -- Let G, F ⊆ N (where G ∩ F = ∅ and G ∪ F ⊂ N) and X, Y ⊆ S, where X ∈ E(s)(G) and Y ∈ E(s)(F)
            intros s G F X Y hunion hX hY hintGF,
            -- ∃φ˜ ⊆ X and ∃ψ˜ ⊆ Y , such that [G]φ ∈ s and [F]ψ ∈ s, from 2.4.1, by definition EC
            have hunion': G ∪ F ≠ univ, from ne_of_ssubset hunion,
            simp [hunion', union_neq_univ_left hunion, union_neq_univ_right hunion] at *,
            clear hunion',
            cases hX with φ, cases hY with ψ,
            apply exists.intro (φ & ψ),

            -- [G∪F](φ ∧ ψ) ∈ s, from hX_h.right and hY_h.right, by axiom (S): ([G]φ∧[F]ψ) → [G ∪ F](φ ∧ ψ)
            have hand: (([G]φ) & ([F]ψ)) ∈ s.1, from 
                max_ax_contains_by_set_proof_2h s.2 hX_h.right hY_h.right axCL.Prop4,
            have hunionand: (([G ∪ F](φ & ψ)) ∈ s.1), from
              max_ax_contains_by_set_proof s.2 hand (axCL.S hintGF),

            -- (φ ∧ ψ)˜ ⊆ X ∩ Y : [G ∪ F](φ ∧ ψ) ∈ s, from hX_h.left and hY_h.left and hunionand
            split,
            {
              split,
              {
                have hsubset: {t : states | φ & ψ ∈ t.val} ⊆ {t : states | φ ∈ t.val}, from
                begin
                  rw set.subset_def,
                  intros t ht, simp at *,
                  exact max_ax_contains_by_set_proof t.2 ht axCL.Prop5,
                end,
                exact subset.trans hsubset hX_h.left,
              },
              {
                have hsubset: {t : states | φ & ψ ∈ t.val} ⊆ {t : states | ψ ∈ t.val}, from
                begin
                  rw set.subset_def,
                  intros t ht, simp at *,
                  exact max_ax_contains_by_set_proof t.2 ht axCL.Prop6,
                end,
                exact subset.trans hsubset hY_h.left,
              },
            },
            {
              exact hunionand,
            },
          end,
      },

      have hE : semi.E = λ s G, {X | ite (G = univ) 
          -- condition G = N
          (∀ φ, ({t: states| φ ∈ (t.val)} ⊆ Xᶜ) → ([∅] φ) ∉ s.val)
          -- condition G ≠ N
          (∃ φ, {t: states| φ ∈ (t.val)} ⊆ X ∧ ( [G] φ) ∈ s.val)},
        from rfl,
      
      -- Regularity
      ----------------------------------------------------------
      have hreg': regular agents states semi.E, from
        begin
          intros s G F h,
          cases eq_or_ssubset_of_subset (subset_univ G),
          {
            -- case: G = N
            -- by definition E and first order logic
            simp [hE, h_1, (ne_of_ssubset (empty_subset_univ ha))] at *,
            exact h,
          },
          {
            cases em (G = ∅),
            {
              -- case: G = ∅
              -- by definition E and first order logic
              simp [hE, (ne_of_ssubset h_1), h_2, (ne_of_ssubset (empty_subset_univ ha))] at *,
              exact h,
            },
            {
              -- case: G ̸= N and G ̸= N:
              -- Let X ⊆ S, where X ∈ E(s)(G). ∃φ˜ ⊆ X : [G]φ ∈ s, by definition EC
              simp [hE, (ne_of_ssubset h_1), h_2] at *,
              cases h with φ h, cases h,
              intros ψ hψ,

              -- Assume by contradiction that Xᶜ ∈ E(s)(Gᶜ)
              by_contradiction hf,

              --  [G ∪ Gᶜ = N](φ ∧ ψ) ∈ s, from h_right and hf, by axiom S [G]φ ∧ [Gᶜ]ψ → [G ∪ Gᶜ = N](φ ∧ ψ) ∈ s
              have hS: ([G ∪ Gᶜ](φ & ψ)) ∈ s.val,
              {
                have hand: (([G]φ) & ([Gᶜ]ψ)) ∈ s.1, from 
                  max_ax_contains_by_set_proof_2h s.2 h_right hf axCL.Prop4,
                apply max_ax_contains_by_set_proof s.2 hand,
                apply axCL.S,
                simp,
              },
              simp at hS,

              -- (φ ∧ ψ)˜ = ∅, because X and Xᶜ are disjoint, meaning φ˜ and ψ˜ are disjoint
              have hemptyint: {t : states | (φ ∈ t.val)} ∩ {t : states | (ψ ∈ t.val)} = ∅, from
                begin
                  rw set.eq_empty_iff_forall_not_mem,
                  intros t hf,
                  rw set.subset_def at *,
                  cases em (t ∈ F),
                  {
                    simp at hψ,
                    apply hψ t.1 t.2 hf.right,
                    simp, exact h,
                  },
                  {
                    apply h, 
                    apply h_left t hf.left,
                  },
                end,
              have hempty: {t : states | (φ & ψ ∈ t.val)} ⊆ ∅,
              {
                intros t hf',
                simp[set.subset_empty_iff, set.eq_empty_iff_forall_not_mem] at hf',
                have hφ: φ ∈ t.1, from max_ax_contains_by_set_proof t.2 hf' axCL.Prop5,
                have hψ: ψ ∈ t.1, from max_ax_contains_by_set_proof t.2 hf' axCL.Prop6,
                rw set.eq_empty_iff_forall_not_mem at hemptyint,
                apply hemptyint t,
                simp,
                exact and.intro hφ hψ,
              },
              
              -- ⊢ (φ ∧ ψ) ↔ ⊥, because {(φ ∧ ψ)} cannot be extended into a maximally consistent set (by 3.3.6), so {(φ ∧ ψ)} must be inconsistent.
              have hiffbot : axCL ((φ & ψ) ↔ ⊥), from
                tilde_empty_iff_false hempty,

              -- ⊢ [N](φ ∧ ψ) ↔ [N]⊥, from 3.3.7, by axiom (Eq)
              have hiffNbot: axCL (([univ] (φ & ψ)) ↔ ([univ] ⊥)), from axCL.Eq hiffbot,
              simp at *,

              -- [N]⊥ ∈ s, from 3.3.7 and 3.3.5.
              have h: ([univ] (⊥: formCL agents)) ∈ s.1, from
                max_ax_contains_by_set_proof s.2 hS (axCL.MP (axCL.Prop5) hiffNbot),

              -- Contradiction from axiom (⊥): ¬[N]⊥ and 3.3.8
              exact ax_neg_containts_pr_false s.2 h axCL.Bot,
              },
          },

        end,

      -- N-maximality
        ----------------------------------------------------------
      have hNmax': N_max agents states semi.E, from
      -- by definition E and first order logic
        begin
          intros s X hXif,
          simp [hE, (ne_of_ssubset (empty_subset_univ ha))] at *,
          intros φ hX,
          exact hXif φ hX,
        end,

      exact playable_from_semi_Nmax_reg states ha semi hNmax' hreg',
    end,
}

def canonical_model_CL (ha: nonempty agents) : modelCL agents :=
{
  f := canonicalCL ha,
  -- V is as usual, such that s ∈ V (p) iff p ∈ s
  v := λ s, {n : ℕ | (formCL.var n) ∈ s.1},
}



----------------------------------------------------------
-- Truth Lemma
----------------------------------------------------------
lemma truth_lemma_CL {agents: Type} (ha: nonempty agents) (φ : formCL agents) (s: (canonical_model_CL ha).f.states): 
(s_entails (canonical_model_CL ha) s φ) ↔ (φ ∈ s.1) :=
begin
  -- This proof is by induction on φ.
  induction' φ with n φ ψ _ _ φ ψ _ _,
  {
    -- case bot
    simp [s_entails],
    exact @bot_not_mem_of_ax_consistent (formCL agents) formulaCL s.1 s.2.1,
  },
  {
    -- case var
    simpa,
  },
  {
    -- case and
    simp [s_entails, ih_φ, ih_ψ],
    split,
    {
      intro h,
      exact max_ax_contains_by_set_proof_2h s.2 h.left h.right axCL.Prop4,
    },
    {
      intro h,
      split,
      exact max_ax_contains_by_set_proof s.2 h axCL.Prop5,
      exact max_ax_contains_by_set_proof s.2 h axCL.Prop6,
    },
  },
  {
    -- case imp
    simp [s_entails, ih_φ, ih_ψ],
    split,
    {
      intro h,
      exact max_ax_contains_imp_by_proof s.2 h,
    },
    {
      intros h hφ,
      exact max_ax_contains_by_set_proof_2h s.2 hφ h likemp,
    },
  },
  {
    -- case E

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
    {
      -- ⊢ [N]φ ↔ ¬[∅]¬φ
      have hempty: axCL (([univ]φ) ↔ ¬([∅](¬φ))), from univ_iff_empty,
      simp [hG] at *, clear hG,

      split,
      {
        -- M s ⊨ [N] φ ⇒ [N] φ ∈ s
        intro h,
        simp[s_entails, hE] at h,

        have hnin: ([∅] (¬φ)) ∉ s.val, from
        begin
          apply h (¬ φ),
          apply @eq.subset (canonical_model_CL ha).f.states {t : (canonical_model_CL ha).f.states | (¬ φ) ∈ ↑t} {t : (canonical_model_CL ha).f.states | s_entails (canonical_model_CL ha) t φ}ᶜ,
          simp[ih],
          exact complement_from_contra,
        end,
        simp at hnin,
        
        have hin:  (¬[∅]¬φ) ∈ s.val, from not_in_from_notin s.2 hnin,
        simp at hin,

        exact max_ax_contains_by_set_proof s.2 hin (axCL.MP (axCL.Prop6) hempty),
      },
      {
        -- [N] φ ∈ s ⇒ M s ⊨ [N] φ
        intro h,
        simp[s_entails, hE, ih],
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

        exact hnin hin',
      },
    },
    {
      -- Case G ⊂ N
      -- intro hG,
      split,
      -- M, s ⊨ [G]φ ⇒ [G]φ ∈ s, when G ⊂ N
      {
        -- Assume M, s ⊨ [G]φ
        intro h,
        -- {s ∈ S| M, s ⊨ φ} ∈ E(s)(G), from h, by definition ⊨
        simp[s_entails] at h,
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
        have hGimp: axCL (formulaCL.imp ([G] ψ) ([G] φ)), from derived_monoticity_rule himp,
        -- [G]φ ∈ s, from hGimp and hGψ
        exact max_ax_contains_by_set_proof s.2 hGψ hGimp,
      },
      -- [G]φ ∈ s ⇒ M, s ⊨ [G]φ, when G ⊂ N
      {
        -- Assume [G]φ ∈ s
        intro h,
        -- ˜φ ⊆ {t ∈ S| φ ∈ t} : [G]φ ∈ s, from 4.1
        simp[s_entails],
        -- {t ∈ S| φ ∈ t} ∈ E (s)(G), from 4.2, by definition E(s)(G).
        simp[hE, (set.ssubset_iff_subset_ne.mp hG).right],
        apply exists.intro φ,
        -- {t ∈ S | M, t ⊨ φ} ∈ E(s)(G), from 4.3, by IH
        split,
        {
          intros t ht,
          simp[ih t],
          exact ht,
        },
        {
          exact h,
        },
      },
    },
  },
end




----------------------------------------------------------
-- Completeness
----------------------------------------------------------

-- Completeness helper
----------------------------------------------------------
lemma comphelper (φ : formCL agents) (ha: nonempty agents): 
  ¬ axCL φ → ax_consistent (@formulaCL agents) {¬φ} :=
begin
  intro h1, intros L h2,
  simp[finite_ax_consistent],
  induction L with hd tl ih,
  {
    simp[finite_conjunction],
    by_contradiction h3,
    have hbot: axCL (@formCL.bot agents), from
      axCL.MP h3 (@prtrue (formCL agents) (formulaCL)),
    exact (nprfalseCL ha) hbot,
  },
  {
    -- intro hf,
    let L := (hd :: tl),
    have h4 : (∀ ψ ∈ L, ψ = (¬φ)) → axCL (¬ (finite_conjunction formulaCL L)) → axCL φ,from 
      @fin_conj_repeat (formCL agents) (formulaCL) _ _ (nprfalseCL ha),
    simp at *, 
    cases h2 with h2 h3,
    intro h6, apply h1, apply h4 h2, 
    exact h3,
    exact h6,
  }
end 

-- Completeness
----------------------------------------------------------
theorem completenessCL (φ : formCL agents) (ha: nonempty agents): global_valid φ → axCL φ :=
begin
  rw ←not_imp_not, intro hnax,
  have hax := comphelper φ ha hnax,
  have hmax := lindenbaum formulaCL {¬φ} hax,
  simp at *,
  cases hmax with Γ' hmax, 
  cases hmax with hmax hnφ,
  simp[global_valid],
  apply exists.intro (canonical_model_CL ha),
  simp[valid_m],
  apply exists.intro (subtype.mk Γ' hmax),
  intro hf,
  have hφ, from (truth_lemma_CL ha φ (subtype.mk Γ' hmax)).mp hf,
  apply contra_containts_pr_false hmax hφ hnφ,
end

-- theorem soundnessCL (φ : formCL agents) : axCL φ → global_valid φ :=

-- def T_canonical  : frame := @canonical T_axioms sem_consT
-- def S4_canonical : frame := @canonical S4_axioms sem_consS4
-- def S5_canonical : frame := @canonical S5_axioms sem_consS5


-- def val_canonical (AX : ctx) [hax : sem_cons AX] : nat → (canonical AX).states → Prop :=
--   λ n, λ xΓ : (canonical AX).states, (p n) ∈ xΓ.val


-- lemma existence (AX : ctx) (hax : sem_cons AX) (xΓ : (canonical AX).states) :
--   ∀ φ, ◇φ ∈ xΓ.val ↔ ∃ yΔ : (canonical AX).states, φ ∈ yΔ.val ∧ (canonical AX).rel xΓ yΔ :=
-- begin
-- intro φ, split,
-- intro h1,
-- let Γbox : ctx := {ψ : form | □ψ ∈ xΓ.val},
-- have h1 : ax_consist AX (Γbox ∪ {φ}), 
-- {by_contradiction h2, simp at h2,
-- have h3 := five AX Γbox φ h2,
-- cases h3 with L h3, cases h3 with h3 h4,
-- have h5 := cut fin_conj_boxn (mp kdist (nec h4)),
-- have h6 := exercise1,
-- have h7 : ∀ ψ ∈ (list.map □ L), ψ ∈ xΓ.1, 
-- intros ψ h8, simp at *, cases h8 with a h8,
-- cases h8 with h8l h8r,
-- subst h8r, exact h3 a h8l,
-- specialize h6 xΓ.2 h7 h5,
-- have h8 := (six AX xΓ.1 (max_imp_ax xΓ.2)).mp xΓ.2 (¬φ).box,
-- cases h8 with h8l h8r, simp at *,
-- exact absurd h1 (h8r h6)
-- },
-- have h2 := lindenbaum AX (Γbox ∪ {φ}) h1,
-- cases h2 with Δ h2, cases h2 with h2 h3,
-- let xΔ : (canonical AX).states := ⟨Δ, h2⟩,
-- existsi (xΔ : (canonical AX).states),
-- have h5 := set.union_subset_iff.mp h3,
-- cases h5, split, simp at h5_right, exact h5_right,
-- have h3 : ∀ φ : form, □φ ∈ xΓ.val → φ ∈ xΔ.val,
-- intros ψ h4, apply h5_left, exact h4,
-- exact h3,
-- simp at *,
-- intros yΔ h1 h2,
-- by_contradiction h3,
-- have h4 := (max_notiff AX xΓ.1 xΓ.2 (◇φ)).mp h3,
-- have h5 := (max_dn AX xΓ.1 xΓ.2 (□¬φ)).mpr h4,
-- have h6 := (max_notiff AX yΔ.1 yΔ.2 φ).mpr (h2 (¬φ) h5),
-- exact absurd h1 h6
-- end


-- lemma truth (AX : ctx) (hax : sem_cons AX) (xΓ : (canonical AX).states) : 
--   ∀ φ, forces (canonical AX) (val_canonical AX) xΓ φ ↔ (φ ∈ xΓ.val) :=
-- begin
-- intro φ, induction φ with n φ ψ ih_φ ih_ψ 
-- φ ψ ih_φ ih_ψ φ ih_φ generalizing xΓ,
-- split, intro h1, exact false.elim h1,
-- intro h1,
-- have h2 := xΓ.2,
-- cases h2,
-- specialize h2_left [⊥],
-- simp at *,
-- exact absurd not_contra (h2_left h1),
-- repeat {rw forces, rw val_canonical},
-- split, intro h1, cases h1 with h1 h2,
-- exact max_conj_1 xΓ.2 (and.intro ((ih_φ xΓ).mp h1) ((ih_ψ xΓ).mp h2)), 
-- intro h1, split,
-- apply (ih_φ xΓ).mpr, exact max_conj_2 xΓ.2 h1,
-- apply (ih_ψ xΓ).mpr, exact max_conj_3 xΓ.2 h1,
-- split, 
-- intro h1,
-- apply max_imp_1 xΓ.2,
-- intro h2,
-- exact (ih_ψ xΓ).mp (h1 ((ih_φ xΓ).mpr h2)),
-- intros h1 h2,
-- apply (ih_ψ xΓ).mpr,
-- exact max_imp_2 xΓ.2 h1 ((ih_φ xΓ).mp h2),
-- split, intros h1, 
-- by_contradiction h2,
-- have h4 := (existence AX hax xΓ (¬φ)).mp,
-- have h5 := max_boxdn AX xΓ.1 xΓ.2 φ ((max_notiff AX xΓ.1 xΓ.2 φ.box).mp h2),
-- cases h4 h5 with xΔ h4, cases h4 with h4 h6,
-- have h7 := max_notiff AX xΔ.1 xΔ.2 φ,
-- cases h7 with h7l h7r,
-- exact absurd ((ih_φ xΔ).mp (h1 xΔ h6)) (h7r h4),
-- intros h1 xΔ h2,
-- apply (ih_φ xΔ).mpr, exact h2 φ h1,
-- end


-- lemma comphelper (AX : ctx) (φ : form) (hax : sem_cons AX) : 
--   ¬ prfK AX φ → ax_consist AX {¬φ} :=
-- begin
-- intro h1, intros L h2,
-- rw fin_ax_consist, induction L,
-- by_contradiction h3,
-- exact absurd (mp dne h3) (nprfalse AX hax), 
-- have h4 : (∀ ψ ∈ L_hd::L_tl, ψ = ¬φ) → prfK AX (¬fin_conj (L_hd::L_tl)) → prfK AX φ, 
-- from fin_conj_repeat hax,
-- simp at *, 
-- cases h2 with h2 h3,
-- intro h6, apply h1, apply h4 h2, 
-- exact h3,
-- exact h6
-- end 


-- theorem forcesAX (AX : ctx) (hax : sem_cons AX) : 
--   forces_ctx (canonical AX) (val_canonical AX) AX :=
-- begin
-- intros φ xΓ h1,
-- have h2 : ∀ ψ ∈ list.nil, ψ ∈ xΓ.val, 
-- {intros ψ h3, have h4 := list.ne_nil_of_length_pos (list.length_pos_of_mem h3),
-- simp at *, exact false.elim h4},
-- exact (truth AX hax xΓ φ).mpr (exercise1 xΓ.2 h2 (mp pl1 (ax h1)))
-- end


-- theorem completeness (AX : ctx) (hax : sem_cons AX) (φ : form) : 
--   global_sem_csq AX φ → prfK AX φ :=
-- begin
-- rw ←not_imp_not, intro h1,
-- have h2 := comphelper AX φ hax h1,
-- have h3 := lindenbaum AX {¬φ} h2,
-- simp at *,
-- cases h3 with Γ' h3, cases h3 with h3 h4, 
-- rw global_sem_csq, 
-- push_neg,
-- let f := canonical, use f AX,
-- let v := val_canonical, use v AX,
-- let xΓ' : (f AX).states := ⟨Γ', h3⟩,
-- split, 
-- exact forcesAX AX hax,
-- use xΓ',
-- have h5 := truth AX hax xΓ' ¬φ,
-- cases h5 with h5 h6,
-- have h7 := not_forces_imp (f AX) (v AX) xΓ' φ,
-- cases h7 with h7 h8, apply h8, apply h6, exact h4
-- end


-- lemma T_reflexive : T_canonical ∈ ref_class :=
-- begin
-- intros x φ h1,
-- have h2 : (∀ ψ ∈ [□φ], ψ ∈ x.1) → prfK T_axioms (fin_conj [□φ] ⊃ φ) → φ ∈ x.1, 
--   from exercise1 x.2, simp at *,
-- have h3 : prfK T_axioms (fin_conj [φ.box] ⊃ φ), 
-- {repeat {rw fin_conj},
-- have h4 : prfK T_axioms (φ.box ⊃ φ), 
-- {refine ax _, rw T_axioms, simp},
-- exact cut (mp pl5 phi_and_true) h4},
-- exact h2 h1 h3
-- end


-- theorem T_completeness (φ : form) : F_valid φ ref_class → prfK T_axioms φ :=
-- begin
-- rw ←not_imp_not, 
-- intro h1,
-- have h2 := completeness T_axioms sem_consT φ,
-- rw ←not_imp_not at h2,
-- specialize h2 h1,
-- rw F_valid, 
-- push_neg,
-- let f := T_canonical, use f,
-- split,
-- exact T_reflexive,
-- let v := val_canonical, use (@v T_axioms sem_consT),
-- have h4 := lindenbaum T_axioms {¬φ} (comphelper T_axioms φ sem_consT h1),
-- simp at *,
-- cases h4 with Γ' h4, cases h4 with h4 h5,
-- let xΓ : f.states := ⟨Γ', h4⟩,
-- use xΓ,
-- have h6 := truth T_axioms sem_consT xΓ ¬φ,
-- cases h6 with h6 h7,
-- have h8 := not_forces_imp f (@v T_axioms sem_consT) xΓ φ,
-- cases h8 with h8 h9, apply h9, apply h7, exact h5
-- end


-- lemma S4_reftrans : S4_canonical ∈ ref_trans_class :=
-- begin
-- split,
-- intros x φ h1,
-- have h2 : (∀ ψ ∈ [□φ], ψ ∈ x.1) → prfK S4_axioms (fin_conj [□φ] ⊃ φ) → φ ∈ x.1, 
--   from exercise1 x.2, simp at *,
-- have h3 : prfK S4_axioms (fin_conj [φ.box] ⊃ φ), 
-- {repeat {rw fin_conj},
-- have h4 : prfK S4_axioms (φ.box ⊃ φ), 
-- {refine ax _, rw S4_axioms, simp, rw T_axioms, simp},
-- exact cut (mp pl5 phi_and_true) h4},
-- exact h2 h1 h3,
-- intros x y z h1 h2 φ h3, apply h2 φ,
-- apply h1 (□φ),
-- have h4 : prfK S4_axioms (fin_conj [φ.box] ⊃ φ.box.box), 
-- {repeat {rw fin_conj},
-- have h5 : prfK S4_axioms (φ.box ⊃ φ.box.box), 
-- {refine ax _, rw S4_axioms, simp},
-- exact cut (mp pl5 phi_and_true) h5},
-- have h6 : (∀ ψ ∈ [□φ], ψ ∈ x.1) → prfK S4_axioms (fin_conj [□φ] ⊃ φ.box.box) → φ.box.box ∈ x.1, 
--   from exercise1 x.2, simp at *,
-- exact h6 h3 h4
-- end


-- theorem S4_completeness (φ : form) : F_valid φ ref_trans_class → prfK S4_axioms φ :=
-- begin
-- rw ←not_imp_not, 
-- intro h1,
-- have h2 := completeness S4_axioms sem_consS4 φ,
-- rw ←not_imp_not at h2,
-- specialize h2 h1,
-- rw F_valid, 
-- push_neg,
-- let f := S4_canonical, use f,
-- split,
-- exact S4_reftrans,
-- let v := val_canonical, use (@v S4_axioms sem_consS4),
-- have h4 := lindenbaum S4_axioms {¬φ} (comphelper S4_axioms φ sem_consS4 h1),
-- simp at *,
-- cases h4 with Γ' h4, cases h4 with h4 h5,
-- let xΓ : f.states := ⟨Γ', h4⟩,
-- use xΓ,
-- have h6 := truth S4_axioms sem_consS4 xΓ ¬φ,
-- cases h6 with h6 h7,
-- have h8 := not_forces_imp f (@v S4_axioms sem_consS4) xΓ φ,
-- cases h8 with h8 h9, apply h9, apply h7, exact h5
-- end


-- lemma euclid_dual {φ : form} : prfK S5_axioms ((◇(¬φ) ⊃ □(◇(¬φ))) ⊃ (◇(□φ) ⊃ □φ)) :=
-- begin
-- simp,
-- have h1 : prfK S5_axioms (◇(¬φ) ⊃ □(◇¬φ)),
-- refine ax _, rw S5_axioms, simp, simp at *,
-- have h2 := contrapos.mpr h1,
-- have h3 := cut h2 (mp pl6 dual_equiv1),
-- have h4 : prfK S5_axioms ((¬□(◇¬φ)) ↔ (¬¬◇(¬(◇¬φ)))),
--   from (mp (mp pl4 (contrapos.mpr (mp pl6 dual_equiv1))) (contrapos.mpr (mp pl5 dual_equiv1))),
-- have h5 := cut dni (cut (mp pl6 h4) h3),
-- have h6 := (contrapos.mpr (mp kdist (nec (contrapos.mpr (mp pl5 dual_equiv1))))),
-- exact (mp pl1 (cut h6 h5))
-- end


-- lemma S5_equiv : S5_canonical ∈ equiv_class :=
-- begin
-- rw equiv_ref_euclid,
-- split,
-- intros x φ h1,
-- have h2 : (∀ ψ ∈ [□φ], ψ ∈ x.1) → prfK S5_axioms (fin_conj [□φ] ⊃ φ) → φ ∈ x.1, 
--   from exercise1 x.2, simp at *,
-- have h3 : prfK S5_axioms (fin_conj [φ.box] ⊃ φ), 
-- {repeat {rw fin_conj},
-- have h4 : prfK S5_axioms (φ.box ⊃ φ), 
-- {refine ax _, rw S5_axioms, simp, rw T_axioms, simp},
-- exact cut (mp pl5 phi_and_true) h4},
-- exact h2 h1 h3,
-- intros x y z h1 h2 φ h3,
-- apply h2 φ, clear h2,
-- have h2 : prfK S5_axioms (◇(¬φ) ⊃ □(◇¬φ)), 
-- {refine ax _, rw S5_axioms, simp},
-- have h4 : prfK S5_axioms (◇(□φ) ⊃ □φ), 
--   from mp euclid_dual h2,
-- have h5 : (∀ ψ ∈ [◇(□φ)], ψ ∈ x.1) → 
--   prfK S5_axioms (fin_conj [◇(□φ)] ⊃ □φ) → □φ ∈ x.1, 
--   from exercise1 x.2, simp at *,
-- apply h5,
-- by_contradiction h6,
-- have h7 := (max_notiff S5_axioms x.1 x.2 (¬(¬φ.box).box)).mp h6,
-- have h8 := (max_dn S5_axioms x.1 x.2 ((¬φ.box).box)).mpr h7,
-- have h9 := (max_notiff S5_axioms y.1 y.2 (φ.box)).mpr (h1 (¬φ.box) h8),
-- exact absurd h3 h9,
-- exact (cut (mp pl5 phi_and_true) h4)
-- end


-- theorem S5_completeness (φ : form) : F_valid φ equiv_class → prfK S5_axioms φ :=
-- begin
-- rw ←not_imp_not, 
-- intro h1,
-- have h2 := completeness S5_axioms sem_consS5 φ,
-- rw ←not_imp_not at h2,
-- specialize h2 h1,
-- rw F_valid, 
-- push_neg,
-- let f := S5_canonical, use f,
-- split,
-- exact S5_equiv,
-- let v := val_canonical, use (@v S5_axioms sem_consS5),
-- have h4 := lindenbaum S5_axioms {¬φ} (comphelper S5_axioms φ sem_consS5 h1),
-- simp at *,
-- cases h4 with Γ' h4, cases h4 with h4 h5,
-- let xΓ : f.states := ⟨Γ', h4⟩,
-- use xΓ,
-- have h6 := truth S5_axioms sem_consS5 xΓ ¬φ,
-- cases h6 with h6 h7,
-- have h8 := not_forces_imp f (@v S5_axioms sem_consS5) xΓ φ,
-- cases h8 with h8 h9, apply h9, apply h7, exact h5
-- end

end canonical
