import syntax.consistency
import syntax.CLLemmas 
import tactic.induction

local attribute [instance] classical.prop_decidable

-- open ax 
open set list


variable {agents : Type}
----------------------------------------------------------
-- Set Helper Functions
----------------------------------------------------------
def union_neq_univ_left {α : Type} {A B : set α} (h : A ∪ B ⊂ univ) : 
  A ≠ univ := 
ne_of_ssubset (ssubset_of_subset_of_ssubset (subset_union_left A B) h)

def union_neq_univ_right {α : Type} {A B : set α} (h : A ∪ B ⊂ univ) : 
  B ≠ univ := 
ne_of_ssubset (ssubset_of_subset_of_ssubset (subset_union_right A B) h)


----------------------------------------------------------
-- Canonical Model Construction
----------------------------------------------------------
namespace canonical

def canonicalCL (agents : Type) (form : Type) [ft : formula form] [clf : CLformula agents form] 
  (ha : nonempty agents) (hnpr : ¬ ax  ft.bot) : frameCL agents := 
{ -- S is the set of all maximal CL-consistent set of formulas
  states := {Γ : (set (form)) // (max_ax_consistent Γ)},

  -- S is not empty  
  -- Any consistent set Σ (eg{⊤}) can be extended to the maximally CL-consistent 
  -- set of formulas Σ′ ⊇ Σ,by Lindenbaum’s lemma
  hs := 
    begin
      rw nonempty_subtype,
      exact max_ax_exists hnpr,
    end,
  
  -- non-empty set of agents
  ha := ha,

  -- E is a playable Effectivity Function
  E :=
    begin
      let states := {Γ : (set (form)) // (max_ax_consistent Γ)},

      --  Showing that an effectivity function E(s) is semi-playable, 
      -- regular and N-maximal, suffices to prove that E(s) is playable
      let semi : semi_playable_effectivity_struct states ha := 

      { -- Define E
        ----------------------------------------------------------
        E := λ s G, {X | ite (G = univ) 
          -- condition G = N
          --  X ∈ E(s)(N) iff ∀φ˜ ⊆ Xᶜ : [∅]φ /∈ s, where φ˜ := {t ∈ S| φ ∈ t}, and Xᶜ := S\X
          (∀ φ, ({t : states| φ ∈ (t.val)} ⊆ Xᶜ) → ([∅]' φ) ∉ s.val)
          -- condition G ≠ N
          --  When G ̸= N : X ∈ E(s)(G) iff ∃φ˜ ⊆ X : [G]φ ∈ s
          (∃ φ, {t : states | φ ∈ (t.val)} ⊆ X ∧ ([G]' φ) ∈ s.val)},
        

        -- Semi-liveness
        ----------------------------------------------------------
        semi_liveness := 
          begin
          -- Let G ⊂ N. Assume towards contradiction that ∅ ∈ E(s)(G)
            intros s G hG hf,
            --  ∃φ˜ ⊆ ∅ : [G]φ ∈ s, from hf, by definition EC
            simp [ne_of_ssubset hG] at *,

            -- ⊢ φ ↔ ⊥, because {φ} cannot be extended into a maximally 
            -- consistent set (by hf), so {φ} must be inconsistent.
            cases hf with φ hφ,
            have hiffbot : ax (φ ↔' ft.bot), from set_empty_iff_false hφ.left,

            -- ⊢ [G]φ ↔ [G]⊥, from hiffbot, by axiom (Eq)
            have hiffGbot : ax (([G]' φ) ↔' ([G]' ft.bot)), from Eq _ _ _ hiffbot,
              -- simp at *,

            -- [G]⊥ ∈ s, from 2.1.5 and 2.1.3.
            have h : ([G]' ft.bot) ∈ s.1, 
              from max_ax_contains_by_set_proof s.2 hφ.right (iff_l hiffGbot),

            -- Contradiction from axiom (⊥) : ¬[G]⊥ and h
            apply ax_neg_containts_pr_false s.2 h (Bot _),
          end,

        -- Semi-safety
        ----------------------------------------------------------
        semi_safety := 
          begin
            -- Let G ⊂ N
            intros s G hG,
            have hG' : G ≠ univ, from ne_of_ssubset hG,
            simp [hG'] at *,
            clear hG',
            
            --  [G]⊤ ∈ s and ⊤˜ = S, from axiom (⊤) : [G]⊤, and definition S
            have hTop : ([G]' ft.top) ∈ s.val, 
              from max_ax_contains_by_empty_proof s.2 (Top _),

            --  ∃φ˜ ⊆ S : [G]φ ∈ s, where φ = ⊤ from hTop
            apply exists.intro (ft.top),
            simp at hTop, exact hTop,
          end,


        -- Semi-monoticity
        ----------------------------------------------------------
        semi_monoticity := 
          begin
          -- Let G ⊂ N and X ⊆ Y ⊆ S, where X ∈ E(s)(G)
            intros s G X Y hG hXY hX,
            -- ∃φ˜ ⊆ X : [G]φ ∈ s, from hX, by definition EC
            have hG' : G ≠ univ, from ne_of_ssubset hG,
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
          -- Let G, F ⊆ N (where G ∩ F = ∅ and G ∪ F ⊂ N) and X, Y ⊆ S, 
          -- where X ∈ E(s)(G) and Y ∈ E(s)(F)
            intros s G F X Y hunion hX hY hintGF,
            -- ∃φ˜ ⊆ X and ∃ψ˜ ⊆ Y , such that [G]φ ∈ s and [F]ψ ∈ s, from 2.4.1, by definition EC
            have hunion' : G ∪ F ≠ univ, from ne_of_ssubset hunion,
            simp [hunion', union_neq_univ_left hunion, union_neq_univ_right hunion] at *,
            clear hunion',
            cases hX with φ, cases hY with ψ,
            apply exists.intro (φ ∧' ψ),

            -- [G∪F](φ ∧ ψ) ∈ s, from hX_h.right and hY_h.right, 
            -- by axiom (S) : ([G]φ∧[F]ψ) → [G ∪ F](φ ∧ ψ)
            have hand : (([G]' φ) ∧' ([F]' ψ)) ∈ s.1, 
              from max_ax_contains_by_set_proof_2h s.2 hX_h.right hY_h.right (p4 _ _),
            have hunionand : (([(G ∪ F)]' (φ ∧' ψ)) ∈ s.1), 
              from max_ax_contains_by_set_proof s.2 hand ((S _ _ _ _) hintGF),

            -- (φ ∧ ψ)˜ ⊆ X ∩ Y : [G ∪ F](φ ∧ ψ) ∈ s, from hX_h.left and hY_h.left and hunionand
            split,
            { split,
              { have hsubset : {t : states | φ ∧' ψ ∈ t.val} ⊆ {t : states | φ ∈ t.val}, from
                begin
                  rw set.subset_def,
                  intros t ht, simp at *,
                  exact max_ax_contains_by_set_proof t.2 ht (p5 _ _),
                end,
                exact subset.trans hsubset hX_h.left, },
              { have hsubset : {t : states | φ ∧' ψ ∈ t.val} ⊆ {t : states | ψ ∈ t.val}, from
                begin
                  rw set.subset_def,
                  intros t ht, simp at *,
                  exact max_ax_contains_by_set_proof t.2 ht (p6 _ _),
                end,
                exact subset.trans hsubset hY_h.left, }, },
            { exact hunionand, },
          end, },
          
      have hE : semi.E = λ s G, {X | ite (G = univ) 
          -- condition G = N
          (∀ φ, ({t : states| φ ∈ (t.val)} ⊆ Xᶜ) → ([∅]' φ) ∉ s.val)
          -- condition G ≠ N
          (∃ φ, {t : states| φ ∈ (t.val)} ⊆ X ∧ ([G]' φ) ∈ s.val)},
        from rfl,
      
      -- Regularity
      ----------------------------------------------------------
      have hreg' : regular agents states semi.E, from
        begin
          intros s G F h,
          cases eq_or_ssubset_of_subset (subset_univ G),

          { -- case : G = N
            -- by definition E and first order logic
            simp [hE, h_1, (ne_of_ssubset (empty_subset_univ ha))] at *,
            exact h, },

          { cases em (G = ∅),

            { -- case : G = ∅
              -- by definition E and first order logic
              simp [hE, (ne_of_ssubset h_1), h_2, (ne_of_ssubset (empty_subset_univ ha))] at *,
              exact h, },

            { -- case : G ̸= N and G ̸= N : 
              -- Let X ⊆ S, where X ∈ E(s)(G). ∃φ˜ ⊆ X : [G]φ ∈ s, by definition EC
              simp [hE, (ne_of_ssubset h_1), h_2] at *,
              cases h with φ h, cases h,
              intros ψ hψ,

              -- Assume by contradiction that Xᶜ ∈ E(s)(Gᶜ)
              by_contradiction hf,

              -- [G ∪ Gᶜ = N](φ ∧ ψ) ∈ s, from h_right and hf, 
              -- by axiom S [G]φ ∧ [Gᶜ]ψ → [G ∪ Gᶜ = N](φ ∧ ψ) ∈ s
              have hS : ([(G ∪ Gᶜ)]' (φ ∧' ψ)) ∈ s.val,

              { have hand : (([G]' φ) ∧' ([Gᶜ]' ψ)) ∈ s.1, 
                from max_ax_contains_by_set_proof_2h s.2 h_right hf (p4 _ _),
                apply max_ax_contains_by_set_proof s.2 hand,
                apply (S _ _ _ _),
                simp, },
              simp at hS,

              -- (φ ∧ ψ)˜ = ∅, because X and Xᶜ are disjoint, meaning φ˜ and ψ˜ are disjoint
              have hemptyint : {t : states | (φ ∈ t.val)} ∩ {t : states | (ψ ∈ t.val)} = ∅, from
                begin
                  rw set.eq_empty_iff_forall_not_mem,
                  intros t hf,
                  rw set.subset_def at *,
                  cases em (t ∈ F),

                  { simp at hψ,
                    apply hψ t.1 t.2 hf.right,
                    simp, exact h, },

                  { apply h, 
                    apply h_left t hf.left, },
                end,
              have hempty : {t : states | (φ ∧' ψ ∈ t.val)} ⊆ ∅,

              { intros t hf',
                simp[set.subset_empty_iff, set.eq_empty_iff_forall_not_mem] at hf',
                have hφ : φ ∈ t.1, from max_ax_contains_by_set_proof t.2 hf' (p5 _ _),
                have hψ : ψ ∈ t.1, from max_ax_contains_by_set_proof t.2 hf' (p6 _ _),
                rw set.eq_empty_iff_forall_not_mem at hemptyint,
                apply hemptyint t,
                simp,
                split, exact hφ, exact hψ, },
              
              -- ⊢ (φ ∧ ψ) ↔ ⊥, because {(φ ∧ ψ)} cannot be extended into 
              -- a maximally consistent set (by 3.3.6), so {(φ ∧ ψ)} must be inconsistent.
              have hiffbot : ax ((φ ∧' ψ) ↔' ft.bot), from set_empty_iff_false hempty,

              -- ⊢ [N](φ ∧ ψ) ↔ [N]⊥, from 3.3.7, by axiom (Eq)
              have hiffNbot : ax (([univ]' (φ ∧' ψ)) ↔' ([univ]' ft.bot)), 
                from (Eq _ _ _) hiffbot,
              simp at *,

              -- [N]⊥ ∈ s, from 3.3.7 and 3.3.5.
              have h : ([univ]' ft.bot) ∈ s.1, 
                from max_ax_contains_by_set_proof s.2 hS (iff_l hiffNbot),

              -- Contradiction from axiom (⊥) : ¬[N]⊥ and 3.3.8
              exact ax_neg_containts_pr_false s.2 h (Bot _), }, },

        end,

      -- N-maximality
        ----------------------------------------------------------
      have hNmax' : N_max agents states semi.E, from
      -- by definition E and first order logic
        begin
          intros s X hXif,
          simp [hE, (ne_of_ssubset (empty_subset_univ ha))] at *,
          intros φ hX,
          exact hXif φ hX,
        end,

      exact playable_from_semi_Nmax_reg states ha semi hNmax' hreg',
    end, }



-- def filtered_model_CL  (agents : Type) (form : Type) [ft : formula form] [clf : CLformula agents form]
--   (ha : nonempty agents) (φ : form) (canonical : modelCL agents) (cl : form → set (form)): 
--   modelCL agents :=
-- { states := 
--   { {s ∈ (canonical.f.states ∩ cl φ) | s ∈ canonical.f.states } },
--   E :=
--   { E := λ s G,

--   }

-- }

  

end canonical
