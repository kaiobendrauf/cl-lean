import syntax.consistency
import syntax.CLLemmas
import semantics.model
import tactic.induction

local attribute [instance] classical.prop_decidable

open set list

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
-- Canonical Frame Defintions and Lemmas
----------------------------------------------------------
namespace canonical

-- Define States
----------------------------------------------------------
-- S is the set of all maximal CL-consistent set of formulas
def states (form : Type) [pf : Pformula form] [pax : Pformula_ax form] := 
{Γ : (set (form)) // (max_ax_consistent Γ)}

/-- Allows us to write `φ ∈ s` instead of `φ ∈ s.val` -/
instance states.set_like {form : Type} [pf : Pformula form] [pax : Pformula_ax form] :
  set_like (states form) form :=
{ coe := λ s, s.1,
  coe_injective' := subtype.coe_injective }

-- Tilde
def tilde {form : Type} [pf : Pformula form] [pax : Pformula_ax form] 
  (states : Type) [sl : set_like states form] (φ : form) : set states := 
{s : states | φ ∈ s}

lemma h_tilde_compl {form : Type} [pf : Pformula form] [pax : Pformula_ax form] 
  (states : Type) [sl : set_like states form] (φ : form) : 
  tilde states (¬' φ) = (tilde states φ)ᶜ := 
begin
  ext s,
  unfold tilde,
  split,
  { intros hx hf,
    apply contra_containts_pr_false,
    exact contra_containts_pr_false x.2 hf hx, },
  { intros hx,
    exact not_in_from_notin x.2 hx, },
end

-- States is not empty
----------------------------------------------------------
lemma hs (form : Type) [pf : Pformula form] [pax : Pformula_ax form] 
  (hnpr : ¬ ⊢' (⊥': form )) : nonempty (states form) :=
begin
  -- Any consistent set Σ (eg{⊤}) can be extended to the maximally CL-consistent 
  -- set of formulas Σ′ ⊇ Σ,by Lindenbaum’s lemma
  unfold states,
  rw nonempty_subtype,
  exact max_ax_exists hnpr,
end

-- Define E
----------------------------------------------------------
def E {agents form : Type} 
  [pf : Pformula form] [pax : Pformula_ax form] [clf : CLformula agents form]
  (s : states form) (G : set agents) :=
{X | ite (G = univ) 
-- condition G = N
--  X ∈ E(s)(N) iff ∀φ˜ ⊆ Xᶜ : [∅]φ /∈ s, where φ˜ := {t ∈ S| φ ∈ t}, and Xᶜ := S\X
(∀ φ, {t : (states form) | φ ∈ (t.val)} ⊆ Xᶜ → (['∅] φ) ∉ s.val)
-- condition G ≠ N
--  When G ≠ N : X ∈ E(s)(G) iff ∃φ˜ ⊆ X : [G]φ ∈ s
(∃ φ, {t : (states form) | φ ∈ (t.val)} ⊆ X ∧ (['G] φ) ∈ s.val)}

-- Semi-liveness
----------------------------------------------------------
lemma semi_liveness {agents form : Type} 
  [pf : Pformula form] [pax : Pformula_ax form] [clf : CLformula agents form]
  (s : states form) {G : set agents} (hG : G ⊂ univ) : ∅ ∉ E (s) (G) :=
begin
-- Let G ⊂ N. Assume towards contradiction that ∅ ∈ E(s)(G)
  unfold E,
  intros hf,
  --  ∃φ˜ ⊆ ∅ : [G]φ ∈ s, from hf, by definition EC
  simp [ne_of_ssubset hG] at hf,

  -- ⊢ φ ↔ ⊥, because {φ} cannot be extended into a maximally 
  -- consistent set (by hf), so {φ} must be inconsistent.
  cases hf with φ hφ,
  have hiffbot : ⊢' (φ ↔' ⊥'), from set_empty_iff_false hφ.left,

  -- ⊢ [G]φ ↔ [G]⊥, from hiffbot, by axiom (Eq)
  have hiffGbot : ⊢' ((['G] φ) ↔' (['G] ⊥')), from Eq _ _ _ hiffbot,
    -- simp at *,

  -- [G]⊥ ∈ s, from 2.1.5 and 2.1.3.
  have h : (['G] ⊥') ∈ s.1, 
    from max_ax_contains_by_set_proof s.2 hφ.right (iff_l hiffGbot),

  -- Contradiction from axiom (⊥) : ¬[G]⊥ and h
  apply ax_neg_containts_pr_false s.2 h (Bot _),
end

-- Semi-safety
----------------------------------------------------------
lemma semi_safety {agents form : Type} 
  [pf : Pformula form] [pax : Pformula_ax form] [clf : CLformula agents form]
  (s : states form) {G : set agents} (hG : G ⊂ univ) : univ ∈ E (s) (G) :=
begin
  -- Let G ⊂ N
  unfold E,
  have hG' : G ≠ univ, from ne_of_ssubset hG,
  simp [hG'] at *,
  clear hG',
  
  --  [G]⊤ ∈ s and ⊤˜ = S, from axiom (⊤) : [G]⊤, and definition S
  have hT : (['G] ⊤') ∈ s.val, 
    from max_ax_contains_taut s.2 (Top _),

  --  ∃φ˜ ⊆ S : [G]φ ∈ s, where φ = ⊤ from hTop
  apply exists.intro (⊤' : form),
  exact hT,
end


-- Semi-monotonicity
----------------------------------------------------------
lemma semi_mono {agents form : Type} 
  [pf : Pformula form] [pax : Pformula_ax form] [clf : CLformula agents form]
  (s : states form) {G : set agents} {X Y : set (states form)} 
  (hG : G ⊂ univ) (hXY : X ⊆ Y) (hX : X ∈ E (s) (G)) : Y ∈ E (s) (G) :=
begin
  unfold E at *,
  -- Let G ⊂ N and X ⊆ Y ⊆ S, where X ∈ E(s)(G)
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
end

-- Semi-superadditivity
----------------------------------------------------------
lemma semi_superadd {agents form : Type} 
  [pf : Pformula form] [pax : Pformula_ax form] [clf : CLformula agents form]
  (s : states form) {G F : set agents} {X Y : set (states form)}
  (hunion : G ∪ F ⊂ univ) (hX : X ∈ E (s) (G)) (hY : Y ∈ E (s) (F)) (hintGF : G ∩ F = ∅) : 
  X ∩ Y ∈ E (s) (G ∪ F) :=
begin
  unfold E at *,
  -- Let G, F ⊆ N (where G ∩ F = ∅ and G ∪ F ⊂ N) and X, Y ⊆ S, 
  -- where X ∈ E(s)(G) and Y ∈ E(s)(F)
  -- ∃φ˜ ⊆ X and ∃ψ˜ ⊆ Y , such that [G]φ ∈ s and [F]ψ ∈ s, from 2.4.1, by definition EC
  have hunion' : G ∪ F ≠ univ, from ne_of_ssubset hunion,
  simp [hunion', union_neq_univ_left hunion, union_neq_univ_right hunion] at *,
  clear hunion',
  cases hX with φ, cases hY with ψ,
  apply exists.intro (φ ∧' ψ),

  -- [G∪F](φ ∧ ψ) ∈ s, from hX_h.right and hY_h.right, 
  -- by axiom (S) : ([G]φ∧[F]ψ) → [G ∪ F](φ ∧ ψ)
  have hand : ((['G] φ) ∧' (['F] ψ)) ∈ s.1, 
    from max_ax_contains_by_set_proof_2h s.2 hX_h.right hY_h.right (p4 _ _),
  have hunionand : ((['(G ∪ F)] (φ ∧' ψ)) ∈ s.1), 
    from max_ax_contains_by_set_proof s.2 hand ((S _ _ _ _) hintGF),

  -- (φ ∧ ψ)˜ ⊆ X ∩ Y : [G ∪ F](φ ∧ ψ) ∈ s, from hX_h.left and hY_h.left and hunionand
  split,
  { split,
    { have hsubset : {t : (states form) | φ ∧' ψ ∈ t.val} ⊆ {t : (states form) | φ ∈ t.val}, from
      begin
        rw set.subset_def,
        intros t ht, simp at *,
        exact max_ax_contains_by_set_proof t.2 ht (p5 _ _),
      end,
      exact subset.trans hsubset hX_h.left, },
    { have hsubset : {t : (states form) | φ ∧' ψ ∈ t.val} ⊆ {t : (states form) | ψ ∈ t.val}, from
      begin
        rw set.subset_def,
        intros t ht, simp at *,
        exact max_ax_contains_by_set_proof t.2 ht (p6 _ _),
      end,
      exact subset.trans hsubset hY_h.left, }, },
  { exact hunionand, },
end

-- Regularity
----------------------------------------------------------
lemma regularity {agents form : Type} [ha : nonempty agents]
  [pf : Pformula form] [pax : Pformula_ax form] [clf : CLformula agents form]
  (s : states form) {G : set agents} {X : set (states form)}
  (h : X ∈ E (s) (G)) : (Xᶜ ∉ E (s) (Gᶜ)) :=
begin
  unfold E at *,
  cases eq_or_ssubset_of_subset (subset_univ G),
  { -- case : G = N
    -- by definition E and first order logic
    simp [h_1, (ne_of_ssubset (empty_subset_univ ha))] at *,
    exact h, },

  { cases em (G = ∅),

    { -- case : G = ∅
      -- by definition E and first order logic
      simp [(ne_of_ssubset h_1), h_2, (ne_of_ssubset (empty_subset_univ ha))] at *,
      exact h, },

    { -- case : G ̸= N and G ̸= N : 
      -- Let X ⊆ S, where X ∈ E(s)(G). ∃φ˜ ⊆ X : [G]φ ∈ s, by definition EC
      simp [(ne_of_ssubset h_1), h_2] at *,
      cases h with φ h, cases h,
      intros ψ hψ,

      -- Assume by contradiction that Xᶜ ∈ E(s)(Gᶜ)
      by_contradiction hf,

      -- [G ∪ Gᶜ = N](φ ∧ ψ) ∈ s, from h_right and hf, 
      -- by axiom S [G]φ ∧ [Gᶜ]ψ → [G ∪ Gᶜ = N](φ ∧ ψ) ∈ s
      have hS : (['(G ∪ Gᶜ)] (φ ∧' ψ)) ∈ s.val,

      { have hand : ((['G] φ) ∧' (['Gᶜ] ψ)) ∈ s.1, 
        from max_ax_contains_by_set_proof_2h s.2 h_right hf (p4 _ _),
        apply max_ax_contains_by_set_proof s.2 hand,
        apply (S _ _ _ _),
        simp, },
      simp at hS,

      -- (φ ∧ ψ)˜ = ∅, because X and Xᶜ are disjoint, meaning φ˜ and ψ˜ are disjoint
      have hemptyint : {t : (states form) | (φ ∈ t.val)} ∩ {t : (states form) | (ψ ∈ t.val)} = ∅, from
        begin
          rw set.eq_empty_iff_forall_not_mem,
          intros t hf,
          rw set.subset_def at *,
          cases em (t ∈ X),

          { simp at hψ hf,
            apply hψ, 
            exact hf.right,
            exact h, },

          { apply h, 
            apply h_left t hf.left, },
        end,
      have hempty : {t : (states form) | (φ ∧' ψ ∈ t.val)} ⊆ ∅,

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
      have hiffbot : ⊢' ((φ ∧' ψ) ↔' ⊥'), from set_empty_iff_false hempty,

      -- ⊢ [N](φ ∧ ψ) ↔ [N]⊥, from 3.3.7, by axiom (Eq)
      have hiffNbot : ⊢' ((['univ] (φ ∧' ψ)) ↔' (['univ] ⊥')), 
        from (Eq _ _ _) hiffbot,
      simp at *,

      -- [N]⊥ ∈ s, from 3.3.7 and 3.3.5.
      have h : (['univ] ⊥') ∈ s.1, from
      begin
        apply max_ax_contains_by_set_proof s.2 hS,
        apply iff_l,
        simp only [ax_and] at *,
        apply hiffNbot,
      end,

      -- Contradiction from axiom (⊥) : ¬[N]⊥ and 3.3.8
      exact ax_neg_containts_pr_false s.2 h (Bot _), }, },
end

-- N maximality
----------------------------------------------------------
lemma N_maximality {agents form : Type} [ha : nonempty agents]
  [pf : Pformula form] [pax : Pformula_ax form] [clf : CLformula agents form]
  (s : states form) {X : set (states form)}
  (h : Xᶜ ∉ E (s) (∅)) : X ∈ E (s) (univ) :=
begin
  unfold E at *,
  simp [(ne_of_ssubset (empty_subset_univ ha))] at *,
  intros φ hX,
  exact h φ hX,
end

----------------------------------------------------------
-- Canonical Frame Constructions
----------------------------------------------------------


@[simps?] def canonicalCL (agents form : Type) [ha : nonempty agents]
 [pf : Pformula form] [pax : Pformula_ax form] [clf : CLformula agents form]
 (hnpr : ¬ ⊢' ⊥') : frameCL agents := 
{ states := states form,
  hs := hs form hnpr,
  -- E is a playable Effectivity Function
  E :=
    begin
      --  Showing that an effectivity function E(s) is semi-playable, 
      -- regular and N-maximal, suffices to prove that E(s) is playable
      let semi : semi_playable_effectivity_struct agents (states form) :=
      { E             := E,
        semi_liveness := semi_liveness,
        semi_safety   := semi_safety,
        semi_mono     := semi_mono,
        semi_superadd := semi_superadd, },

      exact playable_from_semi_Nmax_reg (states form) semi N_maximality regularity,
    end, }

def canonical_model_CL (agents form : Type) [ha : nonempty agents]
 [pf : Pformula form] [pax : Pformula_ax form] [clf : CLformula agents form]
 (hnpr : ¬ ⊢' (⊥' : form)) : modelCL agents :=
{ f := canonicalCL agents form hnpr,
  -- V is as usual, such that s ∈ V (p) iff p ∈ s
  v := λ  n, {s | (Pformula.var n) ∈ s.1} }

@[simps?] def canonical_CLK {agents : Type} (form : Type) 
  [ha : nonempty agents] [hN : fintype agents]
  [pf : Pformula form] [pax : Pformula_ax form] 
  [clf : CLformula agents form] [kf: Kformula agents form]
  (hnpr : ¬ ⊢' (⊥' : form)) : frameCLK agents :=
{ rel := λ i : agents, λ s, {t | {φ | K' (i) (φ) ∈ s.1} = {φ | K' (i) (φ) ∈ t.1}},
  rfl := by simp,
  sym := λ i s t ht, eq.symm ht,
  trans := λ i s t u hst htu, (rfl.congr htu).mp hst,
  .. canonicalCL agents form hnpr }


end canonical
