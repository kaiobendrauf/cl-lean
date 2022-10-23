import soundness.soundnessCLC
import completeness.canonicalCL
import syntax.axiomsCLC
import tactic.induction
import data.finset.powerset


local attribute [instance] classical.prop_decidable

open set formCLC

namespace canonical


def canonical_model_CLC {agents : Type} [hN : fintype agents] (ha : nonempty agents) : 
  modelCLK agents :=
{ f := canonical_CLK ha (formCLC agents) (nprfalseCLC ha),
  -- V is as usual, such that s ∈ V (p) iff p ∈ s
  v := λ  n, {s | (formCLC.var n) ∈ s.1} }

----------------------------------------------------------
-- Filtration
----------------------------------------------------------

-- Let cl(φ) be the smallest set such that:
-- cl(φ) contains all subformulas of φ.
-- For every φ in cl(φ), if φ is not of the form ¬ψ, then ¬φ ∈ cl(φ). In other words cl(φ) is closed under single negations. 
-- C G (φ) ∈ cl (φ) ⇒ K i (C G (φ)) ∈ cl(φ), ∀ i ∈ G . 
-- [G] φ ∈ cl (φ), G ≠ ∅ ⇒ C G [G] φ ∈ cl (φ).

noncomputable def cl_C {agents : Type} [hN : fintype agents] (G : set (agents)) (φ : formCLC agents) : 
  finset (formCLC agents) :=
finset.image (λ i, k (i) (c G φ)) (to_finset G)

def E_list_to_form {agents : Type} [hN : fintype agents] (φ : formCLC agents) : 
  list (agents) → formCLC agents
| list.nil  := ⊤
| (i :: is) := (k i φ) & (E_list_to_form is)

noncomputable def cl_E {agents : Type} [hN : fintype agents] (G : set (agents)) (φ : formCLC agents) : 
  formCLC agents := 
E_list_to_form φ (finset.to_list (to_finset G))

noncomputable def cl {agents : Type} [hN : fintype agents] : 
  formCLC agents → finset (formCLC agents)
|  bot          := {bot, ¬ bot}
| (var n)       := {var n, ¬ var n}
| (imp φ ψ)     := cl φ ∪ cl ψ ∪ 
                    match ψ with
                    | bot := {(imp φ ψ)}
                    | _   := {(imp φ ψ), ¬ (imp φ ψ)} 
                    end
| (and φ ψ)     := cl φ ∪ cl ψ ∪ {(and φ ψ), ¬ (and φ ψ)}
| ([G] φ)       := cl φ ∪ {([G] φ), ¬ [G] φ} ∪ 
                    (ite (G = ∅) (finset.empty : finset (formCLC agents)) 
                         ({(c (G) ([G] φ)), ¬(c (G) ([G] φ))} ∪ cl_C G ([G] φ)))
| (k i φ)       := cl φ ∪ {(k i φ), ¬ (k i φ)}
| (e G φ)       := cl φ ∪ {(e G φ), ¬ (e G φ), cl_E G φ }
| (c G φ)       := cl φ ∪ {(c G φ), ¬ (c G φ)} ∪ cl_C G φ

noncomputable def s_f {agents : Type} [hN : fintype agents]
  (φ : formCLC agents) (s : set (formCLC agents)) : 
  finset (formCLC agents) :=
finset.filter (λ ψ, ψ ∈ s) (cl(φ))

noncomputable def phi_s_f {agents : Type} [hN : fintype agents] 
  (φ : formCLC agents) (s : set (formCLC agents)) :
  formCLC agents :=
finite_conjunction (finset.to_list (s_f φ s))

-- def S_f {agents : Type} [hN : fintype agents] (φ : formCLC agents) : Type :=
-- finset.attach (finset.filter (λ sf, ax_consistent ({x | x ∈ sf})) (finset.powerset (cl(φ))))

def S_f {agents : Type} [hN : fintype agents] (ha : nonempty agents) (φ : formCLC agents) : Type :=
finset.attach (finset.filter (λ sf, ∃ s: (canonical_model_CLC ha).f.states, (s.1 ∩ {x | x ∈ cl(φ)}) = {x | x ∈ sf}) (finset.powerset (cl(φ))))

def s_f_to_s {agents : Type} (ha : nonempty agents) [hN : fintype agents] (φ : formCLC agents) (sf : (S_f ha φ)) :
  ∃ s: (canonical_model_CLC ha).f.states, (s.1 ∩ {x | x ∈ cl(φ)}) = {x | x ∈ sf.1.1}:=
begin
  cases sf.1 with sfin hsf,
  dsimp[finset.powerset, finset.filter] at *,
  simp at *,
  exact hsf.right,
end

def s_f_ax {agents : Type} (ha : nonempty agents) [hN : fintype agents] (φ : formCLC agents) (sf : (S_f ha φ)): 
  ax_consistent {x | x ∈ sf.1.1} :=
begin
  cases (s_f_to_s ha φ sf) with s hs,
  have hax := s.2.1,
  simp[ax_consistent] at *,
  intros fs hsfin,
  apply hax fs, 
  intros ψ hψfs,
  have hsfs : ∀ x ∈ ↑↑↑sf, x ∈ ↑s, from
  begin
    intros x hx,
    rw ←hs at hx,
    exact mem_of_mem_inter_left hx,
  end,
  apply hsfs,
  apply hsfin,
  exact hψfs,
end

noncomputable def phi_X_list {agents : Type} [hN : fintype agents] (ha : nonempty agents) 
  (φ : formCLC agents) :
  list (S_f ha φ) → list (formCLC agents)
| list.nil  := list.nil
| (s :: ss) := ((phi_s_f φ ({x | x ∈ s.1.1})) :: phi_X_list ss)

noncomputable def phi_X {agents : Type} [hN : fintype agents] (ha : nonempty agents) 
  (φ : formCLC agents) (X : finset (S_f ha φ)) :
  formCLC agents :=
finite_disjunction (phi_X_list ha φ (finset.to_list X))

noncomputable def phi_X_set {agents : Type} [hN : fintype agents] (ha : nonempty agents)  
  (φ : formCLC agents) (X : set (S_f ha φ)) :
  formCLC agents :=
begin
  simp[S_f, finset.attach] at X,
  have hX : finite X, from finite.of_fintype X,
  have X : finset (S_f ha φ), from finite.to_finset hX,
  exact phi_X ha φ X,
  -- exact finite_disjunction (phi_X_list ha φ (finset.to_list X)),
end

def tilde {agents : Type} [hN : fintype agents] (ha : nonempty agents) (ψ : formCLC agents): 
  set ((canonical_model_CLC ha).f.states) :=
{s : (canonical_model_CLC ha).f.states | ψ ∈ s.1}

 
def filtered_model_CLC {agents : Type} [hN : fintype agents] (ha : nonempty agents) 
  (φ : formCLC agents) :
  modelCLK agents := 
{ f := 
  { states := S_f ha φ,
    hs := sorry, 
    ha := ha,
    E := 
    { E := λ sf G, {X | ite (G = univ) 
          -- condition G ≠ N
          -- ∀t ∈ S, sf = tf ⇒  ̃phiX ∈ E(t)(G)
          (∀ t : (canonical_model_CLC ha).f.states, (t.1 ∩ cl(φ)) = sf.1 → 
            (tilde ha (phi_X_set ha φ X)) ∈ (canonical_model_CLC ha).f.E.E (t) (G))
          -- condition G = N
          -- ∃t ∈ S, sf = tf and  ̃φX ∈ E(t)(N)
          (∃ t : (canonical_model_CLC ha).f.states, (t.1 ∩ cl(φ)) = sf.1 ∧ 
            (tilde ha (phi_X_set ha φ X)) ∈ (canonical_model_CLC ha).f.E.E (t) (G))},
      liveness :=
      begin
        -- 1.1. First we note that  ̃φ∅ =  ̃⊥ = ∅.
        have hempty : (tilde ha (phi_X_set ha φ ∅)) = ∅, from
        begin
          -- 1.1.1. φ∅ = ⊥, because φ∅ is an empty disjunction, thus  ̃φ∅ =  ̃⊥.
          simp[phi_X_set, phi_X, phi_X_list, finite_disjunction, tilde],
          -- 1.1.2.  ̃⊥ = ∅, because all s ∈ S are consistent.
          simp[eq_empty_iff_forall_not_mem],
          intro s,
          apply bot_not_mem_of_ax_consistent s.1 s.2.1,
        end,
        -- 1.2. Assume by contradiction ∅ ∈ Ef (sf )(G).
        intros sf G hf,
        cases (em (G = univ)),
        -- 1.3. Case: G ≠ N
        { -- 1.3.1. ∀t ∈ S, sf = tf ⇒  ̃φ∅ ∈ E(t)(G), from 1.2, by definition Ef
          simp[h] at hf,
          -- 1.3.2. ∀t ∈ S, sf = tf ⇒ ∅ ∈ E(t)(G), from 1.3.1 & 1.1
          rw hempty at hf,
          -- 1.3.3. ∅ ∈ E(s)(G), from 1.3.2
          cases (s_f_to_s ha φ sf) with s hs,
          specialize hf s hs,
          -- 1.3.4. ∅ /∈ E(s)(G) because E(s) is live.
          have hlive := (canonical_model_CLC ha).f.E.liveness s,
          -- 1.3.5. Contradiction from 1.3.3 & 1.3.4.
          exact hlive univ hf, },
        -- 1.4. Case: G = N
        { -- 1.4.1. ∃t ∈ S, sf = tf and  ̃φ∅ ∈ E(t)(N ), from 1.2, by definition Ef .
          -- 1.4.2. ∃t ∈ S, sf = tf and ∅ ∈ E(t)(N ), from 1.4.1 & 1.1.
          -- 1.4.3. ∀t, ∅ /∈ E(t)(N ) because E(t) is live.
          -- 1.4.4. Contradiction from 1.2.5 & 1.2.6.
          sorry, },
      end,
      safety :=
      begin
        sorry,
      end,
      N_max :=
      begin
        sorry,
      end,
      monoticity :=
      begin
        sorry,
      end,
      superadd :=
      begin
        sorry,
      end,
    },
    rel := λ i s, {t | {φ | K' (i) (φ) ∈ s.1.1} = {φ | K' (i) (φ) ∈ t.1.1}},
    rfl := by simp,
    sym := λ i s t ht, eq.symm ht,
    trans := λ i s t u hst htu, (rfl.congr htu).mp hst, },
  v := λ  n, {s | (formCLC.var n) ∈ s.1.1}, }

----------------------------------------------------------
-- Truth Lemma
----------------------------------------------------------
-- lemma truth_lemma_CL {agents : Type} (ha : nonempty agents) (φ : formCLC agents) 
-- (s : (canonical_model_CLK ha).f.states) : (s_entails_CLC (canonical_model_CLK ha) s φ) ↔ (φ ∈ s.1) :=
-- begin
--   -- This proof is by induction on φ.
--   induction' φ with n φ ψ _ _ φ ψ _ _,

--   { -- case bot
--     simp [s_entails_CLC],
--     exact @bot_not_mem_of_ax_consistent (formCLC agents) formulaCLC s.1 s.2.1, },

--   { -- case var
--     simpa, },

--   { -- case and
--     simp [s_entails_CLC, ih_φ, ih_ψ],
--     split,

--     { intro h,
--       exact max_ax_contains_by_set_proof_2h s.2 h.left h.right axCLC.Prop4, },

--     { intro h,
--       split,
--       exact max_ax_contains_by_set_proof s.2 h axCLC.Prop5,
--       exact max_ax_contains_by_set_proof s.2 h axCLC.Prop6, }, },

--   { -- case imp
--     simp [s_entails_CLC, ih_φ, ih_ψ],
--     split,

--     { intro h,
--       exact max_ax_contains_imp_by_proof s.2 h, },

--     { intros h hφ,
--       exact max_ax_contains_by_set_proof_2h s.2 hφ h likemp, }, },

--   { -- case E
--     let states := {Γ : (set (formCLC agents)) // (max_ax_consistent Γ)},
--     have hE : (canonical_model_CLK ha).f.E.E = λ s, λ G : set agents, {X | ite (G = univ) 
--       -- condition G = N
--       (∀ φ, ({t : (canonical_model_CLK ha).f.states | φ ∈ (t.val)} ⊆ Xᶜ) → ([(∅)] φ) ∉ s.val)      
--       -- condition G ≠ N
--       (∃ φ, {t : (canonical_model_CLK ha).f.states | φ ∈ (t.val)} ⊆ X ∧ ( [G] φ) ∈ s.val)},
--       from rfl,

--     specialize ih ha,
    
--     -- It is sufficient to consider the case when G ⊂ N, because ⊢ [N]φ ↔ ¬[∅]¬φ
--     cases set.eq_or_ssubset_of_subset (set.subset_univ G) with hG hG,
--     -- Case G = N 

--     { -- ⊢ [N]φ ↔ ¬[∅]¬φ
--       have hempty : axCLC (([univ]φ) ↔ ¬([∅](¬φ))), from 
--         @univ_iff_empty agents (formCLC agents) _ _ _,
--       simp [hG] at *, clear hG,

--       split,

--       { -- M s ⊨ [N] φ ⇒ [N] φ ∈ s
--         intro h,
--         simp[s_entails_CLC, hE] at h,
--         have hnin : ([∅] (¬φ)) ∉ s.val, from
--         begin
--           apply h (¬ φ),
--           apply @eq.subset _ _ {t | s_entails_CLC (canonical_model_CLK ha) t φ}ᶜ,
--           simp[ih],
--           exact complement_from_contra,
--         end,
--         simp at hnin,
        
--         have hin :  (¬[∅]¬φ) ∈ s.val, from not_in_from_notin s.2 hnin,
--         simp at hin,

--         exact max_ax_contains_by_set_proof s.2 hin (axCLC.MP (axCLC.Prop6) hempty), },

--       { -- [N] φ ∈ s ⇒ M s ⊨ [N] φ
--         intro h,
--         simp[s_entails_CLC, hE, ih],
--         intros ψ hsubseteq hf,
  
--         simp[set.subset_def] at hsubseteq,

--         have himp : ∀ (x : (canonical_model_CLK ha).f.states), ψ ∈ x.1 → (¬ φ) ∈ x.1, from
--           λ t ht, not_in_from_notin t.2 (hsubseteq t ht),
      
--         have hin : (¬ [∅] ¬φ) ∈ s.val, 
--           from max_ax_contains_by_set_proof s.2 h (axCLC.MP (axCLC.Prop5) hempty),

--         have hnin : ([∅] ¬φ) ∉ s.val, from 
--           λ hf, contra_containts_pr_false s.2 hf hin, 

--         have hax : axCLC (ψ ~> (¬ φ)), from
--           ax_imp_from_ex himp,

--         have hin' : ([∅] ¬ φ) ∈ s.val,
--         { apply max_ax_contains_by_set_proof s.2 hf,
--           apply @derived_monoticity_rule agents (formCLC agents),
--           exact hax, },

--         exact hnin hin', }, },

--     { -- Case G ⊂ N
--       split,
--       -- M, s ⊨ [G]φ ⇒ [G]φ ∈ s, when G ⊂ N

--       { -- Assume M, s ⊨ [G]φ
--         intro h,
--         -- {s ∈ S| M, s ⊨ φ} ∈ E(s)(G), from h, by definition ⊨
--         simp[s_entails_CLC] at h,
--         -- ∃ψ˜ ⊆ {t ∈ S| M, t ⊨ φ} : [G]ψ ∈ s, from above, by definition E
--         have huniv : G ≠ univ, from (set.ssubset_iff_subset_ne.mp hG).right,
--         simp[hE, huniv] at h, clear huniv,
--         -- ∃ψ˜ ⊆ {t ∈ S| M, φ ∈ t} : [G]ψ ∈ s, from above, by IH
--         cases h with ψ hψ, 
--         have hψih : ∀ (a : (canonical_model_CLK ha).f.states), ψ ∈ ↑a → φ ∈ a.val, from
--           begin
--             intros t ht, 
--             apply (ih t).mp, 
--             apply hψ.left, 
--             exact ht,
--           end,
--         -- ∃ψ˜ ⊆ φ˜ : [G]ψ ∈ s, from hih, by definition ψ˜
--         have hGψ : ([G]ψ) ∈ s.val, from hψ.right,
--         -- ⊢ ψ → φ, since ψ˜ ⊆ φ˜ in hψih 
--         have himp : axCLC (ψ ~> φ), from ax_imp_from_ex hψih,
--         -- ⊢ [G]ψ → [G]φ, from himp, by the derived monoticity rule
--         have hGimp : axCLC (([G] ψ) ~> ([G] φ)), from 
--           @derived_monoticity_rule agents (formCLC agents) formulaCLC CLformulaCLC _ _ _ himp,
--         -- [G]φ ∈ s, from hGimp and hGψ
--         exact max_ax_contains_by_set_proof s.2 hGψ hGimp, },
--       -- [G]φ ∈ s ⇒ M, s ⊨ [G]φ, when G ⊂ N

--       { -- Assume [G]φ ∈ s
--         intro h,
--         -- ˜φ ⊆ {t ∈ S| φ ∈ t} : [G]φ ∈ s, from 4.1
--         simp[s_entails_CLC],
--         -- {t ∈ S| φ ∈ t} ∈ E (s)(G), from 4.2, by definition E(s)(G).
--         simp[hE, (set.ssubset_iff_subset_ne.mp hG).right],
--         apply exists.intro φ,
--         -- {t ∈ S | M, t ⊨ φ} ∈ E(s)(G), from 4.3, by IH
--         split,

--         { intros t ht,
--           simp[ih t],
--           exact ht, },

--         { exact h, }, }, }, },
--   -- case K
--   { have hK : (canonical_model_CLK ha).f.rel = λ i s, {t | {φ | (K' i φ) ∈ s.1} = {φ | (K' i φ) ∈ t.1}},
--       from rfl,
--     split,
--     -- ⇒
--     { intro h,
--       simp at *, 
--       simp [s_entails_CLC] at h,
--       simp [hK] at *,
--       have hφ : φ ∈ s.1, 
--       { simp [←(ih a s)],
--         apply h,
--         simp, },
--       have hkj : ∀ t : (canonical_model_CLK ha).f.to_frameCL.states, 
--         {φ : formCLC agents | K' a φ ∈ ↑s} = {φ : formCLC agents | K' a φ ∈ ↑t} → φ ∈ t.1,
--       {
--         intros t ht,
--         simp [←(ih a t)],
--         apply h,
--         exact ht,
--       },
--       dsimp at *,
--       -- have (K' i φ) ∈ s,
      
--       -- simp [ih] at h,
--       sorry,
--       -- simp [(ih i)] at h,

--     },
--     { intro h,
--       simp[s_entails_CLC, ih, hK],
--       intros t ht,
--       have hKt: K' a φ ∈ t.val, from
--       begin 
--         simp[set.ext_iff] at ht,
--         specialize ht φ,
--         simp[←ht],
--         exact h,
--       end,
--       exact max_ax_contains_by_set_proof t.2 hKt axCLC.T, }, },


-- end




----------------------------------------------------------
-- Completeness
----------------------------------------------------------

-- Completeness
----------------------------------------------------------
-- theorem completenessCLC (φ : formCLC agents) (ha : nonempty agents) : 
--   global_valid φ → axCLC φ :=
-- begin
--   -- rw from contrapositive
--   rw ←not_imp_not, 
--   -- assume ¬ ⊢ φ
--   intro hnax,
--   -- from ¬ ⊢ φ, have that {¬ φ} is a consistent set
--   have hax := @comphelper agents (formCLC agents) formulaCLC φ (nprfalseCLC ha) hnax,
--   -- with Lindenbaum, extend {¬ φ} into a maximally consistent set
--   have hmax := lindenbaum {¬φ} hax,
--   simp at *, 
--   cases hmax with s hmax, 
--   cases hmax with hmax hnφ,
--   -- show that φ is not globally valid, 
--   -- by showing that there exists some model where φ is not valid.
--   simp[global_valid],
--   -- let that model be the canonical model
--   apply exists.intro (canonical_model_CLK ha),
--   -- in the canonical model (M) there exists some state (s) where ¬ M s ⊨ φ
--   simp[valid_m],
--   -- let that state (s) be the maximally consistent set extended from {¬ φ}
--   apply exists.intro (subtype.mk s hmax),
--   -- assume by contradiction that M s ⊨ φ
--   intro hf,
--   -- by the truth lemma φ ∈ s
--   have hφ, from (truth_lemma_CL ha φ (subtype.mk s hmax)).mp hf,
--   -- in that state (s), φ ∈ s, so we do not have ¬ φ ∈ s (by consistency)
--   -- contradiction with hnφ
--   apply contra_containts_pr_false hmax hφ hnφ,
-- end

end canonical