import soundness.soundnessCLC
import completeness.canonicalCL
import syntax.axiomsCLC
import tactic.induction
import data.finset.powerset


local attribute [instance] classical.prop_decidable

open set formCLC

namespace canonical


----------------------------------------------------------
-- Canonical CL Model (not a valid CLC model)
----------------------------------------------------------
def canonical_model_CLC {agents : Type} [hN : fintype agents] (ha : nonempty agents) : 
  modelCLK agents :=
{ f := canonical_CLK ha (formCLC agents) (nprfalseCLC ha),
  -- V is as usual, such that s ∈ V (p) iff p ∈ s
  v := λ  n, {s | (formCLC.var n) ∈ s.1} }

----------------------------------------------------------
-- Filtration closure cl
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

----------------------------------------------------------
-- Filtering S
----------------------------------------------------------
-- Definitions about Sf
----------------------------------------------------------
def S_f {agents : Type} [hN : fintype agents] (ha : nonempty agents) (φ : formCLC agents) : Type :=
finset.attach (finset.filter (λ sf, ∃ s: (canonical_model_CLC ha).f.states, (s.1 ∩ {x | x ∈ cl(φ)}) = {x | x ∈ sf}) (finset.powerset (cl(φ))))

-- get sf from s
noncomputable def s_f {agents : Type} [hN : fintype agents] (ha : nonempty agents) 
  (φ : formCLC agents) (s : (canonical_model_CLC ha).f.states) : 
  (S_f ha φ) :=
begin
  fconstructor,
  fconstructor,
  exact finset.filter (λ ψ, ψ ∈ s.1) (cl(φ)),
  simp,
  apply exists.intro s,
  exact s.1.inter_comm ↑(cl φ),
  simp,
end

-- for each sf, there exists some s which filters to sf
def s_f_to_s {agents : Type} (ha : nonempty agents) [hN : fintype agents] (φ : formCLC agents) 
  (sf : (S_f ha φ)) :
  ∃ s: (canonical_model_CLC ha).f.states, (s.1 ∩ {x | x ∈ cl(φ)}) = {x | x ∈ sf.1.1} :=
begin
  cases sf.1 with sfin hsf,
  dsimp[finset.powerset, finset.filter] at *,
  simp at *,
  exact hsf.right,
end

-- Lemmas about Sf
----------------------------------------------------------
-- Sf is  finite
noncomputable lemma fin_S_f {agents : Type} [hN : fintype agents] (ha : nonempty agents) 
  (φ : formCLC agents) : 
  fintype (S_f ha φ) :=  additive.fintype

-- Sf is not empty
lemma nonempty_S_f {agents : Type} [hN : fintype agents] (ha : nonempty agents) 
  (φ : formCLC agents) : 
  nonempty (S_f ha φ) :=  
begin
  -- simp[S_f, finset.filter],
  have hs := (canonical_model_CLC ha).f.hs,
  cases hs with s,
  have sf := s_f ha φ s,
  exact nonempty.intro sf,
end

-- sf ⊆ s
lemma s_f_subset_s {agents : Type} (ha : nonempty agents) [hN : fintype agents] 
  (φ : formCLC agents) (s : (canonical_model_CLC ha).f.states) :
  {x | x ∈ (s_f ha φ s).1.1} ⊆ s.1 :=
begin
  simp[s_f],
  apply inter_subset_right,
end

-- sf ⊆ cl φ
lemma s_f_cl {agents : Type} (ha : nonempty agents) [hN : fintype agents] 
  (φ : formCLC agents) (sf : (S_f ha φ)) : 
  sf.1.1 ⊆ cl φ :=
begin
  have hs := s_f_to_s ha φ sf,
  cases hs with s hs,
  simp at *,
  rw finset.subset_iff,
  intros x hx,
  cases sf,
  cases sf_val,
  simp at *,
  sorry,
  
  
end

-- all sf are consistent
lemma s_f_ax {agents : Type} (ha : nonempty agents) [hN : fintype agents] 
  (φ : formCLC agents) (sf : (S_f ha φ)) : 
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

-- sf = tf iff they have the same finset
lemma s_f_eq {agents : Type} (ha : nonempty agents) [hN : fintype agents] 
  (φ : formCLC agents) (sf tf : (S_f ha φ)) : 
  sf = tf ↔ sf.1.1 = tf.1.1 :=
begin
  split,
   repeat 
   { intro h,
    cases sf, cases tf,
    cases sf_val, cases tf_val,
    simp at *,
    exact h, },
end



----------------------------------------------------------
-- Definitions and Lemmas needed for completness / model construction
----------------------------------------------------------
-- Tilde
----------------------------------------------------------
def tilde {agents : Type} [hN : fintype agents] (ha : nonempty agents) (ψ : formCLC agents): 
  set ((canonical_model_CLC ha).f.states) :=
{s : (canonical_model_CLC ha).f.states | ψ ∈ s.1}

-- phi sf
----------------------------------------------------------
noncomputable def phi_s_f {agents : Type} [hN : fintype agents] (ha : nonempty agents) 
  (φ : formCLC agents) (sf : S_f ha φ) :
  formCLC agents :=
finite_conjunction (finset.to_list (sf.1.1))

-- phi sf ∈ s
lemma phi_s_f_in_s {agents : Type} [hN : fintype agents] (ha : nonempty agents) (φ : formCLC agents)
  (s : (canonical_model_CLC ha).f.states):
  phi_s_f ha φ ((s_f ha φ s)) ∈ s.1 :=
begin
  simp[phi_s_f],
  have hinduct : ∀ fs : list (formCLC agents), 
    (fs ⊆ (s_f ha φ s).1.1.to_list) → finite_conjunction fs ∈ s.1, from
  begin
    intros fs hfs,
    induction fs with f fs ih,
    { simp[finite_conjunction], 
      exact max_ax_contains_by_empty_proof s.2 prtrue, },
    { simp[finite_conjunction] at *,
      cases hfs with hf hfs,
      have hf_in_s : f ∈ s.1, from s_f_subset_s ha φ s hf,
      have hfs_in_s : finite_conjunction fs ∈ s.1, from ih hfs,
      apply max_ax_contains_by_set_proof_2h s.2 hf_in_s hfs_in_s,
      exact axCLC.Prop4, },
  end,
  apply hinduct,
  simp,
end

-- phi X (given a list)
----------------------------------------------------------
noncomputable def phi_X_list {agents : Type} [hN : fintype agents] (ha : nonempty agents) 
  (φ : formCLC agents) :
  list (S_f ha φ) → list (formCLC agents)
| list.nil   := list.nil
| (sf :: ss) := ((phi_s_f ha φ sf) :: phi_X_list ss)

-- if sf ∈ X, then phi sf is one of the disjuncts in phi X.
lemma phi_X_list_contains {agents : Type} [hN : fintype agents] (ha : nonempty agents) 
  (φ : formCLC agents) (sfs : list (S_f ha φ)) (sf : (S_f ha φ)) (hs : sf ∈ sfs) :
  (phi_s_f ha φ sf) ∈ phi_X_list ha φ sfs :=
begin
  induction sfs with hd sfs ih,
  {by_contradiction, simp at *, exact hs, },
  { cases hs,
    { simp[hs, phi_X_list], },
    { simp[phi_X_list] at *,
      apply or.intro_right,
      exact ih hs, }, },
end

lemma phi_X_list_subset {agents : Type} [hN : fintype agents] (ha : nonempty agents) 
  (φ : formCLC agents) (sfs : list (S_f ha φ)) (sfs' : list (S_f ha φ)) (h : sfs ⊆ sfs') :
  phi_X_list ha φ sfs ⊆ phi_X_list ha φ sfs' :=
begin
  induction sfs with hd sfs ih,
  { simp[phi_X_list] at *, },
  { simp[phi_X_list] at *,
    split,
    { exact phi_X_list_contains ha φ _ _ h.left, },
    { exact ih h.right, }, },
end

-- phi X (given a finset)
----------------------------------------------------------
noncomputable def phi_X_finset {agents : Type} [hN : fintype agents] (ha : nonempty agents) 
  (φ : formCLC agents) (X : finset (S_f ha φ)) :
  formCLC agents :=
finite_disjunction (phi_X_list ha φ (finset.to_list X))

lemma phi_X_subset_Y_imp {agents : Type} [hN : fintype agents] (ha : nonempty agents) 
  (φ : formCLC agents) (X : finset (S_f ha φ)) (Y : finset (S_f ha φ)) (hXY : X ⊆ Y) :
  axCLC ((phi_X_finset ha φ X) →' (phi_X_finset ha φ Y)) :=
begin
  simp[phi_X_finset],
  apply imp_finite_disjunction_subset (phi_X_list ha φ X.to_list) ((phi_X_list ha φ Y.to_list)),
  apply phi_X_list_subset,
  intros f hf,
  rw finset.mem_to_list at *,
  exact hXY hf,
end

-- lemma phi_X_int_Y {agents : Type} [hN : fintype agents] (ha : nonempty agents) 
--   (φ : formCLC agents) (X : finset (S_f ha φ)) (Y : finset (S_f ha φ)) :
--   axCLC ((phi_X ha φ X) →' (phi_X ha φ Y) →' (phi_X ha φ (X ∩ Y))) :=
-- begin
--   simp[phi_X],
--   apply imp_finite_disjunction_subset (phi_X_list ha φ X.to_list) ((phi_X_list ha φ Y.to_list)),
--   apply phi_X_list_subset,
--   intros f hf,
--   rw finset.mem_to_list at *,
--   exact hXY hf,
-- end

-- phi X (given a set)
----------------------------------------------------------
noncomputable def phi_X_set {agents : Type} [hN : fintype agents] (ha : nonempty agents)  
  (φ : formCLC agents) (X : set (S_f ha φ)) :
  formCLC agents :=
begin
  simp[S_f, finset.attach] at X,
  have hX : finite X, from finite.of_fintype X,
  have X : finset (S_f ha φ), from finite.to_finset hX,
  exact phi_X_finset ha φ X,
end

lemma phi_X_set_subset_Y_imp {agents : Type} [hN : fintype agents] (ha : nonempty agents) 
  (φ : formCLC agents) (X : set (S_f ha φ)) (Y : set (S_f ha φ)) (hXY : X ⊆ Y) :
  axCLC ((phi_X_set ha φ X) →' (phi_X_set ha φ Y)) :=
begin
  simp[phi_X_set],
  apply phi_X_subset_Y_imp,
  exact finite.to_finset_mono.mpr hXY,
end

-- lemma phi_X_set_int_Y {agents : Type} [hN : fintype agents] (ha : nonempty agents) 
--   (φ : formCLC agents) (X : set (S_f ha φ)) (Y : set (S_f ha φ)) :
--   axCLC ((phi_X_set ha φ X) →' (phi_X_set ha φ Y) →' (phi_X_set ha φ (X ∩ Y))) :=
-- begin
--   simp[phi_X_set],
--   apply phi_X_subset_Y_imp,
--   exact finite.to_finset_mono.mpr hXY,
-- end

-- Main Lemmas
----------------------------------------------------------
-- Lemma 4. ⊢ (∨ {sf ∈Sf } φsf)
lemma univ_disjunct_provability {agents : Type} [hN : fintype agents] (ha : nonempty agents)  
  (φ : formCLC agents) (hs : nonempty (S_f ha φ)):
  axCLC (phi_X_set ha φ (univ : set (S_f ha φ))) :=
begin
  -- 1. By contradiction, assume that ⊬ (∨ {sf ∈Sf } φsf)
  by_contradiction,
  -- 2. ∃t ∈ S, (∨ {sf ∈Sf } φsf) ∉ t, from 1.
  -- 3. ¬(∨ {sf ∈Sf } φsf) ∈ t, because t is maximally consistent, from 2.
  have hax := @comphelper agents (formCLC agents) formulaCLC 
  (phi_X_set ha φ (univ : set (S_f ha φ))) (nprfalseCLC ha) h,
  have hexn := lindenbaum {¬' (phi_X_set ha φ (univ : set (S_f ha φ)))} hax,
  cases hexn with t' hexn,
  let t := (⟨t', hexn.left⟩ : (canonical_model_CLC ha).f.states),
  have htn : ¬' (phi_X_set ha φ univ) ∈ t.1, from by tauto,
  -- 4. ⊢ φtf → (∨ {sf ∈Sf } φsf ), by propositional logic, because t ∈ Sf.
  have himp : ax (phi_s_f ha φ (s_f ha φ t) →' phi_X_set ha φ univ), from
  begin
    simp[phi_X_set, phi_X_finset],
    apply @imp_finite_disjunction (formCLC agents) formulaCLC (phi_s_f ha φ (s_f ha φ t)),
    simp at *,
    apply phi_X_list_contains ha φ,
    simp,
  end,
  -- 5. φtf∈ t, by propositional logic, because all ∀ψ ∈ tf , ψ ∈ t).
  have hphitf : phi_s_f ha φ (s_f ha φ t) ∈ t.1, from phi_s_f_in_s ha φ t, 
  -- 6. (∨{sf ∈Sf } φsf) ∈ t, by propositional logic, from 4 & 5.
  have ht : phi_X_set ha φ (univ : set (S_f ha φ)) ∈ t.1, 
    from max_ax_contains_by_set_proof t.2 hphitf himp,
  -- 7. Contradiction from 3 and 6.
  apply contra_containts_pr_false t.2 ht htn,
  end

-- Lemma 5. ∀sf , tf ∈ Sf , sf ̸ = tf ⇒⊢ φsf→ ¬φtf
lemma unique_s_f {agents : Type} [hN : fintype agents] [ha : nonempty agents]  
  {φ : formCLC agents} (sf  tf : (S_f ha φ)) (hneq : sf ≠ tf) :
  axCLC (phi_s_f ha φ sf →' ¬' (phi_s_f ha φ tf)) :=
  begin
    -- 1. Assume by contradiction ⊬ φsf → ¬φtf
    by_contradiction,
    -- 2. ∃u ∈ S, (φsf → ¬φtf) /∈ u, from 1.
    -- 3. ¬(φsf→ ¬φtf) ∈ u, from 2.
    have hax := @comphelper agents (formCLC agents) formulaCLC 
    (phi_s_f ha φ sf →' ¬' (phi_s_f ha φ tf)) (nprfalseCLC ha) h,
    have hexn := lindenbaum {¬' (phi_s_f ha φ sf →' ¬' (phi_s_f ha φ tf))} hax,
    cases hexn with u' hexn,
    let u := (⟨u', hexn.left⟩ : (canonical_model_CLC ha).f.states),
    have hun : ¬' (phi_s_f ha φ sf →' ¬' (phi_s_f ha φ tf)) ∈ u.1, from by tauto,
    -- 4. φsf ∧ φtf ∈ u, by propositional logic, from 3.
    have hand : (phi_s_f ha φ sf ∧' (phi_s_f ha φ tf)) ∈ u.1, 
      from max_ax_contains_by_set_proof u.2 hun demorgans'',
    -- 5. ∃χ ∈ sf ∪ tf , χ /∈ sf ∨ χ /∈ tf , because sf and tf are not identical.
    have hneq' : ∃ f ∈ (sf.1.1 ∪ tf.1.1), (f ∉ sf.1.1) ∨ (f ∉ tf.1.1), from
    begin
      cases em (sf.1.1 ⊆ tf.1.1) with hsf hsf,
      { have hsf := eq_or_ssubset_of_subset hsf,
        cases hsf with hsf hsf,
      { by_contradiction,
        rw ←s_f_eq at hsf,
        exact hneq hsf, },
      { have hsf := finset.exists_of_ssubset hsf,
        cases hsf with f hsf,
        cases hsf with hfin hfnin,
        apply exists.intro f,
        simp,
        split,
        { apply or.intro_right, exact hfin, },
        { apply or.intro_left, exact hfnin, }, }, },
      { by_contradiction heq,
        apply hsf,
        rw finset.subset_iff,
        intros f hf,
        simp at heq,
        specialize heq f,
        by_contradiction hnt,
        apply heq,
        { apply or.intro_left, exact hf, },
        { apply or.intro_right, exact hnt, }, },
    end,
    -- 6. χ /∈ s ∨ χ /∈ t, from 5, by definition Sf , because χ ∈ cl(φ).
    cases hneq' with x hneq',
    cases hneq' with hun hneq',
    have hx : x ∈ cl φ, from 
    begin
      simp at hun,
      cases hun,
      have hsf := sf.2,
      simp hsf[],
    end,
    cases hneq',
    { have hs := s_f_to_s ha φ sf,
      cases hs with s hs,
      -- 7. ¬χ ∈ s ∨ ¬χ ∈ t, from 6, because s and t are maximally consistent.
      -- 8. ∃ψ, (ψ ↔ ¬χ) ∧ (ψ ∈ cl(φ)), because cl is closed under single negations.
      -- 9. ψ ∈ s ∨ ψ ∈ t, from 7 & 8, because s and t are maximally consistent.
      -- 10. ψ ∈ sf ∨ ψ ∈ tf , from 8 & 9, by definition Sf .
      -- 11. φsf ∧ φtf → ⊥, by propositional logic, from 5, 8 & 10.
      -- 12. ⊥ ∈ u, by propositional logic, from 4 & 11, which contradicts the consistency of u.

    },

   
  end

----------------------------------------------------------
-- Playability
----------------------------------------------------------

def E_f {agents : Type}  [hN : fintype agents] (ha : nonempty agents) (φ : formCLC agents) : 
  (S_f ha φ) → (set agents) → (set (set (S_f ha φ))) := 
λ sf G, {X | ite (G = univ) 
  -- condition G = N
  -- ∃t ∈ S, sf = tf and  ̃φX ∈ E(t)(N)
  (∃ t : (canonical_model_CLC ha).f.states, (t.1 ∩ cl(φ)) = sf.1 ∧ 
    (tilde ha (phi_X_set ha φ X)) ∈ (canonical_model_CLC ha).f.E.E (t) (G))
  -- condition G ≠ N
  -- ∀t ∈ S, sf = tf ⇒  ̃phiX ∈ E(t)(G)
  (∀ t : (canonical_model_CLC ha).f.states, (t.1 ∩ cl(φ)) = sf.1 → 
    (tilde ha (phi_X_set ha φ X)) ∈ (canonical_model_CLC ha).f.E.E (t) (G))}

-- 1. Ef (sf ) is live: ∀G ⊆ N : ∅ /∈ Ef (sf )(G)
lemma Ef_liveness {agents : Type} [hN : fintype agents] (ha : nonempty agents) (φ : formCLC agents) :
  ∀ s : (S_f ha φ), ∀ G : set agents, ∅ ∉ (E_f ha φ s G) := 
begin
  -- 1.1. First we note that  ̃φ∅ =  ̃⊥ = ∅.
  have hempty : (tilde ha (phi_X_set ha φ ∅)) = ∅, from
  begin
    -- 1.1.1. φ∅ = ⊥, because φ∅ is an empty disjunction, thus  ̃φ∅ =  ̃⊥.
    simp[phi_X_set, phi_X_finset, phi_X_list, finite_disjunction, tilde],
    -- 1.1.2.  ̃⊥ = ∅, because all s ∈ S are consistent.
    simp[eq_empty_iff_forall_not_mem],
    intro s,
    apply bot_not_mem_of_ax_consistent s.1 s.2.1,
  end,
  -- 1.2. Assume by contradiction ∅ ∈ Ef (sf )(G).
  intros sf G hf,
  cases (em (G = univ)),
  -- 1.4. Case: G = N
  { -- 1.4.1. ∃t ∈ S, sf = tf and  ̃φ∅ ∈ E(t)(N), from 1.2, by definition Ef .
    simp[h] at hf,
    -- 1.4.2. ∃t ∈ S, sf = tf and ∅ ∈ E(t)(N), from 1.4.1 & 1.1.
    simp [E_f, hempty] at hf,
    cases hf with t hf,
    -- 1.4.3. ∀t, ∅ ∉ E(t)(N) because E(t) is live.
    have hlive := (canonical_model_CLC ha).f.E.liveness t univ,
    -- 1.4.4. Contradiction from 1.4.2 & 1.4.3.
    exact hlive hf.right, },
  -- 1.3. Case: G ≠ N
  { -- 1.3.1. ∀t ∈ S, sf = tf ⇒  ̃φ∅ ∈ E(t)(G), from 1.2, by definition Ef
    simp[E_f, h] at hf,
    -- 1.3.2. ∀t ∈ S, sf = tf ⇒ ∅ ∈ E(t)(G), from 1.3.1 & 1.1
    rw hempty at hf,
    -- 1.3.3. ∅ ∈ E(s)(G), from 1.3.2
    cases (s_f_to_s ha φ sf) with s hs,
    specialize hf s hs,
    -- 1.3.4. ∅ /∈ E(s)(G) because E(s) is live.
    have hlive := (canonical_model_CLC ha).f.E.liveness s,
    -- 1.3.5. Contradiction from 1.3.3 & 1.3.4.
    exact hlive G hf, },
end

-- 2. Ef (sf) is safe: ∀G ⊆ N : Sf ∈ Ef (sf )(G)
lemma Ef_safety {agents : Type} [hN : fintype agents] (ha : nonempty agents) (φ : formCLC agents) :
  ∀ (s : S_f ha φ) (G : set agents), univ ∈ E_f ha φ s G :=
begin
  -- 2.1. First we note that  ̃φSf =  ̃⊤ = S
  have huniv : (tilde ha (phi_X_set ha φ (univ : set (S_f ha φ)))) = (univ : set (canonical_model_CLC ha).f.states), from
  begin
    simp[tilde],
    ext1,
    refine iff_of_true _ trivial,
    simp,
    apply max_ax_contains_by_empty_proof x.2,
    apply univ_disjunct_provability,
    exact nonempty_S_f ha φ,
  end,
  -- 2.2. Additionally, because E(s) is safe for all s ∈ S, ∀G ⊆ N, S ∈ E(s)(G).
  have hsafe := (canonical_model_CLC ha).f.E.safety,
  -- 2.4. Case: G = N
  intros sf G, cases em (G = univ) with hG hG,
  { -- 2.4.1. Sf ∈ Ef (sf )(N ) iff ∃t ∈ S, sf = tf and  ̃φSf ∈ E(t)(N ), by definition Ef .
    simp[hG] at *,
    -- 2.4.2. Sf ∈ Ef (sf )(N ) iff ∃t ∈ S, sf = tf and S ∈ E(t)(N ), from 2.1 & 2.4.1.
    simp[E_f, huniv],
    -- 2.4.3. ∃t ∈ S, sf = tf and S ∈ E(t)(N ), when t = s, because sf = sf and S ∈ E(s)(N ), from 2.2.
    cases (s_f_to_s ha φ sf) with s hs,
    apply exists.intro s,
    -- 2.4.4. Sf ∈ Ef (sf )(N ), from 2.4.2 & 2.4.3s
    simp at *,
    split,
    exact hs,
    apply hsafe, },
  -- 2.3. Case: G ≠ N
  { -- 2.3.1. Sf ∈ Ef (sf )(G) iff ∀t ∈ S, sf = tf ⇒  ̃φSf ∈ E(t)(G), by definition Ef .
    simp[E_f, hG] at *,
    -- 2.3.2. Sf ∈ Ef (sf )(G) iff ∀t ∈ S, sf = tf ⇒ S ∈ E(t)(G), from 2.1 & 2.3.1.
    simp[huniv],
    -- 2.3.3. Sf ∈ Ef (sf )(G), from 2.2 & 2.3.2
    intros t ht,
    apply hsafe, }, 
end

-- 3. Ef (sf) is N-maximal: ∀X ⊆ Sf : Xᶜ ∉ Ef(sf)(∅) ⇒ X ∈ Ef(sf)(N)
lemma Ef_nmax {agents : Type} [hN : fintype agents] (ha : nonempty agents) (φ : formCLC agents) :
  N_max agents (S_f ha φ) (E_f ha φ) :=
begin
  -- 3.1. Assume some X ⊆ Sf such that Xᶜ ∉ Ef(sf)(∅).
  intros sf X hXc,
  -- 3.2. ¬(Xᶜ ∈ Ef sf ∅), from 3.1.
  simp[E_f] at *,
  -- 3.3. ¬(∀t ∈ S, sf = tf ⇒ ~φXᶜ ∈ E(t)(∅)), from 3.2, by definition Ef . 
  -- 3.4. ∃t ∈ S, sf = tf and ~φXᶜ ∉ E(t)(∅)), from 3.3, by first order logic. 
  have hempty_ne_univ : (∅ : set (agents)) ≠ (univ : set (agents)), from empty_ne_univ,
  simp[@empty_ne_univ agents ha] at *, -- clear hempty_ne_univ,
  cases hXc with t ht,
  cases ht with ht hXc,
  apply exists.intro t,
  split, 
  { exact ht, },
  -- 3.5. Note that ⊢ φXᶜ ↔ ¬φX , from Lemma 4 and Lemma 5.
  { 
    have h_tilde: tilde ha (¬ (phi_X_set ha φ X) : formCLC agents) = 
      tilde ha (phi_X_set ha φ Xᶜ), from
    begin
      simp[tilde],
      ext1 u,
      split,
      { intro hu,
        simp at *,
        apply max_ax_contains_by_set_proof u.2 hu,
        sorry,
      },
      { intro hu,
        simp at *,
        apply max_ax_contains_by_set_proof u.2 hu,
        sorry,
      }
    end,

    -- 3.6. ∃t ∈ S, sf = tf and ~¬φX ∉ E(t)(∅)), from 3.4 & 3.5
    have hX : tilde ha (¬ (phi_X_set ha φ X) : formCLC agents) ∉ 
      (canonical_model_CLC ha).f.to_frameCL.E.E t ∅, from
    begin
      simp[h_tilde] at *,
      exact hXc,
    end,  
    -- 3.7. ∃t ∈ S,sf = tf and (~φX)ᶜ ∉ E(t)(∅)), from 3.6, because all s ∈ S are maximally consistent.
    have h_tilde_eq : tilde ha (¬ (phi_X_set ha φ X)) = (tilde ha (phi_X_set ha φ X))ᶜ, from
    begin
      simp[tilde],
      rw (set.compl_def {s : (canonical_model_CLC ha).f.to_frameCL.states | phi_X_set ha φ X ∈ ↑s}),
      ext1,
      simp,
      split,
      { intros hx hf,
        exact contra_containts_pr_false x.2 hf hx, },
      { intros hx,
        exact not_in_from_notin x.2 hx, },
    end,
  simp at *,
  simp[h_tilde_eq] at hX,
    -- 3.8. ∃t ∈ S,sf = tf and φ􏰓 ∈ E(t)(N)), from 3.7, because E(s) is N-maximal X for all s ∈ S (∀X ⊆ S|X ∈/ E(s)(∅) ⇒ X ∈ E(s)(N))
    -- 3.9. Ef (sf )(N), from 3.8, by definition Ef .
  exact (canonical_model_CLC ha).f.to_frameCL.E.N_max t (tilde ha (phi_X_set ha φ X)) hX, },
end

-- Ef (sf ) is outcome monotonic: ∀G ⊆ N, ∀X ⊆ Y ⊆ Sf : X ∈ Ef (sf )(G) ⇒ Y ∈ Ef (sf )(G)
lemma Ef_monoticity {agents : Type} [hN : fintype agents] (ha : nonempty agents) (φ : formCLC agents) :
  ∀ (sf : S_f ha φ) (G : set agents) (X Y : set (S_f ha φ)), X ⊆ Y → X ∈ E_f ha φ sf G → Y ∈ E_f ha φ sf G :=
begin
  -- 4.1. Let G be some G ⊆ N and X and Y be some X ⊆ Y ⊆ Sf .
  intros s G X Y hXY,
  -- 4.2. Assume X ∈ Ef (sf )(G).
  intro hX,
  -- 4.3. First we note that ∀s ∈ S, ∀G ⊆ N,  ̃φX ∈ E(s)(G) ⇒  ̃φY ∈ E(s)(G)
  have himp : ∀ s G, 
    (tilde ha (phi_X_set ha φ X)) ∈ (canonical_model_CLC ha).f.E.E s G → 
    (tilde ha (phi_X_set ha φ Y)) ∈ (canonical_model_CLC ha).f.E.E s G, from
  begin
    -- 4.3.1. Let s be some s ∈ S and G be some G ⊆ N .
    clear hX, intros s G hX,
    -- 4.3.2. ⊢ φX → φY , from 4.1 (X ⊆ Y ).
    have hax : axCLC ((phi_X_set ha φ X) ~> (phi_X_set ha φ Y)), 
      from phi_X_set_subset_Y_imp _ _ _ _ hXY,
    -- 4.3.3.  ̃φX ⊆  ̃φY , from 4.3.2.
    have h_phiXY : (tilde ha (phi_X_set ha φ X)) ⊆ (tilde ha (phi_X_set ha φ Y)), from
    begin 
      rw set.subset_def,
      intros t ht,
      apply max_ax_contains_by_set_proof t.2 ht hax,
    end,
    -- 4.3.4. E(s) is outcome monotonic for all s ∈ S: ∀G ⊆ N, ∀X ⊆ Y ⊆ S, X ∈ E(s)(G) ⇒ Y ∈ E(s)(G)
    have hmonoticity := (canonical_model_CLC ha).f.E.monoticity s G _ _ h_phiXY,
    -- 4.3.5.  ̃φX ∈ E(s)(G) ⇒  ̃φY ∈ E(s)(G), from 4.3.3 & 4.3.4
    apply hmonoticity hX,
  end,
  -- 4.5. Case G = N
  cases em (G = univ) with hG hG,
  { -- 4.5.1. ∃t ∈ S, sf = tf and  ̃φX ∈ E(t)(N ), from 4.2, by definition Ef .
    simp[E_f, hG] at *,
    -- 4.5.2. ∃t ∈ S, sf = tf and  ̃φY ∈ E(t)(N ), from 4.3 & 4.5.1.
    -- 4.5.3. Y ∈ Ef (sf )(N ), from 4.5.2, by definition Ef . 
    cases hX with t ht,
    apply exists.intro t,
    split,
    { exact ht.1 },
    { exact himp _ _ ht.2, }, },
  -- 4.4. Case: G ≠ N
  { -- 4.4.1. ∀t ∈ S, sf = tf ⇒  ̃φX ∈ E(t)(N ), from 4.2, by definition Ef .
    simp[E_f, hG] at *,
    -- 4.4.2. ∀t ∈ S, sf = tf ⇒  ̃φY ∈ E(t)(N ), from 4.3 & 4.4.1.
    -- 4.4.3. Y ∈ Ef (sf )(G), from 4.4.2, by definition Ef .
    intros t ht,
    exact himp t G (hX t ht), },
end

--  Ef (sf ) is superadditive ∀G, F ⊆ N (where G ∩ F = ∅), 
  -- ∀X, Y ⊆ Sf : X ∈ Ef (sf )(G) and Y ∈ Ef (sf )(F ) ⇒ X ∩ Y ∈ Ef (sf )(G ∪ F )
lemma Ef_superadd {agents : Type} [hN : fintype agents] (ha : nonempty agents) (φ : formCLC agents) :
  ∀ (sf : S_f ha φ) (G F : set agents) (X Y : set (S_f ha φ)),
  X ∈ E_f ha φ sf G → Y ∈ E_f ha φ sf F → G ∩ F = ∅ → X ∩ Y ∈ E_f ha φ sf (G ∪ F) :=
begin      
  -- 5.1. Let G, F be some G, F ⊆ N , such that G ∩ F = ∅. Let X, Y be some
    -- X, Y ⊆ S such that X ∈ Ef (sf )(G) and Y ∈ Ef (sf )(F ).
  -- intros sf G F X Y hX hY hGF,
  -- 5.2. First we note that ∀s ∈ S, ∀G, F ⊆ N (where G ∩ F = ∅),  ̃φX ∈ E(s)(G) ⇒  ̃φY ∈ E(s)(F ) ⇒  ̃φX∩Y ∈ E(s)(G ∪ F )
  have hint : ∀ s G F X Y, G ∩ F = ∅ → 
    (tilde ha (phi_X_set ha φ X)) ∈ (canonical_model_CLC ha).f.E.E s G →
    (tilde ha (phi_X_set ha φ Y)) ∈ (canonical_model_CLC ha).f.E.E s F →
    (tilde ha (phi_X_set ha φ (X ∩ Y))) ∈ (canonical_model_CLC ha).f.E.E s (G ∪ F), from
  begin
    -- 5.2.1. Let s be some s ∈ S. Let G, F , be some G, F ⊂ N where G ∩ F = ∅. Assume  ̃φX ∈ E(s)(G) and  ̃φY ∈ E(s)(F ).
    intros s G F X Y hGF hG hF,
    -- 5.2.2. E(s) is superadditive so: ∀X, Y ⊆ S : X ∈ E(s)(G) and Y ∈ E(s)(F ) ⇒ X ∩ Y ∈ E(s)(G ∪ F )
    have hsuperadd := ((canonical_model_CLC ha).f.E.superadd) s G F,
    -- 5.2.3.  ̃φX ∩  ̃φY ∈ E(s)(G ∪ F ), from 5.2.1 & 5.2.2.
    specialize hsuperadd (tilde ha (phi_X_set ha φ X)) (tilde ha (phi_X_set ha φ Y)) hG hF hGF,
    -- 5.2.4.  ̃φX∩Y ∈ E(s)(G ∪ F ), from 5.2.3, because  ̃φX →  ̃φX∩Y and  ̃φY →  ̃φX∩Y .
    have h_tilde_eq : tilde ha (phi_X_set ha φ X) ∩ tilde ha (phi_X_set ha φ Y) = tilde ha (phi_X_set ha φ (X ∩ Y)), from
    begin
      ext1,
      simp[tilde],
      split,
      { 
        intro h,

        -- apply max_ax_contains_by_set_proof_2h x.2 h.left h.right,
        sorry,
        


      },
      { intro h,
        split,
        repeat 
        { apply max_ax_contains_by_set_proof x.2 h,
          apply phi_X_set_subset_Y_imp,
          simp, }, },
    end,
    
    rw h_tilde_eq at hsuperadd,
    exact hsuperadd,
  end,
  
  intros sf G F X Y hX hY hGF,

  -- 5.4. Case G = N or F = N :
  have h_G_or_F_univ : ∀ X' Y', X' ∈ E_f ha φ sf univ → Y' ∈ E_f ha φ sf ∅ → (X' ∩ Y') ∈ E_f ha φ sf univ, from
  begin
    -- 5.4.1. Rename G, F, X&Y to G′, F ′, X′&Y ′, such that G′ = N , F ′ = ∅, X′ ∈ Ef (sf )(G′) and Y ′ ∈ Ef (sf )(F ′).
    clear hX hY,
    intros X' Y',
    -- 5.4.2. ∃t ∈ S, sf = tf and  ̃φX′ ∈ E(t)(N ), from 5.4.1 (X′ ∈ Ef (sf )(G′)), by definition Ef .
    intro hX,
    -- 5.4.3. ∀t ∈ S, sf = tf ⇒  ̃φY ′ ∈ E(t)(∅), from 5.4.1 (Y ′ ∈ Ef (sf )(F ′)), by definition Ef .
    intro hY,
    -- 5.4.4. ∃t ∈ S, sf = tf and  ̃φX′ ∈ E(t)(N ) and  ̃φY ′ ∈ E(t)(∅), from 5.4.2 & 5.4.3.
    simp[E_f, empty_ne_univ] at *,
    cases hX with t hX,
    specialize hY t hX.left,
    apply exists.intro t,
    split, exact hX.left,
    -- 5.4.5. ∃t ∈ S, sf = tf and  ̃φX′ ∩Y ′ ∈ E(t)(N ), from 5.3 & 5.4.4.
    specialize hint t univ ∅ X' Y' (by simp) hX.right hY,
    simp[univ_union] at hint,
    exact hint,
  end,

  cases em (G = univ),
  { simp[h] at *,
    simp[hGF] at *,
    exact h_G_or_F_univ X Y hX hY, },
  -- case G ≠ N
  { cases em (F = univ),
    { simp[h_1] at *,
      simp[hGF] at *,
      rw inter_comm X Y,
      exact h_G_or_F_univ Y X hY hX, },
    -- 5.3. Case G ≠ N and F ≠ N
    { -- 5.3.1. ∀t ∈ S, sf = tf ⇒  ̃φX ∈ E(t)(G), from 5.1 (X ∈ Ef (sf )(G)), by definition Ef .
      -- 5.3.2. ∀t ∈ S, sf = tf ⇒  ̃φY ∈ E(t)(F ), from 5.1 (Y ∈ Ef (sf )(F )), by definition Ef .
      simp[E_f, h, h_1] at *,
      -- 5.3.3. ∀t ∈ S, sf = tf ⇒ (  ̃φX ∈ E(t)(G)and  ̃φY ∈ E(t)(F )), from 5.3.1 & 5.3.2.
      -- 5.3.4. ∀t ∈ S, sf = tf ⇒  ̃φX∩Y ∈ E(t)(G ∪ F ), from 5.2 & 5.3.3.

      -- 5.3.6. Case G ∪ F = N : sf = sf and  ̃φX∩Y ∈ E(s)(G ∪ F ), from 5.3.4. So X ∩ Y ∈ Ef (sf )(G ∪ F = N ), by definition Ef
      cases em (G ∪ F = univ),
      { have hs := s_f_to_s ha φ sf,
        cases hs with s hs,
        specialize hint s G F X Y hGF (hX s hs) (hY s hs),
        simp[h_2] at *,
        apply exists.intro s,
        split, exact hs, exact hint, },
      -- 5.3.5. Case G ∪ F ̸ = N : X ∩ Y ∈ Ef (sf )(G ∪ F ), from 5.3.4, by definition Ef
      { simp[h_2],
        intros t ht,
        exact hint t G F X Y hGF (hX t ht) (hY t ht), }, }, },
end

----------------------------------------------------------
-- Building the coplete filtered CLC model
----------------------------------------------------------
 
def filtered_model_CLC {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) :
  modelCLK agents := 
{ f := 
  { states := S_f ha φ,
    hs := nonempty_S_f ha φ,
    ha := ha,
    E := 
    
-- ∀u∈Sc if [u]=[s] then [φ ]c ∈Ec(u)(G) G̸=N
    { E          := E_f ha φ,
      liveness   := Ef_liveness ha φ,
      safety     := Ef_safety ha φ,
      N_max      := Ef_nmax ha φ,
      monoticity := Ef_monoticity ha φ,
      superadd   := Ef_superadd ha φ, },
    rel   := λ i s, {t | {φ | K' (i) (φ) ∈ s.1.1} = {φ | K' (i) (φ) ∈ t.1.1}},
    rfl   := by simp,
    sym   := λ i s t ht, eq.symm ht,
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