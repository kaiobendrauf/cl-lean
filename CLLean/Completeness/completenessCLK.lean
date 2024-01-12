/-
Authors: Kai Obendrauf
Following the paper "Coalition Logic with Individual, Distributed and Common Knowledge
by Thomas Ågotnes and Natasha Alechina
and the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley

This file contains the truth lemma for CLK, and from that the proof of completeness for CLK.
-/

import CLLean.Completeness.canonical_filtering
import CLLean.Completeness.closureCLK
import CLLean.Soundness.soundnessCLK
import CLLean.Syntax.CLKLemmas
import CLLean.Syntax.formula

open Set Classical Logic

namespace canonical

----------------------------------------------------------
-- Canonical Model CL
----------------------------------------------------------

@[simps!] noncomputable def Mf_CLK {agents : Type} [Nonempty agents] [Fintype agents]
  (φ : formCLK agents) : modelECL agents :=
filtered_modelECL agents (formCLK agents) nprfalseCLK cl cl_closed_single_neg φ


/-- Allows us to write `φ ∈ s` instead of `φ ∈ s` -/
instance Mf_CLK.f.states.SetLike {agents : Type} [ha : Nonempty agents] [hN : Fintype agents]
  {φ : formCLK agents} : SetLike ((Mf_CLK φ).f.states) (formCLK agents) :=
{ coe := λ s => s.1.1
  coe_injective' := by
    intro sf tf h
    simp only [Finset.setOf_mem, Finset.coe_inj, s_f_eq] at h
    exact h }

----------------------------------------------------------
-- Truth Lemma
----------------------------------------------------------

-- E
----------------------------------------------------------
-- Truth Lemma: case [G]ψ, where G = N :
lemma truth_E_univ {agents : Type} [ha : Nonempty agents] [hN : Fintype agents]
  {φ ψ : formCLK agents} {G : Set agents} (sf : (Mf_CLK φ).f.states)
  (hφ : ψ ∈ cl φ) (hφ' : (_[G] ψ) ∈ cl φ)
  (ih : ∀ tf, (s_entails_CLK (Mf_CLK φ) tf ψ) ↔ (ψ ∈ tf)) (hG : G = univ) :
  (s_entails_CLK (Mf_CLK φ) sf (_[G] ψ)) ↔ ((_[G] ψ) ∈ sf) := by
  let MC' := canonical_model_CL agents (formCLK agents) nprfalseCLK
  --  M f , sf ⊨ ψ
  calc
    (s_entails_CLK (Mf_CLK φ) sf (_[G]ψ))
    -- ↔ {sf ∈ Sf | M f , sf ⊨ ψ} ∈ Ef (sf )(N ), by definition ⊨
    ↔ {tf | s_entails_CLK (Mf_CLK φ) tf ψ} ∈ (Mf_CLK φ).f.E.E sf G := by
        simp only [s_entails_CLK, Mf_CLK_f_states, Mf_CLK_f_E_E]
    -- ↔ ∃t ∈ SC′, sf = tf and  ̃φ{sf ∈Sf |M f ,sf ⊨ψ} ∈ EC′(t)(N ), by definition Ef.
    _ ↔ ∃ t, (sf = s_f cl φ t) ∧
          tilde MC'.f.states (phi_X_set {sf | s_entails_CLK (Mf_CLK φ) sf ψ}) ∈ MC'.f.E.E t G := by
        simp only [Mf_CLK_f_states, hG, Mf_CLK_f_E_E, E_f, ite_true, mem_setOf_eq]
    -- ↔ ∃t ∈ SC′, sf = tf and  ̃φ{sf ∈Sf |ψ∈sf } ∈ EC′(t)(N ), by ih.
    _ ↔ ∃ t, (sf = s_f cl φ t) ∧ tilde MC'.f.states
          (phi_X_set {sf : (Mf_CLK φ).f.states | ψ ∈ sf}) ∈ MC'.f.E.E t univ := by
        simp only [Mf_CLK_f_states, ih, mem_mk, Finset.setOf_mem, hG]
        -- ↔ ∃t ∈ SC′, sf = tf and  ̃ψ ∈ EC′(t)(N ), by Lemma 6.
    _ ↔ ∃ t, (sf = s_f cl φ t) ∧ tilde MC'.f.states ψ ∈ MC'.f.E.E t (univ) := by
        have hiff : _⊢ ((phi_X_set {sf : (Mf_CLK φ).f.states | ψ ∈ sf}) _↔ ψ) :=
          phi_X_contains_iff_psi (cl_closed_single_neg φ) (hφ)
        have htilde := @tilde_ax_iff _ (formCLK agents) _ _ _ nprfalseCLK _ _ hiff
        rw [htilde]
    -- ↔ ∃t ∈ SC′, sf = tf and [N ] ψ ∈ t, by Lemma 7.
    _ ↔ ∃ t, (sf = s_f cl φ t) ∧ (_[univ] ψ) ∈ t := by
        simp only [Mf_CLK_f_states, E_s_contains_tilde_iff_E_in_s _ univ]
        exact Iff.rfl
    -- ↔ [N] ψ ∈ sf:= left to right because [N] ψ ∈ tf, and from right to left when s = t.
    _ ↔ (_[G] ψ) ∈ sf := by
        rw [hG] at hφ' ⊢
        apply Iff.intro
        · intro h
          obtain ⟨t, ⟨heq, h⟩⟩ := h
          exact (sf_eq_forall heq).mpr ⟨h, hφ'⟩
        · intro h
          obtain ⟨s, hs⟩ := s_f_to_s sf
          apply Exists.intro s
          exact ⟨sf_eq_s_f  @hs, (hs.mp h).left⟩

-- Truth Lemma: case [G]ψ, where G = N :
lemma truth_E_nuniv {agents : Type} [ha : Nonempty agents] [hN : Fintype agents]
  {φ ψ : formCLK agents} {G : Set agents} (sf : (Mf_CLK φ).f.states)
  (hφ : ψ ∈ cl φ) (hφ' : (_[G] ψ) ∈ cl φ)
  (ih : ∀ tf, (s_entails_CLK (Mf_CLK φ) tf ψ) ↔ (ψ ∈ tf)) (hG : G ≠ univ) :
  (s_entails_CLK (Mf_CLK φ) sf (_[G] ψ)) ↔ ((_[G] ψ) ∈ sf) := by
  let MC' := canonical_model_CL agents (formCLK agents) nprfalseCLK
  -- M f , sf ⊨ ψ
  calc
    (s_entails_CLK (Mf_CLK φ) sf (_[G]ψ))
    -- ↔ {sf ∈ Sf | M f , sf ⊨ ψ} ∈ Ef (sf )(G ), by definition ⊨
    ↔ {tf | s_entails_CLK (Mf_CLK φ) tf ψ} ∈ (Mf_CLK φ).f.E.E sf G := by
        simp only [s_entails_CLK, Mf_CLK_f_states, Mf_CLK_f_E_E]
    -- ↔ ∀t ∈ SC′, sf = tf and  ̃φ{sf ∈Sf |M f ,sf ⊨ψ} ∈ EC′(t)(G ), by definition Ef .
    _ ↔ ∀ t, (sf = s_f cl φ t) →
          tilde MC'.f.states (phi_X_set {sf | s_entails_CLK (Mf_CLK φ) sf ψ}) ∈ MC'.f.E.E t G := by
        simp only [Mf_CLK_f_states, Mf_CLK_f_E_E, E_f, hG, ite_false, mem_setOf_eq]
        -- simp only [hG, if_false]
    -- ↔ ∀t ∈ SC′, sf = tf ⇒  ̃φ{sf ∈Sf |ψ∈sf } ∈ EC′(t)(G ), by ih.
    _ ↔ ∀ t, (sf = s_f cl φ t) →
          tilde MC'.f.states (phi_X_set {sf : (Mf_CLK φ).f.states | ψ ∈ sf}) ∈ MC'.f.E.E t G := by
        simp only [Mf_CLK_f_states, ih, mem_mk, Finset.setOf_mem]
    -- ↔ ∀t ∈ SC′, sf = tf ⇒  ̃ψ ∈ EC′(t)(G ), by Lemma 6.
    _ ↔ ∀ t, (sf = s_f cl φ t) →  tilde MC'.f.states ψ ∈ MC'.f.E.E t G := by
        have hiff : _⊢ ((phi_X_set {sf : (Mf_CLK φ).f.states | ψ ∈ sf}) _↔ ψ) :=
           phi_X_contains_iff_psi (cl_closed_single_neg φ) (hφ)
        have htilde := @tilde_ax_iff _ (formCLK agents) _ _ _ nprfalseCLK _ _ hiff
        rw [htilde]
    -- ↔ ∀t ∈ SC′, sf = tf ⇒ [G ]ψ ∈ t, by Lemma 7.
    _ ↔ ∀ t, (sf = s_f cl φ t) → (_[G] ψ) ∈ t := by
        simp only [E_s_contains_tilde_iff_E_in_s _ G]
        exact Iff.rfl
    -- ↔ [G] ψ ∈ sf := left to right when s = t:= right to left because [G]ψ ∈ sf = tf
    _ ↔ ((_[G] ψ) ∈ sf) := by
        apply Iff.intro
        · intro h
          obtain ⟨s, hs⟩ := s_f_to_s sf
          specialize h s (Eq.symm (s_f_eq_sf @hs))
          apply hs.mpr
          exact ⟨h, hφ'⟩
        · intro h t ht
          exact ((sf_eq_forall ht).mp h).1

-- K
----------------------------------------------------------
-- Truth Lemma: case Kiψ ⇒ : (M f , sf ⊨ Kiψ ⇒ Kiψ ∈ sf ) :
lemma truth_K_lr {agents : Type} [ha : Nonempty agents] [hN : Fintype agents]
  {φ ψ : formCLK agents} {i : agents} (sf : (Mf_CLK φ).f.states)
  (hφ' : (_K i ψ) ∈ cl φ) (ih : ∀ tf, (s_entails_CLK (Mf_CLK φ) tf ψ) ↔ (ψ ∈ tf)) :
  (s_entails_CLK (Mf_CLK φ) sf (_K i ψ)) → ((_K i ψ) ∈ sf) :=  by
  obtain ⟨s, hs⟩ := s_f_to_s sf
  -- 1. Let M f , sf ⊨ Kiψ.
  intro h
  -- 2. ∀tf ∈ Sf , sf ∼fi tf ⇒ M f , tf ⊨ ψ:= 1, by definition ⊨.
  unfold s_entails_CLK at h
  -- 3. ∀tf ∈ Sf , sf ∼fi tf ⇒ ψ ∈ tf := 2, by ih.
  simp only [Mf_CLK_f_states, Mf_CLK_f_rel, mem_setOf_eq] at h
  -- 4. Assume by contradiction that Kiψ ∉ sf .
  by_contra hnin
  -- 5. ¬Kiψ ∈ s:= 4, because s is maximally consistent.
  have hnin : _K i ψ ∉ s := (s_n_contains @hs) (hφ') hnin
  -- 6. Consider the Set Σ = {χ | Kiχ ∈ s}.
  let Γ := {χ | _K i χ ∈ s }
  -- 7. Σ ∪ {¬ψ} is consistent.
  have hcon : ax_consistent (Γ ∪ {_¬ ψ}) := by
      -- 7.1. Assume by contradiction Σ ∪ {¬ψ} is inconsistent.
      by_contra hncon
      -- 7.2. ⊢ (∧χ∈Σ χ) → ψ:= 7.1, by propositional logic.
      obtain ⟨ψs, ⟨hΓ, hax⟩⟩ := inconsistent_prove_neg hncon
      -- 7.3. ⊢ Ki((∧χ∈Σ χ) → ψ):= 7.2, by Axiom RN.
      have hKimp : _⊢ (_K i ((finite_conjunction ψs) _→ ψ)):= by
        apply axCLK.RN
        apply @cut (formCLK agents)
        exact hax
        exact dne
      -- 7.4. ⊢ (Ki(∧χ∈Σ χ)) → (Kiψ):= 7.3, by Axiom K.
      have hKimp : _⊢ ((_K i (finite_conjunction ψs)) _→ K' i ψ) := by
        apply axCLK.MP axCLK.K hKimp
      -- 7.5. ⊢ (∧χ∈Σ Kiχ) → (Kiψ):= 7.4, by propositional logic and Axiom RN.
      have hKimp : _⊢ ((finite_conjunction (List.map (_K i) ψs)) _→ _K i (ψ)):= by
        apply @cut (formCLK agents)
        apply @knows_conjunction agents (formCLK agents)
        exact hKimp
      -- 7.6. (∧χ∈Σ Kiχ) ∈ s, by definition Σ:= 6.
      have hin : (finite_conjunction (List.map (_K i) ψs)) ∈ s := by
        apply max_ax_contains_conj s.2
        intro φ hφ
        obtain ⟨χ, hχ⟩ := List.mem_map.mp hφ
        rw [←hχ.2]
        exact mem_setOf_eq.mp (hΓ χ hχ.1)
      -- 7.7. Kiψ ∈ s:= 7.5 & 7.6.
      have hK : _K i ψ ∈ s := by
        apply max_ax_contains_by_set_proof s.2 hin hKimp
      -- 7.8. Contradiction from 5 and 7.7.
      exact hnin hK
  -- 8. ∃t ∈ SC′, Σ ∪ {¬ψ} ⊆ t:= 7, because SC′ is maximally consistent.
  obtain ⟨t', hmax, hsub⟩ := lindenbaum hcon
  obtain ⟨t, ht⟩ :
    ∃ t : (canonical_model_CL agents (formCLK agents) nprfalseCLK).f.states, t = ⟨t', hmax⟩ :=
      exists_apply_eq_apply _ _
  rw [union_subset_iff] at hsub
  -- Note that ¬ψ ∈ t.
  have hnψ : (_¬ ψ) ∈ t :=  by
    rw [ht]
    apply singleton_subset_iff.mp hsub.2
   -- 9. sf ∼fi tf.
  obtain ⟨tf, htf⟩ := s_to_s_f cl φ t
  have hrel : tf ∈ (Mf_CLK φ).f.rel i sf:= by
    ext1 x
    apply Iff.intro
    -- 9.1 ∀ χ, K i χ ∈ sf → K i χ ∈ tf.
    · simp only [mem_setOf_eq, htf, ht, hs]
      intro hks
      apply And.intro
      · apply mem_of_mem_of_subset _ hsub.1
        simp only [mem_setOf_eq]
        -- Then K i K i χ ∈ s, by Axiom 4. So K i χ ∈ Σ, by definition Σ and K i χ ∈ t, by 8.
        apply max_ax_contains_by_set_proof s.2 hks.1 axCLK.Four
      · exact hks.2
    -- 9.2 ∀ χ, K i χ ∈ tf → K i χ ∈ sf.
    · simp only [mem_setOf_eq, htf, hs]
      intro hkt
      apply And.intro
      · -- Assume by contradiction that K i χ ∈ tf, and K i χ ∉ sf.
        by_contra hnks
        have := contra_contains_pr_false t.2 hkt.1
        simp only at this
        apply this
        rw [ht]
        -- Then K i (¬ K i χ) ∈ s, by Axiom 5.
        have hknks : _K i (_¬ _K i x) ∈ s.val :=
          max_ax_contains_by_set_proof s.2 (not_in_from_notin s.2 hnks) axCLK.Five
        --  So ¬ K i χ ∈ Σ, by definition Σ and ¬ K i χ ∈ t, by 8. Contradiction.
        have hnkΓ : (_¬ _K i x) ∈ Γ:= hknks
        exact mem_of_mem_of_subset hnkΓ hsub.1
      · exact hkt.2
  -- 10. ψ ∈ t := 3 and 9
  have hψ : ψ ∈ t := (htf.mp ((ih tf).mp (h tf hrel))).1
  -- 11. Contradiction from 8 & 10.
  have := contra_contains_pr_false t.2 hψ hnψ
  simp only at this

-- Truth Lemma: case Kiψ ⇐ : (Kiψ ∈ sf ⇒ M f , sf ⊨ Kiψ) :
lemma truth_K_rl {agents : Type} [ha : Nonempty agents] [hN : Fintype agents]
  {φ ψ : formCLK agents} {i : agents} (sf : (Mf_CLK φ).f.states)
  (hφ : ψ ∈ cl φ) (ih : ∀ tf, (s_entails_CLK (Mf_CLK φ) tf ψ) ↔ (ψ ∈ tf)) :
  ((_K i ψ) ∈ sf) → (s_entails_CLK (Mf_CLK φ) sf (_K i ψ)) :=  by
  -- 1. Let Kiψ ∈ sf .
  intro h
  -- 2. ∀tf ∈ Sf, sf ∼fi tf ⇒ Kiψ ∈ tf := 1, by definition ∼fi .
  have hfaK : ∀ tf, tf ∈ (Mf_CLK φ).f.rel i sf → _K i ψ ∈ tf :=
    λ _ htf => (Set.ext_iff.mp htf ψ).mp h
  -- 3. ∀tf ∈ Sf , sf ∼fi tf ⇒ ψ ∈ tf := 2, by Axiom T.
  have hfa : ∀ tf, tf ∈ (Mf_CLK φ).f.rel i sf → ψ ∈ tf:= by
    intro tf htf
    obtain ⟨t, ht⟩ := s_f_to_s tf
    specialize hfaK tf htf
    rw [ht] at hfaK ⊢
    apply And.intro
    · apply max_ax_contains_by_set_proof t.2 hfaK.1 axCLK.T
    · exact hφ
  -- 4. ∀tf ∈ Sf , sf ∼fi tf ⇒ M f , tf ⊨ ψ:= 3, by ih.
  have hent : ∀ tf, tf ∈ (Mf_CLK φ).f.rel i sf → (s_entails_CLK (Mf_CLK φ) tf ψ) :=
    λ tf htf => (ih tf).mpr (hfa tf htf)
  -- 5. M f , sf ⊨ Kiψ, by the definition of ⊨:= 4.
  exact hent


-- Truth Lemma
----------------------------------------------------------
lemma truth_lemma_CLK {agents : Type} [ha : Nonempty agents] [hN : Fintype agents]
  (φ ψ : formCLK agents) (sf : (Mf_CLK φ).f.states) (hφ : ψ ∈ cl φ) :
  (s_entails_CLK (Mf_CLK φ) sf ψ) ↔ (ψ ∈ sf) := by
  -- This proof is by induction on φ.
  induction' ψ with n ψ χ ih_ψ ih_χ ψ χ ih_ψ ih_χ G ψ ih i ψ ih G ψ ih generalizing sf φ -- sf needs to vary for the modal operators
  all_goals
    obtain ⟨s, hs⟩ := s_f_to_s sf

  · -- case bot
    simp [s_entails_CLK, explosion]
    apply s_f_n_contains
    exact @hs
    apply Or.intro_left
    exact @bot_not_mem_of_ax_consistent (formCLK agents) _ s.1 s.2.1

  · -- case var
    simp_all only [mem_mk, Finset.setOf_mem, s_entails_CLK, Mf_CLK_f_states, Mf_CLK_v, mem_setOf_eq,
      and_true]
    apply Iff.intro
    · intro h
      exact h.left
    · intro h
      apply And.intro h hφ

  · -- case and
    have hψ := subformula.in_cl_sub hφ subformula.and_left
    have hχ := subformula.in_cl_sub hφ subformula.and_right
    specialize ih_ψ _ sf hψ
    specialize ih_χ _ sf hχ
    unfold s_entails_CLK
    rw [ih_ψ, ih_χ, hs, hs, hs]
    simp only [hφ, hψ, hχ, and_true]
    apply Iff.intro
    · rintro ⟨hψs, hχs⟩
      apply max_ax_contains_by_set_proof_2h s.2 hψs hχs axCLK.Prop4
    · intro hψχs
      apply And.intro
      · apply max_ax_contains_by_set_proof s.2 hψχs axCLK.Prop5
      · apply max_ax_contains_by_set_proof s.2 hψχs axCLK.Prop6

  · -- case imp
    have hψ := subformula.in_cl_sub hφ subformula.imp_left
    have hχ := subformula.in_cl_sub hφ subformula.imp_right
    specialize ih_ψ _ sf hψ
    specialize ih_χ _ sf hχ
    unfold s_entails_CLK
    rw [ih_ψ, ih_χ, hs, hs, hs]
    simp only [hφ, hψ, hχ, and_true]
    apply Iff.intro
    · intro h
      exact max_ax_contains_imp_by_proof s.2 h
    · intro h hφ
      apply max_ax_contains_by_set_proof_2h s.2 hφ h likemp

  · -- case [G] ψ
    have hψ := subformula.in_cl_sub hφ subformula.effectivity
    let ih := λ sf => ih _ sf hψ
    cases' Classical.em (G = univ) with hG hG
    · exact truth_E_univ _ hψ hφ ih hG
    · exact truth_E_nuniv _ hψ hφ ih hG

  -- case K
  · have hψ := subformula.in_cl_sub hφ subformula.knows
    let ih := λ sf => ih _ sf hψ
    apply Iff.intro
    · exact truth_K_lr _ hφ ih
    · exact truth_K_rl _ hψ ih

----------------------------------------------------------
-- Completeness
----------------------------------------------------------

-- Completeness
----------------------------------------------------------
theorem completenessCLK {agents : Type} [ha : Nonempty agents] [hN : Fintype agents]
  (φ : formCLK agents) : (_⊨ φ) → _⊢ φ := by
  -- rw from contrapositive
  rw [←not_imp_not]
  -- assume ¬ ⊢ φ
  intro hnax
  -- from ¬ ⊢ φ, have that {¬ φ} is a consistent Set
  obtain ⟨s', hmax, hnφ⟩ := @exists_max_ax_consistent_neg_mem (formCLK agents) _ _ hnax
  -- show that φ is not globally valid
  -- by showing that there exists some model where φ is not valid.
  simp[global_valid]
  -- let that model be the canonical model
  apply Exists.intro (Mf_CLK φ)
  -- in the canonical model (M) there exists some state (s) where ¬ M s ⊨ φ
  simp[valid_m]
  obtain ⟨s, hs⟩ :
    ∃ s : (canonical_model_CL agents (formCLK agents) nprfalseCLK).f.states, s = ⟨s', hmax⟩ :=
      exists_apply_eq_apply _ _
  obtain ⟨sf, hsf⟩ := s_to_s_f cl φ s
  apply Exists.intro sf
  -- assume by contradiction that M s ⊨ φ
  intro hf
  -- by the truth lemma φ ∈ s
  have hφ:= (truth_lemma_CLK φ _ sf (cl_contains_phi φ)).mp hf
  -- in that state (s), φ ∈ s, so we do not have ¬ φ ∈ s (by consistency)
  -- contradiction with hnφ
  rw [hsf] at hφ
  have := contra_contains_pr_false s.2 hφ.left
  simp only at this
  apply this
  rw [hs]
  exact hnφ

end canonical
