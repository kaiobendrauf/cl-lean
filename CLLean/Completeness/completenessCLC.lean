/-
Authors: Kai Obendrauf
Following the paper "Coalition Logic with Individual, Distributed and Common Knowledge
by Thomas Ågotnes and Natasha Alechina
and the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley

This file contains the truth lemma for CLC, and from that the proof of completeness for CLC.
-/

import CLLean.Completeness.canonical_filtering
import CLLean.Completeness.closureCLC
import CLLean.Soundness.soundnessCLC
import CLLean.Syntax.CLKLemmas
import CLLean.Syntax.CLCLemmas
import CLLean.Syntax.formula

open Set Classical Logic

namespace canonical

----------------------------------------------------------
-- Canonical Model CL
----------------------------------------------------------

@[simps!] noncomputable def Mf_CLC {agents : Type} [Nonempty agents] [Fintype agents]
  (φ : formCLC agents) : modelECL agents :=
filtered_modelECL agents (formCLC agents) nprfalseCLC cl cl_closed_single_neg φ


/-- Allows us to write `φ ∈ s` instead of `φ ∈ s` -/
instance Mf_CLC.f.states.SetLike {agents : Type} [ha : Nonempty agents] [hN : Fintype agents]
  {φ : formCLC agents} : SetLike ((Mf_CLC φ).f.states) (formCLC agents) :=
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
  {φ ψ : formCLC agents} {G : Set agents} (sf : (Mf_CLC φ).f.states)
  (hφ : ψ ∈ cl φ) (hφ' : (_[G] ψ) ∈ cl φ)
  (ih : ∀ tf, (s_entails_CLC (Mf_CLC φ) tf ψ) ↔ (ψ ∈ tf)) (hG : G = univ) :
  (s_entails_CLC (Mf_CLC φ) sf (_[G] ψ)) ↔ ((_[G] ψ) ∈ sf) := by
  let MC' := canonical_model_CL agents (formCLC agents) nprfalseCLC
  --  M f , sf ⊨ ψ
  calc
    (s_entails_CLC (Mf_CLC φ) sf (_[G]ψ))
    -- ↔ {sf ∈ Sf | M f , sf ⊨ ψ} ∈ Ef (sf )(N ), by definition ⊨
    ↔ {tf | s_entails_CLC (Mf_CLC φ) tf ψ} ∈ (Mf_CLC φ).f.E.E sf G := by
        simp only [s_entails_CLC, Mf_CLC_f_states, Mf_CLC_f_E_E]
    -- ↔ ∃t ∈ SC′, sf = tf and  ̃φ{sf ∈Sf |M f ,sf ⊨ψ} ∈ EC′(t)(N ), by definition Ef.
    _ ↔ ∃ t, (sf = s_f cl φ t) ∧
          tilde MC'.f.states (phi_X_set {sf | s_entails_CLC (Mf_CLC φ) sf ψ}) ∈ MC'.f.E.E t G := by
        simp only [Mf_CLC_f_states, hG, Mf_CLC_f_E_E, E_f, ite_true, mem_setOf_eq]
    -- ↔ ∃t ∈ SC′, sf = tf and  ̃φ{sf ∈Sf |ψ∈sf } ∈ EC′(t)(N ), by ih.
    _ ↔ ∃ t, (sf = s_f cl φ t) ∧ tilde MC'.f.states
          (phi_X_set {sf : (Mf_CLC φ).f.states | ψ ∈ sf}) ∈ MC'.f.E.E t univ := by
        simp only [Mf_CLC_f_states, ih, mem_mk, Finset.setOf_mem, hG]
        -- ↔ ∃t ∈ SC′, sf = tf and  ̃ψ ∈ EC′(t)(N ), by Lemma 6.
    _ ↔ ∃ t, (sf = s_f cl φ t) ∧ tilde MC'.f.states ψ ∈ MC'.f.E.E t (univ) := by
        have hiff : _⊢ ((phi_X_set {sf : (Mf_CLC φ).f.states | ψ ∈ sf}) _↔ ψ) :=
          phi_X_contains_iff_psi (cl_closed_single_neg φ) (hφ)
        have htilde := @tilde_ax_iff _ (formCLC agents) _ _ _ nprfalseCLC _ _ hiff
        rw [htilde]
    -- ↔ ∃t ∈ SC′, sf = tf and [N ] ψ ∈ t, by Lemma 7.
    _ ↔ ∃ t, (sf = s_f cl φ t) ∧ (_[univ] ψ) ∈ t := by
        simp only [Mf_CLC_f_states, E_s_contains_tilde_iff_E_in_s _ univ]
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
  {φ ψ : formCLC agents} {G : Set agents} (sf : (Mf_CLC φ).f.states)
  (hφ : ψ ∈ cl φ) (hφ' : (_[G] ψ) ∈ cl φ)
  (ih : ∀ tf, (s_entails_CLC (Mf_CLC φ) tf ψ) ↔ (ψ ∈ tf)) (hG : G ≠ univ) :
  (s_entails_CLC (Mf_CLC φ) sf (_[G] ψ)) ↔ ((_[G] ψ) ∈ sf) := by
  let MC' := canonical_model_CL agents (formCLC agents) nprfalseCLC
  -- M f , sf ⊨ ψ
  calc
    (s_entails_CLC (Mf_CLC φ) sf (_[G]ψ))
    -- ↔ {sf ∈ Sf | M f , sf ⊨ ψ} ∈ Ef (sf )(G ), by definition ⊨
    ↔ {tf | s_entails_CLC (Mf_CLC φ) tf ψ} ∈ (Mf_CLC φ).f.E.E sf G := by
        simp only [s_entails_CLC, Mf_CLC_f_states, Mf_CLC_f_E_E]
    -- ↔ ∀t ∈ SC′, sf = tf and  ̃φ{sf ∈Sf |M f ,sf ⊨ψ} ∈ EC′(t)(G ), by definition Ef .
    _ ↔ ∀ t, (sf = s_f cl φ t) →
          tilde MC'.f.states (phi_X_set {sf | s_entails_CLC (Mf_CLC φ) sf ψ}) ∈ MC'.f.E.E t G := by
        simp only [Mf_CLC_f_states, Mf_CLC_f_E_E, E_f, hG, ite_false, mem_setOf_eq]
        -- simp only [hG, if_false]
    -- ↔ ∀t ∈ SC′, sf = tf ⇒  ̃φ{sf ∈Sf |ψ∈sf } ∈ EC′(t)(G ), by ih.
    _ ↔ ∀ t, (sf = s_f cl φ t) →
          tilde MC'.f.states (phi_X_set {sf : (Mf_CLC φ).f.states | ψ ∈ sf}) ∈ MC'.f.E.E t G := by
        simp only [Mf_CLC_f_states, ih, mem_mk, Finset.setOf_mem]
    -- ↔ ∀t ∈ SC′, sf = tf ⇒  ̃ψ ∈ EC′(t)(G ), by Lemma 6.
    _ ↔ ∀ t, (sf = s_f cl φ t) →  tilde MC'.f.states ψ ∈ MC'.f.E.E t G := by
        have hiff : _⊢ ((phi_X_set {sf : (Mf_CLC φ).f.states | ψ ∈ sf}) _↔ ψ) :=
           phi_X_contains_iff_psi (cl_closed_single_neg φ) (hφ)
        have htilde := @tilde_ax_iff _ (formCLC agents) _ _ _ nprfalseCLC _ _ hiff
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
  {φ ψ : formCLC agents} {i : agents} (sf : (Mf_CLC φ).f.states)
  (hφ' : (_K i ψ) ∈ cl φ) (ih : ∀ tf, (s_entails_CLC (Mf_CLC φ) tf ψ) ↔ (ψ ∈ tf)) :
  (s_entails_CLC (Mf_CLC φ) sf (_K i ψ)) → ((_K i ψ) ∈ sf) :=  by
  obtain ⟨s, hs⟩ := s_f_to_s sf
  -- 1. Let M f , sf ⊨ Kiψ.
  intro h
  -- 2. ∀tf ∈ Sf , sf ∼fi tf ⇒ M f , tf ⊨ ψ:= 1, by definition ⊨.
  unfold s_entails_CLC at h
  -- 3. ∀tf ∈ Sf , sf ∼fi tf ⇒ ψ ∈ tf := 2, by ih.
  simp only [Mf_CLC_f_states, Mf_CLC_f_rel, mem_setOf_eq] at h
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
        apply axCLC.RN
        apply @cut (formCLC agents)
        exact hax
        exact dne
      -- 7.4. ⊢ (Ki(∧χ∈Σ χ)) → (Kiψ):= 7.3, by Axiom K.
      have hKimp : _⊢ ((_K i (finite_conjunction ψs)) _→ K' i ψ) := by
        apply axCLC.MP axCLC.K hKimp
      -- 7.5. ⊢ (∧χ∈Σ Kiχ) → (Kiψ):= 7.4, by propositional logic and Axiom RN.
      have hKimp : _⊢ ((finite_conjunction (List.map (_K i) ψs)) _→ _K i (ψ)):= by
        apply @cut (formCLC agents)
        apply @knows_conjunction agents (formCLC agents)
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
    ∃ t : (canonical_model_CL agents (formCLC agents) nprfalseCLC).f.states, t = ⟨t', hmax⟩ :=
      exists_apply_eq_apply _ _
  rw [union_subset_iff] at hsub
  -- Note that ¬ψ ∈ t.
  have hnψ : (_¬ ψ) ∈ t :=  by
    rw [ht]
    apply singleton_subset_iff.mp hsub.2
   -- 9. sf ∼fi tf.
  obtain ⟨tf, htf⟩ := s_to_s_f cl φ t
  have hrel : tf ∈ (Mf_CLC φ).f.rel i sf:= by
    ext1 x
    apply Iff.intro
    -- 9.1 ∀ χ, K i χ ∈ sf → K i χ ∈ tf.
    · simp only [mem_setOf_eq, htf, ht, hs]
      intro hks
      apply And.intro
      · apply mem_of_mem_of_subset _ hsub.1
        simp only [mem_setOf_eq]
        -- Then K i K i χ ∈ s, by Axiom 4. So K i χ ∈ Σ, by definition Σ and K i χ ∈ t, by 8.
        apply max_ax_contains_by_set_proof s.2 hks.1 axCLC.Four
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
          max_ax_contains_by_set_proof s.2 (not_in_from_notin s.2 hnks) axCLC.Five
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
  {φ ψ : formCLC agents} {i : agents} (sf : (Mf_CLC φ).f.states)
  (hφ : ψ ∈ cl φ) (ih : ∀ tf, (s_entails_CLC (Mf_CLC φ) tf ψ) ↔ (ψ ∈ tf)) :
  ((_K i ψ) ∈ sf) → (s_entails_CLC (Mf_CLC φ) sf (_K i ψ)) :=  by
  -- 1. Let Kiψ ∈ sf .
  intro h
  -- 2. ∀tf ∈ Sf, sf ∼fi tf ⇒ Kiψ ∈ tf := 1, by definition ∼fi .
  have hfaK : ∀ tf, tf ∈ (Mf_CLC φ).f.rel i sf → _K i ψ ∈ tf :=
    λ _ htf => (Set.ext_iff.mp htf ψ).mp h
  -- 3. ∀tf ∈ Sf , sf ∼fi tf ⇒ ψ ∈ tf := 2, by Axiom T.
  have hfa : ∀ tf, tf ∈ (Mf_CLC φ).f.rel i sf → ψ ∈ tf:= by
    intro tf htf
    obtain ⟨t, ht⟩ := s_f_to_s tf
    specialize hfaK tf htf
    rw [ht] at hfaK ⊢
    apply And.intro
    · apply max_ax_contains_by_set_proof t.2 hfaK.1 axCLC.T
    · exact hφ
  -- 4. ∀tf ∈ Sf , sf ∼fi tf ⇒ M f , tf ⊨ ψ:= 3, by ih.
  have hent : ∀ tf, tf ∈ (Mf_CLC φ).f.rel i sf → (s_entails_CLC (Mf_CLC φ) tf ψ) :=
    λ tf htf => (ih tf).mpr (hfa tf htf)
  -- 5. M f , sf ⊨ Kiψ, by the definition of ⊨:= 4.
  exact hent

-- C
----------------------------------------------------------
lemma not_everyone_knows_consistent_list {agents : Type}
  [hN : Fintype agents] [ha : Nonempty agents]
  {φ : formCLC agents} {is : List (agents)}
  {s : (canonical_model_CL agents (formCLC agents) nprfalseCLC).f.states}
  (hfa : ∀ (x : agents), x ∈ is → (_¬ (_K x φ)) ∉ s) :
  finite_conjunction (List.map (λ (i : agents) => _K i φ) is) ∈ s := by
  induction' is with i is ih
  · apply max_ax_contains_taut s.2 prtrue
  · simp only [List.mem_cons, forall_eq_or_imp] at hfa
    apply max_ax_contains_by_set_proof_2h s.2 _ (ih hfa.right) (p4 _ _)
    exact max_ax_contains_by_set_proof s.2 (not_in_from_notin s.2 hfa.left) dne

lemma not_everyone_knows_consistent {agents : Type} [hN : Fintype agents] [ha : Nonempty agents]
  {φ : formCLC agents} {G : Set (agents)}
  {s : (canonical_model_CL agents (formCLC agents) nprfalseCLC).f.states}
  (h : (_¬ _E G φ) ∈ s) : ∃ i ∈ G, (_¬ (_K i φ)) ∈ s := by
  by_contra hfa
  simp at hfa
  apply in_from_not_notin s.2 h
  apply max_ax_contains_by_set_proof s.2 _ dni
  apply not_everyone_knows_consistent_list
  intro i hi
  apply hfa
  simp [Finite.mem_toFinset] at hi
  exact hi

lemma phi_set_imp_e {agents : Type} [ha : Nonempty agents] [hN : Fintype agents]
  {φ ψ : formCLC agents} {G : Set (agents)} {Γ : Set ((Mf_CLC φ).f.states)}
  (hΓ : Γ = {sf : (Mf_CLC φ).f.states | ∀ (tf : (Mf_CLC φ).f.states) (is), (∀ i, i ∈ is → i ∈ G) →
    ∀ sfs, @C_path agents (Mf_CLC φ) is sfs sf tf → (ψ ∈ tf)}) :
  ⊢' ((phi_X_set Γ) →' E' G (phi_X_set Γ)) := by
  -- 9.1 By contradiction assume ¬ ((phi_X_set Σ) → E G (phi_X_set Σ)) is consistent.
  by_contra h
  -- 9.2 ∃s ∈ SC', ¬ ((phi_X_set Σ) → E G (phi_X_set Σ)) ∈ s:= 9.1.
  obtain ⟨s', hmax, hsn⟩ := exists_max_ax_consistent_neg_mem h
  have hs : ∃ s : (canonical_model_CL _ (formCLC agents) nprfalseCLC).f.states, s = ⟨s', hmax⟩ :=
    exists_apply_eq_apply _ _
  cases' hs with s hs
  have hsn : ¬' (phi_X_set Γ _→ _E G (phi_X_set Γ)) ∈ s := by
    simp_all only [Mf_CLC_f_states, mem_mk, Finset.setOf_mem, Finite.toFinset_setOf,
      Finset.mem_univ, forall_true_left]
    exact hsn
  -- 9.3 (phi_X_set Σ) ∧ ¬ E G (phi_X_set Σ) ∈ s:= 9.2, by propositional logic.
  have hsand : phi_X_set Γ ∧' ¬' (_E G (phi_X_set Γ)) ∈ s := by
    apply max_ax_contains_by_set_proof s.2 hsn (iff_l demorgans'''')
  have hsandl : phi_X_set Γ ∈ s := by
    apply max_ax_contains_by_set_proof s.2 hsand (p5 _ _)
  have hsandr : ¬' (_E G (phi_X_set Γ)) ∈ s := by
    apply max_ax_contains_by_set_proof s.2 hsand (p6 _ _)
  -- 9.4 ∃ tf ∈ Σ, phi tf ∈ s:= 9.3, by propositional logic.
  have htf : ∃ tf : (Mf_CLC φ).f.states, (tf ∈ Γ) ∧ (phi_s_f tf ∈ s):=  by
    obtain ⟨tf, ⟨htf1, htf2⟩⟩ := phi_X_set_exists hsandl
    apply Exists.intro tf
    exact ⟨htf1, htf2⟩
  obtain ⟨tf, ⟨htfΓ, htfs⟩⟩ := htf
  -- 9.5 ∃ i ∈ G, (¬ _K i (phi_X_set Σ)) ∈ s:= 9.3, by propositional logic.
  have hnk : ∃ i ∈ G, (_¬ _K i (phi_X_set Γ)) ∈ s :=
    not_everyone_knows_consistent hsandr
  obtain ⟨i, ⟨hi, hnk⟩⟩ := hnk
  -- 9.6 ¬ _K i ¬ (phi_X_set Σᶜ)) ∈ s:= 9.5, by propositional logic, axiom K and Lemma 4.
  have hnkc : (_¬ (_K i (_¬ (phi_X_set Γᶜ)))) ∈ s := by
    apply max_ax_contains_by_set_proof s.2 hnk
    apply (nk_imp_nk i)
    apply (phi_X_set_disjunct_of_disjuncts _ _).mpr
    rw [compl_union_self Γ]
    apply univ_disjunct_provability
  -- 9.7 ∃ uf ∈ Σᶜ, such that ¬ _K i ¬ (phi_s_f φ uf) ∈ s:= 9.6
    -- by propositional logic and axiom K.
  have hnkc : _ ∈ s := by
    apply max_ax_contains_by_set_proof s.2 hnkc (by apply nk_disjunction i)
  have huf : ∃ uf ∈ Γᶜ, (¬' (K' i (¬' (phi_s_f uf)))) ∈ s := by
      by_contra hfa
      simp only [exists_prop, not_exists, not_and] at hfa
      apply in_from_not_notin s.2 hnkc
      apply nk_phi_X_list_exists i
      intro sf hsf
      apply hfa
      simp only [Finite.mem_toFinset, Finset.mem_toList, mem_compl_iff] at hsf
      exact hsf
  obtain ⟨uf, ⟨hufΓc, hufs⟩⟩ := huf
  -- 9.8 ∃ vf, uf ~fCG vf and ψ ∉ vf:= 9.7, by definition Σᶜ.
  simp only [C_path, hΓ, mem_setOf_eq,  mem_compl_iff, not_forall, exists_prop, exists_and_right, exists_and_left] at hufΓc htfΓ
  obtain ⟨vf, hvf⟩ := hufΓc
  obtain ⟨is, his, ⟨ufs, hufvf⟩, hvf⟩ := hvf
  -- 9.9 tf ~i uf.
  have htu : uf ∈ (Mf_CLC φ).f.rel i tf:= by
    ext1 χ
    simp only [mem_setOf_eq]
    apply Iff.intro
    -- ⇒ ∃ χ, K i χ ∈ tf ∧ K i χ ∉ uf.
    · intro hxtf
      by_contra hxuf
      -- ⊢ K i χ → ¬ phi uf .
      have haxkimp : ⊢' (K' i χ →' ¬' (phi_s_f uf)):= by
        obtain ⟨nχ, hnχ, hiffnχ⟩ :=
          s_f_closed (cl_closed_single_neg φ) hxuf (Finset.subset_iff.mp (s_f_subset_cl _) hxtf)
        apply cut dni
        apply cut (iff_l (iff_not hiffnχ))
        apply notin_nphi_s_f hnχ
      -- ⊢ (¬ K i ¬ phi uf) → ¬ K i K i χ, by propositional logic and axiom K.
      have haxnkimp : ⊢' ( ¬' (K' i (¬' (phi_s_f uf))) →' (¬' (K' i (K' i χ)))) :=
        nk_imp_nk i haxkimp
      -- ¬ K i K i χ ∈ s:= this and 9.7.
      have hsnkk : (¬' (K' i (K' i (χ)))) ∈ s := by
        apply max_ax_contains_by_set_proof s.2 hufs haxnkimp
      -- K i K i χ ∈ s:= 9.4, because K i χ ∈ tf and by axiom Four.
      have hskk : ((K' i (K' i (χ)))) ∈ s:=  by
        apply max_ax_contains_by_set_proof s.2 htfs
        apply cut (phi_s_f_forall_imp _ hxtf)
        apply Four
      -- Contradiction.
      have := contra_contains_pr_false s.2 hskk hsnkk
      simp only at this
    -- ⇐ ∃ χ, K i χ ∈ uf ∧ K i χ ∉ tf.
    · intro hxuf
      by_contra hxtf
      -- ⊢ ¬ K i χ → ¬ phi uf.
      have haximp : ⊢' ((¬' (K' i χ)) →' ¬' (phi_s_f uf)):= notin_nphi_s_f hxuf
      -- ⊢ (¬ K i ¬ phi uf) → ¬ K i ¬ K i χ, by propositional logic and axiom K.
      have haxnkimp : ⊢' (¬' (K' i (¬' (phi_s_f uf)))) →' ¬' (K' i (¬' (K' i χ))) :=
        nk_imp_nk i haximp
      -- ¬ K i ¬ K i χ ∈ s:= this and 9.7.
      have hsnknk : (¬' (K' i (¬' (K' i (χ))))) ∈ s :=
        by apply max_ax_contains_by_set_proof s.2 hufs haxnkimp
      -- K i χ ∈ s, by axiom 5.
      have hsk : ((K' i (χ))) ∈ s :=
        by apply max_ax_contains_by_set_proof s.2 hsnknk nnk_imp_k
      -- ¬ K i χ ∈ s:= 9.4, because K i χ ∉ tf.
      obtain ⟨nχ, hnχ, hiffnχ⟩ :=
        s_f_closed (cl_closed_single_neg φ) hxtf (Finset.subset_iff.mp (s_f_subset_cl _) hxuf)
      have hsnk : ((¬' (K' i (χ)))) ∈ s := by
        apply max_ax_contains_by_set_proof s.2 htfs
          (cut (phi_s_f_forall_imp _ hnχ) (iff_l hiffnχ))
      -- Contradiction.
      have := contra_contains_pr_false s.2 hsk hsnk
      simp only at this
  -- 9.10 ψ ∈ vf, because tf ∈ Σ (from 9.4)
    -- and there is a path tf ~fi uf (from 9.9), uf ~cG vf (from 9.8).
  have hvf' : ψ ∈ vf := by
    apply htfΓ _ (i :: is) _ (uf :: ufs)
    · unfold C_path
      exact And.intro htu hufvf
    · simp only [List.mem_cons, forall_eq_or_imp]
      exact And.intro hi his
  -- Contradiction from 9.8 & 9.10.
  exact hvf hvf'

-- Case CGψ ⇒ (M f , sf ⊨ CGψ ⇒ GGψ ∈ sf) :
lemma truth_C_lr {agents : Type} [ha : Nonempty agents] [hN : Fintype agents]
  {φ ψ : formCLC agents} {sf : (Mf_CLC φ).f.states} {G : Set (agents)}
  (hcl : _C G ψ ∈ cl φ) (ih : ∀ tf, (s_entails_CLC (Mf_CLC φ) tf ψ) ↔ (ψ ∈ tf)) :
  (s_entails_CLC (Mf_CLC φ) sf (_C G ψ)) → (_C G ψ) ∈ sf := by
  -- 1. Let M f , sf ⊨ CGψ.
  intro h
  -- 2. ∀ tf, sf ∼f CG tf → M f , tf ⊨ ψ:= 1, by definition ⊨
  unfold s_entails_CLC at h
  -- 3. ∀ tf, sf ∼f CG tf → ψ ∈ tf := 2, by ih.
  simp only [ih] at h
  -- 4. Let Σ = {sf | ∀tf, sf ∼f CG tf → ψ ∈ tf }.
  let Γ := {sf : (Mf_CLC φ).f.states | ∀ tf, (∃ is,
            (∀ i, i ∈ is → i ∈ G) ∧ ∃ sfs, C_path is sfs sf tf) → ψ ∈ tf}
  -- 5. sf ∈ Σ:= 3, by definition Σ:= 4 .
  have hsfΓ : sf ∈ Γ:=  by
    apply mem_setOf_eq.mpr
    exact h
  -- 6. ⊢ φsf → φΣ := 5, by propositional logic.
  have haxsfΓ : _⊢ ((phi_s_f sf) _→ (phi_X_set Γ)) :=
    ax_phi_s_f_imp_phi_X_set_of_mem hsfΓ
  -- 7. G ≠ ∅ ⇒ ∀ sf ∈ Σ, ψ ∈ sf, by definition Σ:= 4.
  have hψΓ : (∃ i, i ∈ G) → ∀ sf ∈ Γ, ψ ∈ sf:= by
    intro hi sf hsf
    cases' hi with i hi
    simp only [mem_setOf_eq, mem_mk, forall_exists_index, and_imp] at hsf
    exact hsf sf [i] (by simp only [hi, List.mem_singleton, forall_eq]) [] rfl
  -- 8. G ≠ ∅ ⇒ ⊢ φΣ → ψ:= 7, by propositional logic.
  have haxΓψ  : (∃ i, i ∈ G) → _⊢ ((phi_X_set Γ) _→ ψ):= by
    intro hi
    apply @cut (formCLC agents)
    apply iff_l
    apply phi_X_list_conj_contains
    · intro sf hsf
      apply hψΓ hi
      simp only [Finset.mem_toList, Finite.mem_toFinset] at hsf
      exact hsf
    exact p5 _ _
  -- 9. ⊢ φΣ → EGφΣ.
  have haxE : _⊢ ((phi_X_set Γ) _→ _E G (phi_X_set Γ)) := by
    apply phi_set_imp_e
    simp only [Mf_CLC_f_states, mem_mk, Finset.setOf_mem, forall_exists_index, and_imp]
    rfl
  -- 10. ⊢ φΣ → CGψ:= 8 & 9, by Axiom RC.
  have haxC : _⊢ ((phi_X_set Γ) _→ _C G ψ):=  by
    apply axCLC.RC
    cases' (Classical.em (G = ∅)) with hempty hnempty
    · apply axCLC.MP axCLC.Prop1
      rw [hempty]
      exact @everyone_empty _ (formCLC agents) hN _ _ _ ∅ rfl
    · have hi : ∃ (x : agents), x ∈ G :=
        nonempty_def.mp (nonempty_iff_ne_empty.mpr hnempty)
      apply @cut (formCLC agents) _ _ _ _ haxE
      apply mp
      apply @K_everyone _ _ hN (@formula_axCLC _ hN)
      apply everyone_knows_pr
      apply imp_imp_and
      exact haxΓψ hi
      exact iden
  -- 11. CGψ ∈ sf:= 6 & 10, by propositional logic.
  obtain ⟨s, hs⟩ := s_f_to_s sf
  apply hs.mpr
  simp only [hcl, and_true]
  apply max_ax_contains_by_set_proof s.2 (phi_s_f_in_s s)
  rw [(s_f_eq_sf @hs)]
  exact cut haxsfΓ haxC

-- Case CGψ ⇐ (GGψ ∈ sf ⇒ M f, sf ⊨ CGψ) :
lemma truth_C_rl {agents : Type} [ha : Nonempty agents] [hN : Fintype agents]
  {φ ψ : formCLC agents} {sf : (Mf_CLC φ).f.states} {G : Set (agents)}
  (hcl : ψ ∈ cl φ) (hcl' : _C G ψ ∈ cl φ) (hcl'' : ∀ i ∈ G, (_K i (_C G ψ)) ∈ cl φ)
  (ih : ∀ tf, (s_entails_CLC (Mf_CLC φ) tf ψ) ↔ (ψ ∈ tf)) :
  (_C G ψ) ∈ sf → (s_entails_CLC (Mf_CLC φ) sf (_C G ψ)) := by
  -- 1. Let CGψ ∈ sf, and tf be some world such that sf ∼f CG tf.
  intro h tf htf
  obtain ⟨is, his, sfs, hsftf⟩ := htf
  -- 2. ∀ u ∈ SC', ∀ v ∈ SC', ∀ i ∈ G, C G ψ ∈ uf → uf ~fi vf → ψ ∈ vf ∧ C G ψ ∈ vf
  have hsfrel : ∀ uf vf,  ∀ i, i ∈ G → (_C G ψ) ∈ uf → (vf ∈ (@Mf_CLC _ ha hN φ).f.rel i uf) →
    ψ ∈ vf ∧ _C G ψ ∈ vf := by
    -- 2.1 Assume some worlds u v, and assume some agent i ∈ G, such that C G ψ ∈ uf and uf ~fi vf.
    intro uf vf i hi h hrel
    obtain ⟨u, hu⟩ := s_f_to_s uf
    obtain ⟨v, hv⟩ := s_f_to_s vf
    rw [hu] at h
    simp only [hcl', and_true] at h
    -- 2.2 K i C G ψ ∈ uf:= 2.1, by definition (cl (C G ψ)), propositional logic
      -- and Axioms C, K and RN.
    have hkuf : _K i (_C G ψ) ∈ uf:=  by
      apply hu.mpr
      apply And.intro
      · apply @max_ax_contains_by_set_proof _ (@formula_axCLC _ hN) _ _ _ u.2 h
        exact @c_imp_kc _ _ hN (@formula_axCLC _ hN) _ _ _ G i hi
      · exact hcl'' i hi
    -- 2.3 K i C G ψ ∈ vf:= 2.1 & 2.2, by definition ∼if.
    have hkv : _K i (_C G ψ) ∈ vf:=  by
      simp only [Mf_CLC_f_rel, ext_iff] at hrel
      dsimp at hrel
      apply (hrel _).mp
      exact hkuf
    rw [hv] at hkv ⊢
    rw [hv]
    simp only [hcl, hcl', hcl'', and_true] at hkv ⊢
    -- 2.4 C G ψ ∈ vf:= 2.3, by Axiom T.
    have hcv : (_C G ψ) ∈ v :=
      @max_ax_contains_by_set_proof _ (@formula_axCLC _ hN) _ _ _ v.2 hkv.1 (by apply axCLC.T)
    -- 2.5 ψ ∈ vf:= 2.4, by propositional logic, and Axioms T, C, K and RN.
    have hv : ψ ∈ v := by
      apply @max_ax_contains_by_set_proof _ (@formula_axCLC _ hN) _ _ _ v.2 hcv
        (@c_imp _ _ hN (@formula_axCLC _ hN) _ _ ψ G i hi)
    exact And.intro hv hcv
  -- 3. This proof is by induction on length of the path.
  induction' sfs with uf sfs ihC generalizing ψ sf tf G is
  all_goals
    cases' is with i is his -- to unfold C_path we need to unfold the is too
  all_goals
    try unfold C_path at hsftf
    try simp only at hsftf
    try simp only [List.mem_cons, forall_eq_or_imp] at his
  · -- 3.1 Base case : Path := sf ~i tf.
    -- 3.1.1. ψ ∈ tf:= 2, because C G ψ ∈ sf (from 1), and sf ~i tf (from 3.1).
    have := (hsfrel sf tf i his.1 h hsftf).1
    -- 3.1.2. M, tf ⊨ ψ:= 3.1.1, by ih.
    rw [←ih] at this
    exact this
  · -- 3.2 Base case : Path := sf ~i sf_1 ~i1 _ ~in tf, or sf ~i sf_1, s_1 ~fCG tf.
     -- Induction Hypothesis for the path : ∀ uf, C G ψ ∈ uf → (uf ∼fCG tf) → (Mf, tf ⊨ ψ)).
    -- 3.2.1 C G ψ ∈ sf_1:= 2, because C G ψ ∈ sf (from 1), and sf ~i tf (from 3.2).
    have hsf1 : _C G ψ ∈ uf:= (hsfrel sf uf i his.1 h hsftf.1).2
    -- 3.2.2  M, tf ⊨  ψ:= 3.2 by the Induction Hypothesis for the path
     -- because C G ψ ∈ sf_1 (from 3.2.1) and sf_1 ∼fCG tf:= 3.2
    exact @ihC ψ uf G hcl hcl' hcl'' ih hsf1 tf is his.2 hsftf.2 hsfrel

-- Truth Lemma
----------------------------------------------------------
lemma truth_lemma_CLC {agents : Type} [ha : Nonempty agents] [hN : Fintype agents]
  (φ ψ : formCLC agents) (sf : (Mf_CLC φ).f.states) (hφ : ψ ∈ cl φ) :
  (s_entails_CLC (Mf_CLC φ) sf ψ) ↔ (ψ ∈ sf) := by
  -- This proof is by induction on φ.
  induction' ψ with n ψ χ ih_ψ ih_χ ψ χ ih_ψ ih_χ G ψ ih i ψ ih G ψ ih generalizing sf φ -- sf needs to vary for the modal operators
  all_goals
    obtain ⟨s, hs⟩ := s_f_to_s sf

  · -- case bot
    simp [s_entails_CLC, explosion]
    apply s_f_n_contains
    exact @hs
    apply Or.intro_left
    exact @bot_not_mem_of_ax_consistent (formCLC agents) _ s.1 s.2.1

  · -- case var
    simp_all only [mem_mk, Finset.setOf_mem, s_entails_CLC, Mf_CLC_f_states, Mf_CLC_v, mem_setOf_eq,
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
    unfold s_entails_CLC
    rw [ih_ψ, ih_χ, hs, hs, hs]
    simp only [hφ, hψ, hχ, and_true]
    apply Iff.intro
    · rintro ⟨hψs, hχs⟩
      apply max_ax_contains_by_set_proof_2h s.2 hψs hχs axCLC.Prop4
    · intro hψχs
      apply And.intro
      · apply max_ax_contains_by_set_proof s.2 hψχs axCLC.Prop5
      · apply max_ax_contains_by_set_proof s.2 hψχs axCLC.Prop6

  · -- case imp
    have hψ := subformula.in_cl_sub hφ subformula.imp_left
    have hχ := subformula.in_cl_sub hφ subformula.imp_right
    specialize ih_ψ _ sf hψ
    specialize ih_χ _ sf hχ
    unfold s_entails_CLC
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

  -- case C
  · have hψ := subformula.in_cl_sub hφ subformula.common_know
    let ih := λ sf => ih _ sf hψ
    unfold s_entails_CLC
    have hcl : ∀ i ∈ G, (_K i (_C G ψ)) ∈ cl φ :=
      λ i hi => cl_C_contains_KC hi hφ
    apply Iff.intro
    · exact truth_C_lr hφ ih
    · exact truth_C_rl hψ hφ hcl ih

----------------------------------------------------------
-- Completeness
----------------------------------------------------------

-- Completeness
----------------------------------------------------------
theorem completenessCLC {agents : Type} [ha : Nonempty agents] [hN : Fintype agents]
  (φ : formCLC agents) : (_⊨ φ) → _⊢ φ := by
  -- rw from contrapositive
  rw [←not_imp_not]
  -- assume ¬ ⊢ φ
  intro hnax
  -- from ¬ ⊢ φ, have that {¬ φ} is a consistent Set
  obtain ⟨s', hmax, hnφ⟩ := @exists_max_ax_consistent_neg_mem (formCLC agents) _ _ hnax
  -- show that φ is not globally valid
  -- by showing that there exists some model where φ is not valid.
  simp[global_valid]
  -- let that model be the canonical model
  apply Exists.intro (Mf_CLC φ)
  -- in the canonical model (M) there exists some state (s) where ¬ M s ⊨ φ
  simp[valid_m]
  obtain ⟨s, hs⟩ :
    ∃ s : (canonical_model_CL agents (formCLC agents) nprfalseCLC).f.states, s = ⟨s', hmax⟩ :=
      exists_apply_eq_apply _ _
  obtain ⟨sf, hsf⟩ := s_to_s_f cl φ s
  apply Exists.intro sf
  -- assume by contradiction that M s ⊨ φ
  intro hf
  -- by the truth lemma φ ∈ s
  have hφ:= (truth_lemma_CLC φ _ sf (cl_contains_phi φ)).mp hf
  -- in that state (s), φ ∈ s, so we do not have ¬ φ ∈ s (by consistency)
  -- contradiction with hnφ
  rw [hsf] at hφ
  have := contra_contains_pr_false s.2 hφ.left
  simp only at this
  apply this
  rw [hs]
  exact hnφ


end canonical
