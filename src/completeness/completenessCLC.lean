import completeness.filtered_modelC
import syntax.CLClemmas


local attribute [instance] classical.prop_decidable

open set formCLC

namespace canonical

----------------------------------------------------------
-- Truth Lemma
----------------------------------------------------------

-- 2. CGψ ∈ sf ⇒ ∀sn ∈ S that are reachable from sf by some path sf ∼f i1 sf1 ∼fi2 ... ∼f in sfn, 
--       where {i1, i2..in} ⊆ G, then ψ ∈ sfn and CGψ ∈ sfn
lemma truth_C_helper' {agents : Type} [ha : nonempty agents] [hN : fintype agents]
  {φ ψ : formCLC agents} {sf: S_f φ} {sfs : list (S_f φ)} {G : set (agents)} {is : list (agents)} 
  (hG : ∀ i, i ∈ is → i ∈ G) (hC : (C G ψ) ∈ sf) 
  (hcl : ψ ∈ cl φ) (hcl' : c G ψ ∈ cl φ) (hcl'' : ∀ i ∈ G, (K i (C G ψ)) ∈ cl φ) :
  ∀ tf : (S_f φ), (@C_path agents (filtered_model_CLC φ) is sfs sf tf) → (ψ ∈ tf ∧ (C G ψ) ∈ tf):=
begin
    -- This proof is by induction on the length of the path.
    obtain ⟨s, hs⟩ := s_f_to_s φ sf,
    induction' is with i is ih,
    { simp [C_path], },
    { simp only [list.mem_cons_iff, forall_eq_or_imp] at hG,
      -- simp [hs, ht, hcl, hcl'] at *, 
      cases sfs with tf sfs,
      { intros tf htf,
        obtain ⟨t, ht⟩ := @s_f_to_s agents ha hN φ tf,unfold C_path at htf,
        dsimp at htf,
        simp[ext_iff] at htf,
        -- specialize htf ψ,
        specialize hcl'' i hG.left,
        -- specialize htf _ (hcl'' i hG.left),
        -- simp [hcl''] at htf,
        have hkt : k i (C G ψ) ∈ tf, from
        begin
          -- specialize htf _ (hcl'' i hG.left),
          apply (htf _ ).mp,
          simp [hs, ht, hcl, hcl'] at *,
          split,
          apply @max_ax_contains_by_set_proof _ _ (@formula_axCLC _ hN) _ _ _ s.2 hC,
          exact @c_imp_kc _ hN _ _ (@formula_axCLC _ hN) _ _ ψ G i hG.left,
          exact hcl'',
        end,
        simp [hs, ht, hcl, hcl'] at *,
        have hct : (C G ψ) ∈ t, 
          from by apply @max_ax_contains_by_set_proof _ _ (@formula_axCLC _ hN) _ _ _ t.2 hkt.left (@axCLC.T _ hN _ _),
        have ht : ψ ∈ t, 
          from by apply @max_ax_contains_by_set_proof _ _ (@formula_axCLC _ hN) _ _ _ t.2 hct 
            (@c_imp _ hN _ _ (@formula_axCLC _ hN) _ _ ψ G i hG.left),
        exact and.intro ht hct, },
      { -- 2.2. Inductive step: length (n) = m + 1
        -- 2.2.1. Inductive Hypothesis: ∀sf m′ ∈ Sf if there exists some path sf ∼fi1 sf1 ∼fi2 ... ∼f im′ sfm′ , 
          --  where {i1, i2..im′ } ⊆ G and m′ ≤ m then ψ ∈ sfm′ and CGψ ∈ sfm′ .
        -- 2.2.2. Assume CGψ ∈ sf .
        intros uf huf,
        obtain ⟨t, ht⟩ := @s_f_to_s agents ha hN φ tf,
        obtain ⟨u, hu⟩ := @s_f_to_s agents ha hN φ uf,
        simp only [C_path] at *,
        cases huf with hst htu,
        dsimp at hst,
        simp[ext_iff] at hst,
        have hkt : k i (C G ψ) ∈ tf, from
        begin
          apply (hst _ ).mp,
          simp [hs, ht, hcl, hcl'] at *,
          split,
          apply @max_ax_contains_by_set_proof _ _ (@formula_axCLC _ hN) _ _ _ s.2 hC,
          exact @c_imp_kc _ hN _ _ (@formula_axCLC _ hN) _ _ ψ G i hG.left,
          exact hcl'' i hG.left,
        end,
        simp [hs, ht, hcl, hcl'] at hkt,
        have hct : (C G ψ) ∈ tf, from 
        begin
          simp [hs, ht, hcl, hcl'] at *,
          apply @max_ax_contains_by_set_proof _ _ (@formula_axCLC _ hN) _ _ _ t.2 hkt.left (@axCLC.T _ hN _ _),
        end,
        -- 2.2.3. ψ ∈ sfm and CGψ ∈ sfm, from 2.2.1.
        -- specialize @ih i hN ψ _ (t :: ss) G hC hG.right u,
        -- specialize @ih_s ψ t G hC i is hG.left hG.right ih u,
        apply @ih ha,
        -- apply ih hct hG.right uf htu,
        exact hct,
        repeat { assumption, },
        exact hG.right,

        -- exact @ih ha hN _ _ _ _ _ _ _ _ _ i hN ψ tf (sfs) G hct hG.right uf htu,
        -- 2.2.4. Kim+1 CGψ ∈ sfm, by Axiom C, from 2.2.3.
        -- 2.2.5. Kim+1 CGψ ∈ sfm+1, by definition ∼f (given that sfm ∼im+1sfm+1), from 2.2.4.
        -- 2.2.6. CGψ ∈ sfm+1, by Axiom T, from 6.2.6.
        -- 2.2.7. ψ ∈ sfm+1, by Axioms c & T, from 6.2.7.
    }, },
end

-- lemma anouther C_helper  {agents : Type} [ha : nonempty agents] [hN : fintype agents]
--   {φ ψ : formCLC agents} {sf: S_f φ} {G : set (agents)} 
--   (hcl : ψ ∈ cl φ) (hcl' : c G ψ ∈ cl φ) (hcl'' : ∀ i ∈ G, (K i (C G ψ)) ∈ cl φ)

lemma not_everyone_knows_consistent_list {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  {φ : formCLC agents} {is : list (agents)} {s : (canonical_model_CLC agents).f.states} 
  (hfa : ∀ (x : agents), x ∈ is → (¬ (k x φ)) ∉ s) : finite_conjunction (list.map (λ (i : agents), k i φ) is) ∈ s
 :=
begin
  induction is with i is ih,
  { simp,
    apply max_ax_contains_by_empty_proof s.2 prtrue, },
  { simp [finite_conjunction],
    simp at hfa,
    apply max_ax_contains_by_set_proof_2h s.2 _ _ (p4 _ _),
    { apply max_ax_contains_by_set_proof s.2 _ dne,
      exact not_in_from_notin s.2 hfa.left, },
    { apply ih,
    exact hfa.right, } },
end

lemma not_everyone_knows_consistent {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  {φ : formCLC agents} {G : set (agents)} {s : (canonical_model_CLC agents).f.states} 
  (h : (¬ e G φ) ∈ s) : ∃ i ∈ G, (¬ (k i φ)) ∈ s :=
begin
  by_contradiction hfa,
  simp at hfa,
  apply in_from_not_notin s.2 h,
  apply max_ax_contains_by_set_proof s.2 _ dni,
  apply max_ax_contains_by_set_proof s.2 _ (iff_r axCLC.E),
  apply not_everyone_knows_consistent_list,
  intros i hi,
  apply hfa,
  simp [finite.mem_to_finset] at hi,
  exact hi,
end

lemma phi_set_imp_e {agents : Type} [ha : nonempty agents] [hN : fintype agents]
  {φ ψ : formCLC agents} {G : set (agents)} {Γ : set (S_f φ)} -- (hG : G.nonempty)
  (hΓ : Γ = {sf : S_f φ | ∀ (tf : (S_f φ)) (is), (∀ i, i ∈ is → i ∈ G) → 
    ∀ sfs, @C_path agents (filtered_model_CLC φ) is sfs sf tf → (ψ ∈ tf)}) : 
  ax ((phi_X_set φ Γ) ~> e G (phi_X_set φ Γ)) :=
begin
  -- By contradiction assume (¬ ((phi_X_set φ Γ) → e G (phi_X_set φ Γ))) is consistent
  by_contradiction,
  have := comphelper h,
  obtain ⟨s', hexn, htn⟩ := exists_max_ax_consistent_neg_mem h,
  let s : (canonical_model_CLC agents).f.states := ⟨s', hexn⟩,
  have hsn : ¬' (phi_X_set φ Γ~>e G (phi_X_set φ Γ)) ∈ s, from by apply htn,
  -- ((phi_X_set φ Γ) ∧ ¬ (e G (phi_X_set φ Γ))) is consistent
  have hs1 : phi_X_set φ Γ ∧' ¬' (e G (phi_X_set φ Γ)) ∈ s, 
    from by apply max_ax_contains_by_set_proof s.2 htn (iff_l demorgans''''),
  -- There exists some tf ∈ Sf, such that ((phi_s_f φ tf) ∧ ¬ (e G (phi_X_set φ Γ))) is consistent
  have hs2 : phi_X_set φ Γ ∈ s, 
    from by apply max_ax_contains_by_set_proof s.2 hs1 (p5 _ _),
  have hs3 : ∃ uf ∈ Γ, phi_s_f φ uf ∈ s, from phi_X_set_exists hs2,
  cases hs3 with tf hs3, cases hs3 with htf hs3,
  -- There exists some i ∈ G, such that ((phi_s_f φ tf) ∧ (k i ¬ (phi_X_set φ Γ))) is consistent
  have hs4 : ¬' (e G (phi_X_set φ Γ)) ∈ s, from by apply max_ax_contains_by_set_proof s.2 hs1 (p6 _ _),
  have hs5 : ∃ i ∈ G, (¬ k i (phi_X_set φ Γ)) ∈ s, from not_everyone_knows_consistent hs4,
  cases hs5 with i hs5, cases hs5 with hi hs5,
  have hs6 : ((phi_s_f φ tf) & (¬ (k i (phi_X_set φ Γ)))) ∈ s, 
    from by apply max_ax_contains_by_set_proof_2h s.2 hs3 hs5 axCLC.Prop4,

  have hs6 : @ax_consistent (formCLC agents) _ _ 
    {((phi_s_f φ tf) ∧' (K' i (¬' (phi_X_set φ Γ))))}, from 
  begin
    intros fs hfs,
    unfold finite_ax_consistent,
    induction fs with f fs ih,
    { simp,
      exact consistent_of_not_ax h, },
    { simp at *,
      rw hfs.left at *,
      intro hf,
      sorry,
    }

  end,

  -- ((phi_s_f φ tf) ∧ (k i (phi_X_set φ Γᶜ))) is consistent

  -- ((phi_s_f φ tf) ∧ (V_{sf ∈ Γᶜ} k i (phi_s_f φ sf))) is consistent

  -- There exists some uf ∈ Γᶜ, such that ((phi_s_f φ tf) ∧ (k i (phi_s_f φ uf))) is consistent

  -- tf ~a uf, 
    -- Suppose that Γ ∧ Kˆa∆ is consistent. Suppose that it is not the case that Γ ∼ca ∆. Therefore, there is a formula φ such that
    --   a) Kaφ∈Γ but Kaφ̸∈∆, or
    --   b) Kaφ̸∈Γ but Kaφ∈∆. We proceed by these cases
    --   a) By 2 of this lemma and the fact that Φ is closed under single negations, ¬Kaφ ∈ ∆. However, by positive introspection Γ ⊢ KaKaφ. Note that KaKaφ∧Kˆa¬Kaφ is inconsistent. However ⊢ Kˆa∆ → Kˆa¬Kaφ. Therefore Γ ∧ Kˆa∆ is inconsistent, contradicting our initial assump- tion.
    --   b) By 2 of this lemma and the fact that Φ is closed under single nega- tions, ¬Kaφ ∈ Γ. However, ⊢ Kˆa∆ → KˆaKaφ and ⊢ KˆaKaφ → Kaφ. Therefore Γ ∧ Kˆa∆ is inconsistent, contradicting our initial assump-
    --   tion. 
    --   In both cases we are led to a contradiction. Therefore Γ ∼ca ∆.

  -- Contradiction because there is a path tf ~i uf ~cG vf such that φ ∉ vf, but tf ∈ Γ,

  sorry,
end


lemma truth_C_helper'' {agents : Type} [ha : nonempty agents] [hN : fintype agents]
  {φ ψ : formCLC agents} {sf: S_f φ} {G : set (agents)} 
  (hcl : ψ ∈ cl φ) (hcl' : c G ψ ∈ cl φ) (hcl'' : ∀ i ∈ G, (K i (C G ψ)) ∈ cl φ)
  (h : ∀ (tf : (S_f φ)) (is), (∀ i, i ∈ is → i ∈ G) → 
    ∀ sfs, @C_path agents (filtered_model_CLC φ) is sfs sf tf → (ψ ∈ tf))
  -- , (∀ (a : agents), a ∈ x → a ∈ G) → ∀ (x_1 : list (filtered_model_CLC χ).f.to_frameCL.states), C_path x x_1 sf t → φ ∈ t
  :
  (C G ψ) ∈ sf :=
begin
    -- 3.1. Assume ∀sfn ∈ Sf if there exists some path sf ∼fi1 sf1 ∼fi2 ... ∼fin sfn,where {i1, i2..in} ⊆ G then ψ ∈ sfn
    -- 3.2. let Σ be the set of all tf ∈ Sf, 
      -- such that for every state tfn if that tf n is reachable from tf through some path tf ∼f i1 tf 1 ∼fi2 ... ∼fin tf n,
      -- where {i1, i2..in} ⊆ G, then ψ ∈ tf .
    let Γ := {sf : S_f φ | ∀ (tf : (S_f φ)) (is), (∀ i, i ∈ is → i ∈ G) → 
      ∀ sfs, @C_path agents (filtered_model_CLC φ) is sfs sf tf → (ψ ∈ tf)},
    -- 3.3. sf ∈ Σ, from 2.3.1 and 2.3.2.
    have hsfΓ : sf ∈ Γ, from h,
    -- 3.4. ⊢ φsf→ φΣ , by propositional logic, from 2.3.3.
    have hax1 : axCLC ((phi_s_f φ sf) ~> (phi_X_set φ Γ)), from ax_phi_s_f_imp_phi_X_set_of_mem' hsfΓ,
    -- 3.5. ⊢ φΣ → ψ, by propositional logic, because all t ∈ Σ, ψ ∈ t.
    -- 3.6. ⊢ φΣ → EGφΣ , from 2.3.2.
    have hax1' : ∀ sf, sf ∈ Γ → axCLC ((phi_s_f φ sf) ~> (phi_X_set φ Γ)), 
      from λ sf h, ax_phi_s_f_imp_phi_X_set_of_mem' h,
    -- 3.7. ⊢ φsf → CGψ, by Axiom RC, from 2.3.4, 2.3.5 & 2.3.6.
    have hψΓ : (∃ i, i ∈ G) → ∀ sf ∈ Γ, ψ ∈ sf, from
    begin
      intros hi sf hsf,
      cases hi with i hi,
      simp [Γ] at hsf,
      apply hsf sf (i :: list.nil) (by simp [hi]) (list.nil),
      unfold C_path,
      exact rfl,
    end,
    have hax2 : axCLC ((phi_X_set φ Γ) ~> e G (ψ & (phi_X_set φ Γ))), from
    begin
      cases (em (G = ∅)) with hempty hnempty,
      { apply axCLC.MP,
        apply axCLC.Prop1,
        rw hempty,
        apply @everyone_empty _ hN (formCLC agents), },
      { have hnempty : G.nonempty, from ne_empty_iff_nonempty.mp hnempty,
        rw nonempty_def at hnempty,
        specialize hψΓ hnempty,
        cases hnempty with i hi,

        have hax3 : axCLC ((phi_X_set φ Γ) ~> ψ), from
        begin
          apply @cut (formCLC agents),
          apply iff_l,
          unfold phi_X_set phi_X_finset,
          apply phi_X_list_conj_contains,
          { intros sf hsf,
            apply hψΓ,
            simp [Γ] at *,
            exact hsf, },
          exact p5 _ _,
        end,

        have hax4 : ax ((phi_X_set φ Γ) ~> e G (phi_X_set φ Γ)), from phi_set_imp_e (by simp [Γ]),

        apply @cut (formCLC agents),
        exact hax4,
        apply mp,
        apply @K_everyone _ hN _ _ (@formula_axCLC _ hN),
        apply everyone_knows_pr,
        apply imp_imp_and,
        apply hax3,
        exact iden,
      },
    end,
    -- 3.8. CGψ ∈ sf , from 2.3.7.
    have hax3 : axCLC ((phi_X_set φ Γ) ~> C G ψ), from axCLC.RC hax2,
    obtain ⟨s, hs⟩ := s_f_to_s φ sf,
    -- simp [hs, hcl'],
    have hs_f_sf := s_f_to_s_to_s_f @hs,
    simp [hs, hcl'] at *,
    apply max_ax_contains_by_set_proof s.2 (phi_s_f_in_s φ s),
    rw hs_f_sf,
    exact cut hax1 hax3,
end

lemma truth_lemma_CLC {agents : Type} [ha : nonempty agents] [hN : fintype agents]
  (χ : formCLC agents) (sf : (S_f χ)) (φ) (hχ : subformula φ χ) :
  (s_entails_CLC (@filtered_model_CLC agents hN ha χ) sf φ) ↔ (φ ∈ sf) :=
begin
  -- This proof is by induction on φ.
  induction' φ fixing ha hN φ with n φ ψ _ _ φ ψ _ _, -- sf needs to vary for the modal operators
  all_goals
  { have hs := s_f_to_s χ sf,
    cases hs with s hs, },

  { -- case bot
    simp [s_entails_CLC, s_entails_CLC.aux],
    apply s_f_n_contains,
    exact @hs, 
    apply or.intro_left,
    exact @bot_not_mem_of_ax_consistent (formCLC agents) _ _ s.1 s.2.1, },

  { -- case var
    simpa [s_entails_CLC, s_entails_CLC.aux], },

  { -- case and
    have hφ := subformula.trans (subformula.and_left _ _) hχ,
    have hψ := subformula.trans (subformula.and_right _ _) hχ,
    specialize ih_φ _ sf hφ,
    specialize ih_ψ _ sf hψ,
    unfold s_entails_CLC s_entails_CLC.aux at *,
    rw [ih_φ, ih_ψ, hs, hs, hs],
    simp only [hφ.mem_cl, hψ.mem_cl, hχ.mem_cl, and_true],
    split,
    { rintro ⟨hφs, hψs⟩,
      apply max_ax_contains_by_set_proof_2h s.2 hφs hψs axCLC.Prop4 },
    { intro hφψs,
      split,
      { apply max_ax_contains_by_set_proof s.2 hφψs axCLC.Prop5 },
      { apply max_ax_contains_by_set_proof s.2 hφψs axCLC.Prop6 } } },

  { -- case imp
    have hφ := subformula.trans (subformula.imp_left _ _) hχ,
    have hψ := subformula.trans (subformula.imp_right _ _) hχ,
    specialize ih_φ _ sf hφ,
    specialize ih_ψ _ sf hψ,
    unfold s_entails_CLC s_entails_CLC.aux at *,
    rw [ih_φ, ih_ψ, hs, hs, hs],
    simp only [hφ.mem_cl, hψ.mem_cl, hχ.mem_cl, and_true],
    split,

    { intro h,
      exact max_ax_contains_imp_by_proof s.2 h, },

    { intros h hφ,
      exact max_ax_contains_by_set_proof_2h s.2 hφ h likemp, }, },

  { -- case [G] ψ
    -- have hE : (filtered_model_CLC χ).f.E.E = E_f, from rfl,
    have hφ := subformula.trans (subformula.effectivity _ _) hχ,
    let ih := λ sf, ih _ sf hφ,
    cases em (G = univ) with hG hG,
    { -- case [G]ψ, where G = N :
      calc s_entails_CLC (filtered_model_CLC χ) sf ([G]φ) 
          -- ↔ {sf ∈ Sf | M f , sf ⊨ ψ} ∈ E(sf )(N ), by definition ⊨
          ↔ {t | s_entails_CLC.aux (filtered_model_CLC χ) φ t} ∈ (filtered_model_CLC χ).f.to_frameCL.E.E sf G : 
            by unfold s_entails_CLC s_entails_CLC.aux at *
          -- ↔ ∃t ∈ S, sf = tf and  ̃φ{sf ∈Sf |M f ,sf ⊨ψ} ∈ E(t)(N ), by definition E.
      ... ↔ ∃ t, (∀ x, x ∈ sf ↔ x ∈ t ∧ x ∈ cl χ) ∧ tilde (phi_X_set χ ({sf | s_entails_CLC (filtered_model_CLC χ) sf φ})) ∈ (canonical_model_CLC agents).f.to_frameCL.E.E t (univ) :
          begin
            simp [E_f, hG] { eta := ff },
            split,
            repeat { intro h, apply h, },
          end
          -- ↔ ∃t ∈ S, sf = tf and  ̃φ{sf ∈Sf |ψ∈sf } ∈ E(t)(N ), , by the inductive hypothesis: ∀sf ∈ Sf , M f , sf ⊨ ψ iff ψ ∈ sf .
      ... ↔ ∃ t, (∀ x, x ∈ sf ↔ x ∈ t ∧ x ∈ cl χ) ∧ tilde (phi_X_set χ ({sf | φ ∈ sf} : set (S_f χ))) ∈ (canonical_model_CLC agents).f.to_frameCL.E.E t (univ) :
          by simp only [ih]
          -- ↔ ∃t ∈ S, sf = tf and  ̃ψ ∈ E(t)(N ), by Lemma 6.
      ... ↔ ∃ t, (∀ x, x ∈ sf ↔ x ∈ t ∧ x ∈ cl χ) ∧ tilde φ ∈ (canonical_model_CLC agents).f.to_frameCL.E.E t (univ) :
          by rw tilde_ax_iff χ (phi_X_contains_iff_psi χ φ (subformula.mem_cl hφ))
          -- ↔ ∃t ∈ S, sf = tf and [N ]ψ ∈ E(t)(N ), by Lemma 7.
          -- ↔ [N ]ψ ∈ sf , by definition Sf .
      ... ↔ ([G] φ) ∈ sf : 
          begin
            rw hG,
            split,
            { intro h,
              cases h with t h,
              rw E_s_contains_tilde_iff_E_in_s χ φ t univ at *,
              cases h with heq h,
              apply (heq ([univ] φ)).mpr,
              split,
              { exact h, },
              { simp [hG] at hχ,
                exact subformula.mem_cl hχ, }, },
            { intro h,
              apply exists.intro s,
              split,
              { simp at hs,
                exact @hs, },
              { simp [@hs] at h,
                rw E_s_contains_tilde_iff_E_in_s χ φ s univ at *,
                exact h.left, }, },
          end, },
    { calc s_entails_CLC (filtered_model_CLC χ) sf ([G]φ) 
          -- ↔ {sf ∈ Sf | M f , sf ⊨ ψ} ∈ E(sf )(G), by definition ⊨
          ↔ {t | s_entails_CLC.aux (filtered_model_CLC χ) φ t} ∈ (filtered_model_CLC χ).f.to_frameCL.E.E sf G : 
            by unfold s_entails_CLC s_entails_CLC.aux at *
          -- ↔ ∀t ∈ S, sf = tf ⇒  ̃φ{sf ∈Sf |M f ,sf ⊨ψ} ∈ E(t)(G), by definition E.
      ... ↔ ∀ t, (∀ x, x ∈ sf ↔ x ∈ t ∧ x ∈ cl χ) → tilde (phi_X_set χ ({sf | s_entails_CLC (filtered_model_CLC χ) sf φ})) ∈ (canonical_model_CLC agents).f.to_frameCL.E.E t (G) :
          begin
            simp [E_f, hG] { eta := ff },
            split,
            repeat { intro h, apply h, }
          end
          -- ↔ ∀t ∈ S, sf = tf ⇒  ̃φ{sf ∈Sf |M f ,ψ∈sf } ∈ E(t)(G), by the inductive hypothesis: ∀sf ∈ Sf , M f , sf ⊨ ψ iff ψ ∈ sf .
      ... ↔ ∀ t, (∀ x, x ∈ sf ↔ x ∈ t ∧ x ∈ cl χ) → tilde (phi_X_set χ ({sf | φ ∈ sf})) ∈ (canonical_model_CLC agents).f.to_frameCL.E.E t (G) :
          by simp only [ih]
          -- ↔ ∀t ∈ S, sf = tf ⇒  ̃ψ ∈ E(t)(G), by Lemma 6.
      ... ↔ ∀ t, (∀ x, x ∈ sf ↔ x ∈ t ∧ x ∈ cl χ) → tilde φ ∈ (canonical_model_CLC agents).f.to_frameCL.E.E t (G) :
          by rw tilde_ax_iff χ (phi_X_contains_iff_psi χ φ (subformula.mem_cl hφ))
          -- ↔ ∀t ∈ S, sf = tf ⇒ [G]ψ ∈ t, by Lemma 7.
          -- ↔ [G]ψ ∈ sf , by definition Sf .
      ... ↔ ([G] φ) ∈ sf : 
          begin
            split,
            { intro h,
              specialize h s @hs,
              rw E_s_contains_tilde_iff_E_in_s χ φ s G at h,
              simp only [@hs, subformula.mem_cl hχ, and_true],
              exact h, },
            { intros h t ht,
              rw E_s_contains_tilde_iff_E_in_s χ φ t G,
              apply and.elim_left,
              exact (ht _).mp h, },
          end, }, },
  
  -- case K
  { 
    -- have hK : (filtered_model_CLC χ).f.rel = λ i : agents, λ s : (@filtered_model_CLC agents hN ha χ).f.states, 
  --   {t : (@filtered_model_CLC agents hN ha χ).f.states | {φ : formCLC agents| ((K' i φ) : formCLC agents) ∈ s} = {φ | (K' i φ) ∈ t}},
  --     from rfl,
    have hφ := subformula.trans (subformula.knows _ _) hχ,
    let ih := λ sf, ih _ sf hφ,
    -- unfold s_entails_CLC s_entails_CLC.aux at *
    split,
    { -- ⇒
      simp only [@hs, hφ.mem_cl, hχ.mem_cl, and_true],
      -- 1. Let M f , sf ⊨ Kiψ
      intro h,
      -- 2. ∀tf ∈ Sf , sf ∼fi tf ⇒ M f , tf ⊨ ψ, by the definition of ⊨, from 1.
      unfold s_entails_CLC s_entails_CLC.aux at h ih,
      -- 3. ∀tf ∈ Sf , sf ∼fi tf ⇒ ψ ∈ tf , by the induction hypothesis, from 2.
      simp only [ih] at h,
      -- 4. Assume by contradiction that ¬Kiψ ∈ s.
      by_contradiction hnin,
      have hnk := not_in_from_notin s.2 hnin,
      -- 5. Consider the set Σ = {φ | φ is of the shape Kiχ and φ ∈ sf }.
      let Γ := {ψ : formCLC agents | k a ψ ∈ s},
      -- 6. Σ ∪ {¬ ψ} is consistent.
      have hcon : ax_consistent (Γ ∪ {¬ φ}), from
      begin
        -- 6.1. Assume by contradiction Σ ∪ {¬ψ} is inconsistent.
        by_contradiction hncon,
        -- 6.2. ⊢ (φΣ ∧ ¬ψ) → ⊥, from 6.1.
        have hncon' := five Γ (¬ φ) hncon,
        cases hncon' with ψs hncon', 
        -- 6.3. ⊢ φΣ → ψ, by propositional logic, from 6.2.
        cases hncon' with hΓ hax,
        -- 6.4. ⊢ Ki(φΣ → ψ), by Axiom RN, from 6.3.
        -- 6.5. ⊢ (KiφΣ ) → (Kiψ), by Axiom K, from 6.4.
        have h5 : axCLC ((finite_conjunction (list.map (K a) ψs)) ~> k a (φ)), from by
        begin 
          apply @cut (formCLC agents),
          apply @knows_conjunction agents hN (formCLC agents) _,
          apply axCLC.MP axCLC.K,
          apply axCLC.RN,
          simp at hax,
          apply @cut (formCLC agents),
          exact hax,
          exact dne,
        end,
        -- 6.6. ⊢ φΣ → KiφΣ , by Axiom K, and propositional logic.
        have h6 := exercise1,
        -- 6.7. φΣ ∈ s, by definition Sigma, from 5.
        -- 6.8. Kiψ ∈ s, from 6.5, 6.6 & 6.7.
        have h7 : ∀ ψ ∈ (list.map (K a) ψs), ψ ∈ s, from
        begin
          intros ψ h8, simp at *, cases h8 with a h8,
          cases h8 with h8l h8r,
          subst h8r, exact hΓ a h8l,
        end,
        specialize h6 s.2 h7 h5,
        have h8 := (max_ax_contains_phi_xor_neg s.1 (max_imp_ax s.2)).mp s.2 (K a (φ)),
        cases h8 with h8l h8r, simp at *, 
        -- 6.9. Contradiction from 4 and 6.8.
        apply (h8r h6),
        exact hnk,
      end,
      -- 7. ∃u ∈ S, sf ∼fi u and ¬ψ ∈ uf , from 6, based on the definitions of ∼fi and Σ.
      obtain ⟨t', ht, hsub⟩ := lindenbaum hcon,
      let t : (canonical_model_CLC agents).f.to_frameCL.states := ⟨t', ht⟩,
      have h5 := set.union_subset_iff.mp hsub,
      simp at h5,
      cases h5,
      have hnin : (¬ φ) ∈ t, from h5_right,
      simp at hnin,
      obtain ⟨tf, htf⟩ := s_to_s_f χ t,
      have hrel : tf ∈ (filtered_model_CLC χ).f.rel a sf, from
      begin
        simp,
        ext1,
        split,
        { simp [@hs, htf],
          intros hks hcl,
          split,
          { apply mem_of_mem_of_subset _ h5_left,
            simp only [Γ],
            apply max_ax_contains_by_set_proof s.2 hks axCLC.Four, },
          { exact hcl, },
        },
        { simp [@hs, htf],
          intros hkt hcl,
          split,
          { by_contradiction hnks,
            have hnks' := not_in_from_notin s.2 hnks,
            have hknks := max_ax_contains_by_set_proof s.2 hnks' axCLC.Five,
            have hnkΓ : (¬ k a x) ∈ Γ, from hknks,
            have hnkt : (¬ k a x) ∈ t.1, from mem_of_mem_of_subset hnkΓ h5_left,
            exact contra_containts_pr_false t.2 hkt hnkt, },
          { exact hcl, },
        },
      end,
      specialize h tf hrel,
      simp [@hs, htf] at h,
      -- 8. Contradiction from 3 & 7.
      apply contra_containts_pr_false t.2 h.left hnin, },
    {  -- ⇐
      -- 1. Let Kiψ ∈ sf .
      intro h,
      -- 2. Consider any tf ∈ Sf , such that sf ∼f i tf .
      -- 3. {χ | Kiχ ∈ sf } = {χ | Kiχ ∈ tf }, by definition ∼f i , from 2.
      unfold s_entails_CLC s_entails_CLC.aux at *,
      dsimp,
      intros tf htf,
      obtain ⟨t, ht⟩ := s_f_to_s χ tf,
      -- simp at tf,
      -- 4. Kiψ ∈ tf , from 1 & 3.
      have hkt : (K' a φ) ∈ tf, from 
      begin
        simp [ext_iff] at htf,
        exact (htf φ).mp h, 
      end,
      -- 5. ψ ∈ tf , by Axiom T, from 4.
      have hφt : φ ∈ tf, from
      begin
        simp only [ht, hφ.mem_cl, hχ.mem_cl, and_true] at *,
        exact max_ax_contains_by_set_proof t.2 hkt.left axCLC.T,
      end,
      -- 6. ∀tf ∈ Sf , sf ∼fi tf ⇒ ψ ∈ tf , from 2 & 5.
      -- 7. ∀tf ∈ Sf , sf ∼fi tf ⇒ M f , tf ⊨ ψ, by the induction hypothesis, from 6.
      simp only [ih],
      -- 8. M f , sf ⊨ Kiψ, by the definition of ⊨, from 7.
      exact hφt, }, },
  
  -- case E
  { have hφ := subformula.trans (subformula.everyone_knows _ _) hχ,
    let ih := λ sf, ih _ sf hφ,
    unfold s_entails_CLC s_entails_CLC.aux at *,
    dsimp,
    split,
    { intro h,
      sorry,
    },
    { intro h,
      sorry,
    },

  },

  -- case C
  { have hφ := subformula.trans (subformula.common_know _ _) hχ,
    let ih := λ sf, ih _ sf hφ,
    unfold s_entails_CLC s_entails_CLC.aux at *,
    simp [ih],
    have hcl : φ ∈ cl χ, from subformula.mem_cl hφ,
    have hcl' : c G φ ∈ cl χ, from subformula.mem_cl hχ,
    have hcl'' : ∀ i ∈ G, (K i (C G φ)) ∈ cl χ, 
      from λ i hi, finset.subset_iff.mp (subformula.cl_subset hχ) (by simp [cl, cl_C, hi]),

    -- 2. CGψ ∈ sf ⇒ ∀sn ∈ S that are reachable from sf by some path sf ∼f i1 sf1 ∼fi2 ... ∼f in sfn, 
      -- where {i1, i2..in} ⊆ G, then ψ ∈ sfn and CGψ ∈ sfn
    -- have hl := truth_C_helper' _ _ hcl hcl' hcl'',
    -- have hr := truth_C_helper'' hcl hcl' hcl'',

    -- 3. (∀sn ∈ S that are reachable from sf by some path sf ∼fi1 sf1 ∼fi2 ... ∼finsfn, where {i1, i2..in} ⊆ G, then ψ ∈ sfn) ⇒ CGψ ∈ sf .
    -- 4. CGψ ∈ sf ⇔ ∀sn ∈ S if sf n is reachable from sf by some path sf ∼fi1 sf1 ∼fi2 ... ∼fin sf n, 
      -- where {i1, i2..in} ⊆ G, then ψ ∈ sfn, from 2 & 3.
    split,
    { intros h,
      exact truth_C_helper'' hcl hcl' hcl'' h, },
    { intros hsf tf is his sfs hC,
      exact (truth_C_helper' his hsf hcl hcl' hcl'' tf hC).left, },
    -- 5. CGψ ∈ sf ⇔ ∀sn ∈ S if sfn is reachable from sf by some path sf ∼fi1 sf1 ∼fi2 ... ∼f in sfn, where {i1, i2..in} ⊆ G, then M f , sfn ⊨ ψ, from 1 & 4.
    -- 6. CGψ ∈ sf ⇔ M f , sf ⊨ CGψ, by definition ⊨, from 5.
  },
end

----------------------------------------------------------
-- Completeness
----------------------------------------------------------

-- Completeness
----------------------------------------------------------
theorem completenessCLC {agents : Type} [h : fintype agents] (φ : formCLC agents) [ha : nonempty agents] : 
  global_valid φ → axCLC φ :=
begin
  -- rw from contrapositive
  rw ←not_imp_not, 
  -- assume ¬ ⊢ φ
  intro hnax,
  -- from ¬ ⊢ φ, have that {¬ φ} is a consistent set
  obtain ⟨s, hmax, hnφ⟩ := @exists_max_ax_consistent_neg_mem (formCLC agents) _ _ _ hnax,
  -- show that φ is not globally valid, 
  -- by showing that there exists some model where φ is not valid.
  simp[global_valid],
  -- let that model be the canonical model
  apply exists.intro (filtered_model_CLC φ),
  -- in the canonical model (M) there exists some state (s) where ¬ M s ⊨ φ
  simp[valid_m],
  -- let that state (s) be the maximally consistent set extended from {¬ φ}
  obtain ⟨sf, hsf⟩ := s_to_s_f φ (subtype.mk s hmax),
  apply exists.intro sf,
  -- assume by contradiction that M s ⊨ φ
  intro hf,
  -- by the truth lemma φ ∈ s
  have hsub: subformula φ φ, from subformula.refl φ,
  have hφ, from (truth_lemma_CLC φ _ φ hsub).mp hf,
  -- in that state (s), φ ∈ s, so we do not have ¬ φ ∈ s (by consistency)
  -- contradiction with hnφ
  rw hsf at hφ,
  simp at hφ,
  apply contra_containts_pr_false hmax hφ.left hnφ,
end

end canonical
