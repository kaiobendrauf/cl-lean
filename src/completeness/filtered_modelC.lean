import completeness.filteringC


local attribute [instance] classical.prop_decidable

open set formCLC

namespace canonical


----------------------------------------------------------
-- Definitions and Lemmas needed for completness / model construction
----------------------------------------------------------
-- Tilde
----------------------------------------------------------
def tilde {agents : Type} [hN : fintype agents] [ha : nonempty agents] (ψ : formCLC agents) : 
  set ((canonical_model_CLC agents).f.states) :=
{s : (canonical_model_CLC agents).f.states | ψ ∈ s}

lemma h_tilde_compl {agents : Type} [hN : fintype agents] [ha : nonempty agents] (ψ : formCLC agents) : 
  tilde (¬ ψ) = (tilde ψ)ᶜ := 
begin
  ext,
  simp[tilde],
  split,
  { intros hx hf,
    exact contra_containts_pr_false x.2 hf hx, },
  { intros hx,
    exact not_in_from_notin x.2 hx, },
end

-- phi sf
----------------------------------------------------------
noncomputable def phi_s_f {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (sf : S_f φ) : formCLC agents :=
finite_conjunction (finset.to_list (sf.1))

-- phi sf ∈ s
lemma phi_s_f_in_s {agents : Type} [hN : fintype agents] [ha : nonempty agents] (φ : formCLC agents)
  (s : (canonical_model_CLC agents).f.states):
  phi_s_f φ ((s_f φ s)) ∈ s :=
begin
  simp[phi_s_f],
  have hinduct : ∀ fs : list (formCLC agents), 
    (fs ⊆ ((s_f φ s).1 : finset (formCLC agents)).to_list) → finite_conjunction fs ∈ s, from
  begin
    intros fs hfs,
    induction fs with f fs ih,
    { simp[finite_conjunction],
      exact @max_ax_contains_by_empty_proof (formCLC agents) _ _ _ _ s.prop prtrue, },
    { simp[finite_conjunction] at *,
      cases hfs with hf hfs,
      have hf_in_s : f ∈ s, from s_f_subset_s φ s hf,
      have hfs_in_s : finite_conjunction fs ∈ s, from ih hfs,
      apply max_ax_contains_by_set_proof_2h s.2 hf_in_s hfs_in_s,
      exact axCLC.Prop4, },
  end,
  apply hinduct,
  simp,
end

lemma phi_s_f_forall_iff {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  {φ : formCLC agents} (sf : S_f φ) : 
  (∀ x : formCLC agents, x ∈ sf → axCLC x) ↔ axCLC (phi_s_f φ sf) :=
begin
  unfold phi_s_f,
  have h_con := @finite_conj_forall_iff (formCLC agents) _ _ (sf.1.1).to_list,
  split,
  { intro h,
    apply h_con.mp,
    intros x hx,
    apply h,
    have hx : x ∈ sf.1.1, from (multiset.mem_to_list x _).mp hx,
    exact hx, },
  { intros h x hx,
    apply h_con.mpr,
    exact h,
    rw multiset.mem_to_list,
    exact hx, },
end

lemma phi_s_f_forall_imp {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  {φ : formCLC agents} {sf : S_f φ} : 
  (∀ x ∈ sf, axCLC ((phi_s_f φ sf) ~> x)) := 
begin
  unfold phi_s_f,
  intros x hx,
  have hx : x ∈ sf.1.1.to_list, from (multiset.mem_to_list x _).mpr hx,
  exact @finite_conj_forall_imp (formCLC agents) _ _ (sf.1.1).to_list x (hx),
end

lemma notin_nphi_s_f {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  {φ ψ : formCLC agents} {sf : S_f φ} (h : ψ ∈ sf): 
  (axCLC ((¬ ψ) ~> ¬ phi_s_f φ sf)) :=
begin
  unfold phi_s_f,
  apply @noin_imp_nfin_con (formCLC agents) _ _ _ ψ,
  simp, apply h,
end

lemma phi_s_f_conj_contains_ax {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  {φ ψ : formCLC agents} (sf : S_f φ) (hψ : ψ ∈ sf) : 
  axCLC (phi_s_f φ sf) ↔ axCLC (ψ & (phi_s_f φ sf)) :=
begin
  split,
  { intro h,
    apply @and_ax (formCLC agents),
    exact (phi_s_f_forall_iff sf).mpr h ψ hψ,
    exact h, },
  { intro h,
    apply and.elim_right,
    apply (@ax_and (formCLC agents) _ _ ψ (phi_s_f φ sf)).mp,
    exact h, },
end

lemma phi_s_f_conj_contains {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  {φ ψ : formCLC agents} (sf : S_f φ) (hψ : ψ ∈ sf) : 
  axCLC ((phi_s_f φ sf) <~> (ψ & (phi_s_f φ sf))) :=
begin
  apply @ax_iff_intro (formCLC agents),
  { apply imp_imp_and,
    exact phi_s_f_forall_imp _ hψ,
    exact iden, },
  { refine imp_and_r _,
    exact iden, },
end

-- phi X (given a list)
----------------------------------------------------------
noncomputable def phi_X_list {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) :
  list (S_f φ) → list (formCLC agents)
| list.nil   := list.nil
| (sf :: ss) := ((phi_s_f φ sf) :: phi_X_list ss)

-- if sf ∈ X, then phi sf is one of the disjuncts in phi X.
lemma phi_X_list_contains {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (sfs : list (S_f φ)) (sf : (S_f φ)) (hs : sf ∈ sfs) :
  (phi_s_f φ sf) ∈ phi_X_list φ sfs :=
begin
  induction sfs with hd sfs ih,
  {by_contradiction, simp at *, exact hs, },
  { cases hs,
    { simp[hs, phi_X_list], },
    { simp[phi_X_list] at *,
      apply or.intro_right,
      exact ih hs, }, },
end

lemma phi_X_list_subset {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (sfs : list (S_f φ)) (sfs' : list (S_f φ)) (h : sfs ⊆ sfs') :
  phi_X_list φ sfs ⊆ phi_X_list φ sfs' :=
begin
  induction sfs with hd sfs ih,
  { simp[phi_X_list], },
  { simp[phi_X_list] at *,
    split,
    { exact phi_X_list_contains φ _ _ h.left, },
    { exact ih h.right, }, },
end

lemma phi_X_list_append {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : list (S_f φ)) :
  phi_X_list φ (X ++ Y) ⊆ phi_X_list φ X ++ phi_X_list φ Y :=
begin
  induction X with hd X ih,
  { simp[phi_X_list], },
  { simp[phi_X_list] at *,
    exact list.subset_cons_of_subset (phi_s_f φ hd) ih, },
end

lemma phi_X_list_single {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (sf : (S_f φ)) :
  axCLC ((phi_s_f φ sf) ↔' finite_disjunction (phi_X_list φ (sf :: list.nil))) :=
begin
  apply @ax_iff_intro (formCLC agents),
  { unfold phi_X_list finite_disjunction,
    apply cut,
    exact dni,
    exact iden, },
  { unfold phi_X_list finite_disjunction,
    exact dne, },
end

lemma phi_X_list_conj_contains {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  {φ ψ : formCLC agents} {X : list (S_f φ)} (hψ : ∀ sf, sf ∈ X → ψ ∈ sf) : 
  axCLC (finite_disjunction (phi_X_list φ X) <~> (ψ & finite_disjunction (phi_X_list φ X))) :=
begin
  induction X with sf X ih,
  { simp [phi_X_list, finite_disjunction],
    apply @and_ax (formCLC agents),
    exact explosion,
    exact imp_and_r iden, },
  { simp [phi_X_list, finite_disjunction],
    apply @and_ax (formCLC agents),
    { apply or_cases,
      { apply imp_imp_and,
        { apply cut,
          apply iff_l,
          apply phi_s_f_conj_contains sf,
          apply hψ,
          simp,
          exact p5 _ _, },
        { exact contra_explosion, }, },
      { have hψ' : ∀ sf, sf ∈ X → ψ ∈ sf, from
        begin
          intros tf htf,
          apply hψ,
          simp [htf],
        end,
        specialize ih hψ',
        have ih := (@ax_and (formCLC agents) _ _ _ _).mp ih,
        apply imp_imp_and,
        { apply cut,
          exact ih.left,
          exact p5 _ _, },
        { exact p1 _ _, }, }, },
      { exact p6 _ _, }, },
end

lemma phi_X_list_exists {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  {φ : formCLC agents} {X : list (S_f φ)} {s : (canonical_model_CLC agents).f.states} 
  (hfa : ∀ x, x ∈ X → phi_s_f φ x ∉ s) : (¬' (finite_disjunction (phi_X_list φ X))) ∈ s :=
begin
  induction X with x X ih,
  { simp only [phi_X_list, finite_disjunction],
    apply max_ax_contains_by_empty_proof s.2 not_bot, },
  { simp only [phi_X_list, finite_disjunction] at *,
    simp at hfa,
    apply max_ax_contains_by_set_proof s.2 _ (iff_r demorgans''''),
    apply max_ax_contains_by_set_proof_2h s.2 _ _ (axCLC.Prop4),
    exact not_in_from_notin s.2 hfa.left,
    exact ih hfa.right, },
end

lemma nk_phi_X_list_exists {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  {φ : formCLC agents} {i : agents} {X : list (S_f φ)} {s : (canonical_model_CLC agents).f.states} 
  (hfa : ∀ x, x ∈ X → ¬' (K' i (¬'(phi_s_f φ x))) ∉ s) : 
  (¬' (finite_disjunction (list.map (λ (φ : formCLC agents), ¬' (K' i (¬' φ))) (phi_X_list φ X)))) ∈ s :=
begin
  induction X with x X ih,
  { simp only [phi_X_list, finite_disjunction],
    apply max_ax_contains_by_empty_proof s.2 not_bot, },
  { simp only [phi_X_list, finite_disjunction] at *,
    simp at hfa,
    apply max_ax_contains_by_set_proof s.2 _ (iff_r demorgans''''),
    apply max_ax_contains_by_set_proof_2h s.2 _ _ (axCLC.Prop4),
    exact not_in_from_notin s.2 hfa.left,
    exact ih hfa.right, },
end


-- phi X (given a finset)
----------------------------------------------------------
noncomputable def phi_X_finset {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X : finset (S_f φ)) :
  formCLC agents :=
finite_disjunction (phi_X_list φ (finset.to_list X))

lemma phi_X_subset_Y_imp {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : finset (S_f φ)) (hXY : X ⊆ Y) :
  axCLC ((phi_X_finset φ X) →' (phi_X_finset φ Y)) :=
begin
  simp[phi_X_finset],
  apply imp_finite_disjunction_subset (phi_X_list φ X.to_list) (phi_X_list φ Y.to_list),
  apply phi_X_list_subset,
  intros f hf,
  rw finset.mem_to_list at *,
  exact hXY hf,
end

lemma phi_X_list_append' {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : finset (S_f φ)) :
  phi_X_list φ X.to_list ++ phi_X_list φ Y.to_list ⊆ phi_X_list φ (X ∪ Y).to_list :=
begin
  simp at *,
  split,
  { apply phi_X_list_subset,
    intros f hf,
    rw finset.mem_to_list at *,
    exact finset.mem_union_left Y hf, },
 {  apply phi_X_list_subset,
    intros f hf,
    rw finset.mem_to_list at *,
    exact finset.mem_union_right X hf, }, 
end

lemma phi_X_list_append'' {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : finset (S_f φ)) :
  phi_X_list φ (X ∪ Y).to_list ⊆ phi_X_list φ X.to_list ++ phi_X_list φ Y.to_list :=
begin
  have h1 := phi_X_list_append φ X.to_list Y.to_list,
  have h2 : phi_X_list φ (X ∪ Y).to_list ⊆ phi_X_list φ (X.to_list ++ Y.to_list), from
  begin
    refine phi_X_list_subset φ (X ∪ Y).to_list (X.to_list ++ Y.to_list) _,
    intros f hf,
    simp at *,
    exact hf,
  end,
  exact subset.trans h2 h1,
end

lemma phi_X_finset_union {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : finset (S_f φ)) :
  axCLC ((¬' (phi_X_finset φ X) →' (phi_X_finset φ Y)) →' (phi_X_finset φ (X ∪ Y))) :=
begin
  simp[phi_X_finset],
  apply @cut (formCLC agents),
  apply disjunc_disjunct,
  apply imp_finite_disjunction_subset,
  apply phi_X_list_append',
end

lemma phi_X_finset_disjunct_of_disjuncts {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : finset (S_f φ)) :
  axCLC (¬' (phi_X_finset φ X) →' (phi_X_finset φ Y)) ↔ axCLC (phi_X_finset φ (X ∪ Y)) :=
begin
  have hax := @ax_iff_disjunc_disjunct (formCLC agents) _ _
              (phi_X_list φ X.to_list) (phi_X_list φ Y.to_list),
  simp[phi_X_finset],
  split,
  { intro h,
    apply @MP' (formCLC agents),
    apply hax.mp h,
    apply imp_finite_disjunction_subset,
    apply phi_X_list_append', },
  { intro h,
    apply hax.mpr,
    apply @MP' (formCLC agents),
    apply h,
    apply imp_finite_disjunction_subset,
    apply phi_X_list_append'',
  },
end

-- lemma phi_X_list_conj_contains {agents : Type} [hN : fintype agents] [ha : nonempty agents]
--   {φ ψ : formCLC agents} (X : finset (S_f φ)) (hψ : ∀ sf ∈ X, ψ ∈ sf) : 
--   axCLC (ψ & (phi_X_finset φ X)) :=
-- begin
--   unfold phi_X_finset,
-- end



-- phi X (given a set)
----------------------------------------------------------

/-- `phi_X_set φ X` is a finite disjunction of all elements of `X`. -/
noncomputable def phi_X_set {agents : Type} [hN : fintype agents] [ha : nonempty agents]  
  (φ : formCLC agents) (X : set (S_f φ)) :
  formCLC agents :=
begin
  simp[S_f, finset.attach] at X,
  have hX : finite X, from finite.of_fintype X,
  have X : finset (S_f φ), from finite.to_finset hX,
  exact phi_X_finset φ X,
end

lemma phi_X_set_subset_Y_imp {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X : set (S_f φ)) (Y : set (S_f φ)) (hXY : X ⊆ Y) :
  axCLC ((phi_X_set φ X) →' (phi_X_set φ Y)) :=
begin
  simp[phi_X_set],
  apply phi_X_subset_Y_imp,
  exact finite.to_finset_mono.mpr hXY,
end

lemma phi_X_set_disjunct {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : set (S_f φ)) :
  axCLC ((¬' (phi_X_set φ X) →' (phi_X_set φ Y)) →' (phi_X_set φ (X ∪ Y))) :=
begin
  unfold phi_X_set,
  apply @cut (formCLC agents),
  apply phi_X_finset_union,
  apply phi_X_subset_Y_imp,
  apply finset.union_subset,
  repeat { simp,},
end

lemma phi_X_set_disjunct_of_disjuncts {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : set (S_f φ)) :
  axCLC (¬' (phi_X_set φ X) →' (phi_X_set φ Y)) ↔ axCLC (phi_X_set φ (X ∪ Y)) :=
begin
  unfold phi_X_set,
  split,
  { intro h,
    have hax := (phi_X_finset_disjunct_of_disjuncts φ _ _).mp,
    specialize hax h,
    apply @MP' (formCLC agents),
    apply hax,
    apply phi_X_subset_Y_imp,
    apply finset.union_subset,
    repeat { simp, }, },
  { intro h,
    apply (phi_X_finset_disjunct_of_disjuncts φ _ _).mpr,
    apply @MP' (formCLC agents),
    apply h,
    apply phi_X_subset_Y_imp,
    refine finset.subset_iff.mpr _,
    intros f hf,
    simp at *,
    exact hf, },
end

lemma phi_X_set_exists {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  {φ : formCLC agents} {X : set (S_f φ)} {s : (canonical_model_CLC agents).f.states} 
  (h : phi_X_set φ X ∈ s) : ∃ tf ∈ X, phi_s_f φ tf ∈ s :=
begin
  by_contradiction hfa,
  simp at hfa,
  apply in_from_not_notin s.2 h,
  unfold phi_X_set phi_X_finset,
  apply phi_X_list_exists,
  intros sf hsf,
  apply hfa,
  simp [finite.mem_to_finset] at hsf,
  exact hsf,
end

section lemmas

-- Motivation: self-contained `have`-block
@[simp] lemma tilde_empty {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  {φ : formCLC agents} : (tilde (phi_X_set φ ∅)) = ∅ :=
begin
  -- 1.1.1. φ∅ = ⊥, because φ∅ is an empty disjunction, thus  ̃φ∅ =  ̃⊥.
  simp [phi_X_set, phi_X_finset, phi_X_list, finite_disjunction, tilde],
  -- 1.1.2.  ̃⊥ = ∅, because all s ∈ S are consistent.
  simp [eq_empty_iff_forall_not_mem],
  intro s,
  exact bot_not_mem_of_ax_consistent s.1 s.2.1
end

lemma tilde_ax_iff {agents : Type} [hN : fintype agents] [ha : nonempty agents] (φ : formCLC agents)
  {ψ χ : formCLC agents} (hax : axCLC (ψ <~> χ)) : 
  tilde ψ = tilde χ :=
begin
  unfold tilde,
  ext1 s,
  split,
  { intro hs,
    simp at *,
    apply max_ax_contains_by_set_proof s.2 hs,
    apply iff_l,
    apply hax, },
  { intro hs,
    simp at *,
    apply max_ax_contains_by_set_proof s.2 hs,
    apply iff_r,
    apply hax, },
end

-- Motivation: simple way to prove `phi_X_set`
lemma ax_phi_s_f_imp_phi_X_set_of_mem {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  {φ : formCLC agents} {t} {X : set _} (h : s_f φ t ∈ X) :
  ax (phi_s_f φ (s_f φ t) →' phi_X_set φ X) :=
begin
  simp [phi_X_set],
  apply @imp_finite_disjunction (formCLC agents) _ _ (phi_s_f φ (s_f φ t)),
  apply phi_X_list_contains φ,
  simpa,
end

lemma ax_phi_s_f_imp_phi_X_set_of_mem' {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  {φ : formCLC agents} {sf} {X : set _} (h : sf ∈ X) :
  ax (phi_s_f φ (sf) →' phi_X_set φ X) :=
begin
  simp [phi_X_set],
  apply @imp_finite_disjunction (formCLC agents) _ _ (phi_s_f φ (sf)),
  apply phi_X_list_contains φ,
  simpa,
end

-- Main Lemmas
----------------------------------------------------------
-- Lemma 4. ⊢ (∨ {sf ∈Sf } φsf)
lemma univ_disjunct_provability {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  (φ : formCLC agents) (hs : nonempty (S_f φ)):
  ax (phi_X_set φ (univ : set (S_f φ))) :=
begin
  -- 1. By contradiction, assume that ⊬ (∨ {sf ∈Sf } φsf)
  by_contradiction,
  -- 3. ¬(∨ {sf ∈Sf } φsf) ∈ t, because t is maximally consistent, from 1.
  obtain ⟨t', hexn, htn⟩ := exists_max_ax_consistent_neg_mem h,
  let t := (⟨t', hexn⟩ : (canonical_model_CLC agents).f.states),
  -- 4. ⊢ φtf → (∨ {sf ∈Sf } φsf ), by propositional logic, because t ∈ Sf.
  have himp : ax (phi_s_f φ (s_f φ t) →' phi_X_set φ univ),
    from ax_phi_s_f_imp_phi_X_set_of_mem (mem_univ _),
  -- 5. φtf∈ t, by propositional logic, because all ∀ψ ∈ tf , ψ ∈ t).
  have hphitf : phi_s_f φ (s_f φ t) ∈ t.1, from phi_s_f_in_s φ t, 
  -- 6. (∨{sf ∈Sf } φsf) ∈ t, by propositional logic, from 4 & 5.
  have ht : phi_X_set φ (univ : set (S_f φ)) ∈ t.1, 
    from max_ax_contains_by_set_proof t.2 hphitf himp,
  -- 7. Contradiction from 3 and 6.
  apply contra_containts_pr_false t.2 ht htn,
end

-- Motivation: self-contained `have`-block
-- 2.1. First we note that  ̃φSf =  ̃⊤ = S
@[simp] lemma tilde_univ {agents : Type} [hN : fintype agents] [ha : nonempty agents] {φ : formCLC agents} :
  (tilde (phi_X_set φ (univ : set (S_f φ)))) = (univ : set (canonical_model_CLC agents).f.states) :=
begin
  simp[tilde],
  ext1,
  refine iff_of_true _ trivial,
  simp,
  apply max_ax_contains_by_empty_proof x.2,
  apply univ_disjunct_provability,
  exact canonical.nonempty_S_f φ,
end

-- Lemma 5. ∀sf , tf ∈ Sf , sf ̸ = tf ⇒⊢ φsf→ ¬φtf
lemma unique_s_f_helper {agents : Type} [hN : fintype agents] [ha : nonempty agents]  
  {φ x : formCLC agents} (sf  tf : (S_f φ)) (hxf : x ∈ sf) (hnf : x ∉ tf) :
  axCLC (¬' (phi_s_f φ sf ∧' phi_s_f φ tf)) := 
begin
  -- -- 6. χ /∈ t, from 5, by definition Sf , because χ ∈ cl(φ).
  -- -- 7. ¬χ ∈ t, from 6, because s and t are maximally consistent.
  -- -- 8. ∃ψ, (ψ ↔ ¬χ) ∧ (ψ ∈ cl(φ)), because cl is closed under single negations.
  -- -- 9. ψ ∈ s ∨ ψ ∈ t, from 7 & 8, because s and t are maximally consistent.
  -- -- 10. ψ ∈ sf ∨ ψ ∈ tf , from 8 & 9, by definition Sf .
  have hst := s_f_closed hnf (finset.subset_iff.mp (s_f_subset_cl φ _) hxf),
  cases hst with ψ hst,
  cases hst with hst hψ,
  -- 11. φsf ∧ φtf → ⊥, by propositional logic, from 5, 8 & 10.
  simp[phi_s_f],
  apply @contra_con_cons (formCLC agents) _ _,
  exact hψ,
  exact (sf.1.1).mem_to_list.mpr hxf,
  exact (tf.1.1).mem_to_list.mpr hst,
end

lemma unique_s_f {agents : Type} [hN : fintype agents] [ha : nonempty agents]  
  {φ : formCLC agents} (sf  tf : (S_f φ)) (hneq : sf ≠ tf) :
  ax (phi_s_f φ sf →' ¬' (phi_s_f φ tf)) :=
begin
  -- 1. Assume by contradiction ⊬ φsf → ¬φtf
  by_contradiction,
  -- 2. ∃u ∈ S, (φsf → ¬φtf) /∈ u, from 1.
  -- 3. ¬(φsf→ ¬φtf) ∈ u, from 2.
  obtain ⟨u', hexn.left, hun⟩ := exists_max_ax_consistent_neg_mem h,
  let u := (⟨u', hexn.left⟩ : (canonical_model_CLC agents).f.states),
  have hun : ¬' (phi_s_f φ sf →' ¬' (phi_s_f φ tf)) ∈ u.1, from by tauto,
  -- 4. φsf ∧ φtf ∈ u, by propositional logic, from 3.
  have hand : (phi_s_f φ sf ∧' (phi_s_f φ tf)) ∈ u.1,
    from max_ax_contains_by_set_proof u.2 hun demorgans'',
  -- 5. ∃χ ∈ sf ∪ tf , χ /∈ sf ∨ χ /∈ tf , because sf and tf are not identical.
  have : ¬(sf.1.1 ⊆ tf.1.1) ∨ ¬(tf.1.1 ⊆ sf.1.1), from
  begin
    { rw ← not_and_distrib,
      rintro ⟨hst, hts⟩,
      apply hneq,
      ext : 2,
      exact subset_antisymm hst hts },
  end,
    obtain ⟨x, hun, hneq'⟩ : ∃ f, f ∈ (sf.1.1 ∪ tf.1.1) ∧ ((f ∉ sf.1.1) ∨ (f ∉ tf.1.1)),
    { simp only [finset.not_subset] at this, -- Motivation: I recall `not_subset` had something like `x ∈ s ∧ ¬ x ∈ t` so I reworked the statement to make it come true.
      rcases this with ⟨x, hxu, hxn⟩ | ⟨x, hxu, hxn⟩;
        use x;
        simp only [finset.mem_union, hxu, hxn, not_true, not_false_iff, true_or, or_true, true_and] },
  rw finset.mem_union at hun,

  -- 11. φsf ∧ φtf → ⊥, from helper  (6-10)
  -- 12. ⊥ ∈ u, by propositional logic, from 4 & 11, which contradicts the consistency of u.
  apply ax_neg_containts_pr_false u.2 hand,
  cases hun with hxf hxf,
  { cases hneq' with hnf hnf,
    { finish, },
    { apply unique_s_f_helper _ _ hxf hnf, }, },
  { cases hneq' with hnf hnf,
    { apply cut (iff_l and_switch),
      apply unique_s_f_helper _ _ hxf hnf, },
    { finish, }, },
end

lemma phi_X_list_unique {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : list (S_f φ)) (hXY : X.disjoint Y) (hX : list.nodup X) (hY : list.nodup Y) :
  axCLC (finite_disjunction (phi_X_list φ X)→' ¬' (finite_disjunction (phi_X_list φ Y))) :=
begin
  induction' X with x X ihx,
  { simp [phi_X_list, finite_disjunction],
    apply @explosion (formCLC agents), },
  { simp [phi_X_list, finite_disjunction],
    apply @or_cases (formCLC agents),
    { induction Y with y Y ihy,
      { simp [phi_X_list, finite_disjunction],
        apply MP',
        apply not_bot,
        apply axCLC.Prop1, },
      { simp [phi_X_list, finite_disjunction] at *,
        rw ←contrapos,
        apply cut,
        apply dne,
        apply or_cases,
        apply unique_s_f, 
        by_contradiction,
        simp[h] at hXY,
        exact hXY,
        rw ←contrapos,
        apply cut,
        apply dne,
        apply ihy hY.right,
        exact hXY.2.1,
        exact hXY.2.2, }, },
    { apply ihx,
      exact hY,
      apply list.disjoint_of_disjoint_cons_left hXY,
      simp at hX,
      exact hX.2, }, },
end

lemma phi_X_finset_unique {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : finset (S_f φ)) (hXY : X ∩ Y = ∅) :
  axCLC ((phi_X_finset φ X) →' ¬' (phi_X_finset φ (Y))) :=
begin
  simp[phi_X_finset],
  apply phi_X_list_unique,
  rw list.disjoint_left,
  intros f hf,
  simp at *,
  by_contradiction,
  exact finset.eq_empty_iff_forall_not_mem.mp hXY f (finset.mem_inter_of_mem hf h),
  repeat {exact finset.nodup_to_list _, },
end

lemma phi_X_set_unique {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : set (S_f φ)) (hXY : X ∩ Y = ∅) :
  axCLC ((phi_X_set φ X) →' ¬' (phi_X_set φ (Y))) :=
begin
  simp[phi_X_set],
  apply phi_X_finset_unique,
  apply finset.eq_empty_iff_forall_not_mem.mpr,
  intros f hf,
  simp at *,
  exact eq_empty_iff_forall_not_mem.mp hXY f ((mem_inter_iff f X Y).mpr hf),  
end

lemma contra_fin_disjunct_psi_and_not {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  {φ ψ : formCLC agents} (hψ : ψ ∈ cl φ) (sfs : list (S_f φ)) 
  (hsfs : ∀ sf : (@S_f agents _ ha φ), sf ∈ sfs → ψ ∉ sf) :
  axCLC (⊥' <~> (ψ & finite_disjunction (phi_X_list φ sfs))) :=
begin
  apply @ax_iff_intro (formCLC agents),
  exact explosion,
  induction sfs with sf sfs ih,
  { unfold phi_X_list finite_disjunction,
    exact p6 _ _, },
  { unfold phi_X_list finite_disjunction at *,
    have hsfs' : ∀ sf : (@S_f agents _ ha φ), sf ∈ sfs → ψ ∉ sf, from
    begin
      intros sf hsf,
      apply hsfs,
      simp [hsf],
    end,
    specialize ih hsfs',
    refine and_right_imp.mpr _,
    apply or_cases,
    { have hχ := s_f_closed (hsfs sf (by simp)) hψ,
      cases hχ with χ hχ,
      apply cut,
      apply iff_l,
      apply phi_s_f_conj_contains sf hχ.left,
      apply imp_and_l,
      apply cut,
      apply iff_l,
      apply hχ.2,
      exact iden, },
    { refine and_right_imp.mp _,
      apply ih, }, },
end

lemma phi_X_contains_iff_psi_helper_list {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  {φ ψ : formCLC agents} (hψ : ψ ∈ cl φ)  (sfs tfs : list (S_f φ))
  (hsfs : ∀ sf : (@S_f agents _ ha φ), sf ∈ sfs → ψ ∈ sf)
  (htfs : ∀ tf : (@S_f agents _ ha φ), tf ∈ tfs → ψ ∉ tf)
  (hSf : axCLC (¬' (finite_disjunction (phi_X_list φ tfs))→'finite_disjunction (phi_X_list φ sfs))) :
  -- (hSf : axCLC (finite_disjunction (phi_X_list φ tfs ++ phi_X_list φ sfs))) :
  -- (hempty : (sfs = list.nil → axCLC (⊥' <~> ψ)) ∨ (sfs ≠ list.nil)) :
  axCLC ((finite_disjunction (phi_X_list φ sfs)) <~> ψ) :=
begin
  -- ↔ ∨ {sf |ψ∈sf }(ψ ∧ φsf), by propositional logic.
  apply @iff_cut (formCLC agents),
  exact (phi_X_list_conj_contains hsfs),
  -- ↔ ⊥ ∨ (∨{sf |ψ∈sf }(ψ ∧ φsf)), by propositional logic.
  apply iff_cut,
  exact iff_switch_ax.mp (ax_not_bot_imp_iff _),
  -- ↔ (∨ {tf |¬ψ∈tf }(ψ ∧ φtf)) ∨ (∨ {sf |ψ∈sf }(ψ ∧ φsf)), by propositional logic.
  apply iff_cut,
  apply or_cut_l,
  apply contra_fin_disjunct_psi_and_not hψ tfs htfs,
   -- ↔ ψ ∧ ((∨ {tf |¬ψ∈tf } φtf ) ∨ (∨ {sf |ψ∈sf } φsf )), by propositional logic.
  apply @iff_cut _ _ _ _
    (ψ & (¬' (finite_disjunction (phi_X_list φ tfs)) →' finite_disjunction (phi_X_list φ sfs))),
  apply distr_or_and,
  -- ↔ ψ ∧ (∨ {sf ∈Sf } φsf ), because {tf | ¬ψ ∈ tf } ∪ {sf | ψ ∈ sf } = Sf .
  -- ↔ ψ ∧ ⊤, from Lemma 4.
  -- ↔ ψ, by propositional logic.
  apply ax_iff_intro,
  exact p5 _ _,
  apply cut,
  apply MP',
  exact hSf,
  exact p4 _ _,
  apply iff_l,
  exact and_switch,
end

lemma phi_X_contains_iff_psi_helper_finset {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  {φ ψ : formCLC agents} (hψ : ψ ∈ cl φ)  (sfs: finset (S_f φ)) 
  (hsfs : ∀ sf : (@S_f agents _ ha φ), sf ∈ sfs → ψ ∈ sf)
  (htfs : ∀ tf : (@S_f agents _ ha φ), tf ∉ sfs → ψ ∉ tf)
  (hSf : axCLC ((¬ phi_X_finset φ sfsᶜ) ~> phi_X_finset φ sfs)) :
  axCLC ( (phi_X_finset φ sfs) <~> ψ) :=
begin
  unfold phi_X_finset,
  apply phi_X_contains_iff_psi_helper_list hψ _ sfsᶜ.to_list,
  simp [finset.to_list], exact hsfs,
  simp [finset.to_list], exact htfs,
  exact hSf,
end

-- Lemma 6. ∀ ψ ∈ cl(φ), φ{sf |ψ∈sf } ↔ ψ
lemma phi_X_contains_iff_psi {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  (φ ψ : formCLC agents) (hψ : ψ ∈ cl φ) :
  axCLC (phi_X_set φ {sf | ψ ∈ sf} <~> ψ) :=
begin
  apply phi_X_contains_iff_psi_helper_finset hψ, simp, simp,
  apply (phi_X_finset_disjunct_of_disjuncts φ _ _).mpr,
  apply @MP' (formCLC agents),
  exact univ_disjunct_provability φ (canonical.nonempty_S_f φ),
  apply phi_X_subset_Y_imp,
  intros sf hsf,
  simp [to_finset] at *,
  rw or.comm,
  exact (em (ψ ∈ sf)),
end

lemma imp_ax_imp {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  {φ ψ : formCLC agents} (h : ∀ (a : (canonical_model_CLC agents).f.to_frameCL.states), φ ∈ a → ψ ∈ a) :
  axCLC (φ ~> ψ) :=
begin
  apply @ax_imp_from_ex (formCLC agents),
  apply h,
end

-- Lemma 7.  ̃ψ ∈ E(s)(G) iff [G]ψ ∈ s
lemma E_s_contains_tilde_iff_E_in_s {agents : Type} [hN : fintype agents] [ha : nonempty agents]
  (φ ψ : formCLC agents) (s : (canonical_model_CLC agents).f.states) (G : set agents) :
  ((tilde ψ) ∈ ((canonical_model_CLC agents).f.E.E s G)) ↔ (([G] ψ) ∈ s) :=
begin
  let hE : (canonical_model_CLC agents).f.to_frameCL.E.E = λ s G, {X | ite (G = univ) 
          -- condition G = N
          (∀ φ, ({t | φ ∈ t} ⊆ Xᶜ) → ([∅]' φ) ∉ s.val)
          -- condition G ≠ N
          (∃ φ, {t | φ ∈ t} ⊆ X ∧ ([G]' φ) ∈ s.val)},
        from rfl,
  let hs : (canonical_model_CLC agents).f.to_frameCL.states = {Γ : (set (formCLC agents)) // (max_ax_consistent Γ)}, 
    from rfl,
  -- Proof. We consider the case when G ̸ = N and G = N separately.
  cases (em (G = univ)) with hG hG,
  { -- 2. case G = N
    rw hG,
    split,
    { -- 2.1. ⇒
      -- 2.1.1. Assume  ̃ψ ∈ E(s)(N ).
      intro h,
      -- 2.1.2. ∀ ̃χ ⊆  ̃ψᶜ : [∅]χ /∈ s, from 2.1.1, by definition E.
      simp [hE] at h {eta := ff}, clear hE,
      -- 2.1.3. ∀ ̃χ ⊆  ̃¬ψ : [∅]χ /∈ s, from 2.1.2, because  ̃ψᶜ =  ̃¬ψ.
      have h_subeq : {t : (canonical_model_CLC agents).f.to_frameCL.states | (¬ ψ) ∈ t} ⊆ (tilde ψ)ᶜ, from
      begin
        intros t ht hf,
        simp[tilde] at *,
        exact contra_containts_pr_false t.2 hf ht,
      end,
      -- 2.1.4. [N ]ψ ∈ s, from 2.1.3, by axiom N.
      specialize h (¬ ψ) h_subeq,
      have hin := not_in_from_notin s.2 h,
      apply max_ax_contains_by_set_proof s.2 hin axCLC.N, },
    { -- 2.2. ⇐
      -- 2.2.1. Assume [N ]ψ ∈ s.
      intro h,
      -- 2.2.2. ¬[∅]¬ψ ∈ s, from 2.2.1
      have hin : (¬ ([∅] (¬ ψ))) ∈ s, from
      begin
        apply max_ax_contains_by_set_proof s.2 h,
        exact iff_l (@univ_iff_empty agents (formCLC agents) _ _ _ ψ),
      end,
      -- 2.2.3. ¬∃χ,  ̃χ ⊆  ̃¬ψ : [∅]χ ∈ s, from proof by contradiction, 
        -- else by definition E we would have [∅]¬ψ ∈ s, which contradicts with 2.2.2.
      have hne : ¬ ∃ (χ : formCLC agents), (tilde χ) ⊆ (tilde ¬ ψ) ∧ ([∅]' χ) ∈ s, from 
      begin
        intro hf,
        cases hf with χ hf,
        cases hf with himp hf,
        simp [tilde] at himp,
        have hax : axCLC (χ ~>(¬ ψ)), from imp_ax_imp himp,
        have hf : ([∅]' (¬' ψ)) ∈ s, from
        begin
          apply max_ax_contains_by_set_proof s.2 hf,
          apply @derived_monoticity_rule agents (formCLC agents),
          exact hax,
        end,
        apply contra_containts_pr_false s.2 hf hin,
      end,
      -- 2.2.4. ∀χ,  ̃χ ⊆  ̃¬ψ : [∅]χ /∈ s, from 2.2.3, by first order logic.
      simp at hne,
      -- 2.2.5. ∀χ,  ̃χ ⊆  ̃ψ : [∅]χ /∈ s, because all s ∈ S are maximally consistent.
      rw h_tilde_compl at hne,
      -- 2.2.6.  ̃ψ ∈ E(s)(N ), from 2.2.5, by definition E.
      simp [hE] {eta := ff},
      exact hne, }, },
  { -- 1. case G ̸ = N
    split,
    { -- 1.1. ⇒
      -- 1.1.1. Assume  ̃ψ ∈ E(s)(G).
      intro h,
      -- 1.1.2. ∃ ̃χ ⊆  ̃ψ : [G]χ ∈ s, from 1.1.1, by definition E.
      simp [hE, hG] at h {eta := ff},
      -- 1.1.3. ⊢ χ → ψ, from 1.1.2.
      cases h with χ h,
      cases h with himp h,
      simp [tilde] at himp,
      have hax : axCLC (χ ~> ψ), from imp_ax_imp himp,
      -- 1.1.4. [G]ψ ∈ s, from 1.1.2 & 1.1.3, by lemma 2.
      apply max_ax_contains_by_set_proof s.2 h,
      apply @derived_monoticity_rule agents (formCLC agents),
      exact hax, },
    { -- 1.2. ⇐ is immediate by definition.
      simp [hE, hG],
      intro h,
      apply exists.intro ψ,
      split,
      simp [tilde],
      exact h, }, },
end

end lemmas

-- Effectivity
----------------------------------------------------------
def E_f {agents : Type}  [hN : fintype agents] [ha : nonempty agents] {φ : formCLC agents} : 
  (S_f φ) → (set agents) → (set (set (S_f φ))) := 
λ sf G, {X | ite (G = univ) 
  -- condition G = N
  -- ∃t ∈ S, sf = tf and  ̃φX ∈ E(t)(N)
  (∃ t : (canonical_model_CLC agents).f.states, (∀ {x}, x ∈ sf ↔ x ∈ t ∧ x ∈ cl φ) ∧ 
    (tilde (phi_X_set φ X)) ∈ (canonical_model_CLC agents).f.E.E (t) (G))
  -- condition G ≠ N
  -- ∀t ∈ S, sf = tf ⇒  ̃phiX ∈ E(t)(G)
  (∀ t : (canonical_model_CLC agents).f.states, (∀ {x}, x ∈ sf ↔ x ∈ t ∧ x ∈ cl φ) → 
    (tilde (phi_X_set φ X)) ∈ (canonical_model_CLC agents).f.E.E (t) (G))}

----------------------------------------------------------
-- Playability
----------------------------------------------------------

-- 1. Ef (sf ) is live: ∀G ⊆ N : ∅ /∈ Ef (sf )(G)
lemma Ef_liveness {agents : Type} [hN : fintype agents] [ha : nonempty agents] (φ : formCLC agents) :
  ∀ s : (S_f φ), ∀ G : set agents, ∅ ∉ (E_f s G) := 
begin
  -- 1.2. Assume by contradiction ∅ ∈ Ef (sf )(G).
  intros sf G hf,
  unfold E_f at hf,
  split_ifs at hf with h h,
  -- 1.4. Case: G = N
  { -- 1.4.1. ∃t ∈ S, sf = tf and  ̃φ∅ ∈ E(t)(N), from 1.2, by definition Ef .
    simp[h] at hf,
    -- 1.4.2. ∃t ∈ S, sf = tf and ∅ ∈ E(t)(N), from 1.4.1 & 1.1.
    cases hf with t hf,
    -- 1.4.3. ∀t, ∅ ∉ E(t)(N) because E(t) is live.
    have hlive := (canonical_model_CLC agents).f.E.liveness t univ,
    -- 1.4.4. Contradiction from 1.4.2 & 1.4.3.
    exact hlive hf.right, },
  -- 1.3. Case: G ≠ N
  { -- 1.3.1. ∀t ∈ S, sf = tf ⇒  ̃φ∅ ∈ E(t)(G), from 1.2, by definition Ef
    -- 1.3.2. ∀t ∈ S, sf = tf ⇒ ∅ ∈ E(t)(G), from 1.3.1 & 1.1
    simp[E_f, h] at hf,
    -- 1.3.3. ∅ ∈ E(s)(G), from 1.3.2
    cases (s_f_to_s φ sf) with s hs,
    specialize hf s @hs,
    -- 1.3.4. ∅ /∈ E(s)(G) because E(s) is live.
    have hlive := (canonical_model_CLC agents).f.E.liveness s,
    -- 1.3.5. Contradiction from 1.3.3 & 1.3.4.
    exact hlive G hf, },
end

-- 2. Ef (sf) is safe: ∀G ⊆ N : Sf ∈ Ef (sf )(G)
lemma Ef_safety {agents : Type} [hN : fintype agents] [ha : nonempty agents] (φ : formCLC agents) :
  ∀ (s : S_f φ) (G : set agents), univ ∈ E_f s G :=
begin
  -- 2.2. Additionally, because E(s) is safe for all s ∈ S, ∀G ⊆ N, S ∈ E(s)(G).
  have hsafe := (canonical_model_CLC agents).f.E.safety,
  -- 2.4. Case: G = N
  intros sf G, cases em (G = univ) with hG hG,
  { -- 2.4.1. Sf ∈ Ef (sf )(N ) iff ∃t ∈ S, sf = tf and  ̃φSf ∈ E(t)(N ), by definition Ef .
    simp[hG] at *,
    -- 2.4.2. Sf ∈ Ef (sf )(N ) iff ∃t ∈ S, sf = tf and S ∈ E(t)(N ), from 2.1 & 2.4.1.
    simp[E_f],
    -- 2.4.3. ∃t ∈ S, sf = tf and S ∈ E(t)(N ), when t = s, because sf = sf and S ∈ E(s)(N ), from 2.2.
    cases (s_f_to_s φ sf) with s hs,
    apply exists.intro s,
    -- 2.4.4. Sf ∈ Ef (sf )(N ), from 2.4.2 & 2.4.3s
    simp at *,
    split,
    exact @hs,
    apply hsafe, },
  -- 2.3. Case: G ≠ N
  { -- 2.3.1. Sf ∈ Ef (sf )(G) iff ∀t ∈ S, sf = tf ⇒  ̃φSf ∈ E(t)(G), by definition Ef .
    -- 2.3.2. Sf ∈ Ef (sf )(G) iff ∀t ∈ S, sf = tf ⇒ S ∈ E(t)(G), from 2.1 & 2.3.1.
    simp[E_f, hG] at *,
    -- 2.3.3. Sf ∈ Ef (sf )(G), from 2.2 & 2.3.2
    intros t ht,
    apply hsafe, }, 
end

-- 3. Ef (sf) is N-maximal: ∀X ⊆ Sf : Xᶜ ∉ Ef(sf)(∅) ⇒ X ∈ Ef(sf)(N)
lemma Ef_nmax {agents : Type} [hN : fintype agents] [ha : nonempty agents] (φ : formCLC agents) :
  N_max agents (S_f φ) (E_f) :=
begin
  -- 3.1. Assume some X ⊆ Sf such that Xᶜ ∉ Ef(sf)(∅).
  intros sf X hXc,
  -- 3.2. ¬(Xᶜ ∈ Ef sf ∅), from 3.1.
  -- 3.3. ¬(∀t ∈ S, sf = tf ⇒ ~φXᶜ ∈ E(t)(∅)), from 3.2, by definition Ef . 
  -- 3.4. ∃t ∈ S, sf = tf and ~φXᶜ ∉ E(t)(∅)), from 3.3, by first order logic. 
  simp[E_f, empty_ne_univ] at *,
  obtain ⟨t, ht, hXc⟩ := hXc,
  refine ⟨t, @ht, _⟩,
  { 
    have h_tilde: tilde (¬ (phi_X_set φ X) : formCLC agents) = 
      tilde (phi_X_set φ Xᶜ), from
    begin
      simp[tilde],
      ext1 u,
      split,
      { intro hu,
        simp at *,
        apply max_ax_contains_by_set_proof u.2 hu,
        apply (phi_X_set_disjunct_of_disjuncts φ _ _).mpr,
        rw (union_compl_self X),
        apply univ_disjunct_provability,
        exact canonical.nonempty_S_f φ, },
      { intro hu,
        simp at *,
        apply max_ax_contains_by_set_proof u.2 hu,
        unfold phi_X_set,
        apply phi_X_set_unique,
        simp, },
    end,

    -- 3.6. ∃t ∈ S, sf = tf and ~¬φX ∉ E(t)(∅)), from 3.4 & 3.5
    have hX : tilde (¬ (phi_X_set φ X) : formCLC agents) ∉ 
      (canonical_model_CLC agents).f.to_frameCL.E.E t ∅, from
    begin
      simp[h_tilde] at *,
      exact hXc,
    end,  
    -- 3.7. ∃t ∈ S,sf = tf and (~φX)ᶜ ∉ E(t)(∅)), from 3.6, because all s ∈ S are maximally consistent.
  simp at *,
  simp[h_tilde_compl] at hX,
    -- 3.8. ∃t ∈ S,sf = tf and φ􏰓 ∈ E(t)(N)), from 3.7, because E(s) is N-maximal X for all s ∈ S (∀X ⊆ S|X ∈/ E(s)(∅) ⇒ X ∈ E(s)(N))
    -- 3.9. Ef (sf )(N), from 3.8, by definition Ef .
  exact (canonical_model_CLC agents).f.to_frameCL.E.N_max t (tilde (phi_X_set φ X)) hX, },
end

-- Ef (sf ) is outcome monotonic: ∀G ⊆ N, ∀X ⊆ Y ⊆ Sf : X ∈ Ef (sf )(G) ⇒ Y ∈ Ef (sf )(G)
lemma Ef_monoticity {agents : Type} [hN : fintype agents] [ha : nonempty agents] (φ : formCLC agents) :
  ∀ (sf : S_f φ) (G : set agents) (X Y : set (S_f φ)), X ⊆ Y → X ∈ E_f sf G → Y ∈ E_f sf G :=
begin
  -- 4.1. Let G be some G ⊆ N and X and Y be some X ⊆ Y ⊆ Sf .
  intros s G X Y hXY,
  -- 4.2. Assume X ∈ Ef (sf )(G).
  intro hX,
  -- 4.3. First we note that ∀s ∈ S, ∀G ⊆ N,  ̃φX ∈ E(s)(G) ⇒  ̃φY ∈ E(s)(G)
  have himp : ∀ s G, 
    (tilde (phi_X_set φ X)) ∈ (canonical_model_CLC agents).f.E.E s G → 
    (tilde (phi_X_set φ Y)) ∈ (canonical_model_CLC agents).f.E.E s G, from
  begin
    -- 4.3.1. Let s be some s ∈ S and G be some G ⊆ N .
    clear hX, intros s G hX,
    -- 4.3.2. ⊢ φX → φY , from 4.1 (X ⊆ Y ).
    have hax : axCLC ((phi_X_set φ X) ~> (phi_X_set φ Y)), 
      from phi_X_set_subset_Y_imp _ _ _ hXY,
    -- 4.3.3.  ̃φX ⊆  ̃φY , from 4.3.2.
    have h_phiXY : (tilde (phi_X_set φ X)) ⊆ (tilde (phi_X_set φ Y)), from
    begin 
      rw set.subset_def,
      intros t ht,
      apply max_ax_contains_by_set_proof t.2 ht hax,
    end,
    -- 4.3.4. E(s) is outcome monotonic for all s ∈ S: ∀G ⊆ N, ∀X ⊆ Y ⊆ S, X ∈ E(s)(G) ⇒ Y ∈ E(s)(G)
    have hmonoticity := (canonical_model_CLC agents).f.E.monoticity s G _ _ h_phiXY,
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
    exact himp t G (hX t @ht), },
end

lemma phi_X_list_inter {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : list (S_f φ)) (hX : list.nodup X) (hY : list.nodup Y) :
  axCLC (finite_disjunction (phi_X_list φ X)→' finite_disjunction (phi_X_list φ Y) →' 
        finite_disjunction (phi_X_list φ (X ∩ Y))) :=
begin
  induction' X with x X ihx,
  { simp [phi_X_list, finite_disjunction],
    apply axCLC.Prop1, },
  { simp [phi_X_list, finite_disjunction],
    apply @or_cases (formCLC agents),
    { cases (em (x ∈ Y)),
      { apply cut,
        apply iff_l,
        apply phi_X_list_single,
        apply @cut _ _ _ _ (finite_disjunction (phi_X_list φ ((x :: X) ∩ Y))),
        apply imp_finite_disjunction_subset,
        apply phi_X_list_subset,
        simp,
        exact h,
        exact axCLC.Prop1, },
      { apply cut,
        apply iff_l,
        apply phi_X_list_single,
        apply cut1,
        apply phi_X_list_unique,
        exact list.singleton_disjoint.mpr h,
        exact list.nodup_singleton x,
        exact hY,
        exact explosion, }, },
    { simp at hX,
      specialize ihx Y hY hX.2,
      apply cut1,
      apply ihx,
      apply imp_finite_disjunction_subset,
      apply phi_X_list_subset,
      intros y hy,
      simp at *,
      split,
      apply or.intro_right,
      exact hy.1,
      exact hy.2, }, },
end

lemma phi_X_finset_inter {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : finset (S_f φ)) :
  axCLC ((phi_X_finset φ X) →' phi_X_finset φ Y →' (phi_X_finset φ (X ∩ Y))) :=
begin
  unfold phi_X_finset,
  apply @cut1 (formCLC agents),
  apply phi_X_list_inter,
  repeat {exact finset.nodup_to_list _, },
  apply imp_finite_disjunction_subset,
  apply phi_X_list_subset,
  intros x hx,
  simp [finset.mem_to_list] at *,
  exact hx,
end

lemma phi_X_set_inter {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) (X Y : set (S_f φ)) :
  axCLC ((phi_X_set φ X) →' (phi_X_set φ Y) →' (phi_X_set φ (X ∩ Y))) :=
begin
  simp[phi_X_set],
  apply @cut1 (formCLC agents),
  apply phi_X_finset_inter,
  apply phi_X_subset_Y_imp,
  intros x hx,
  simp at *,
  exact hx, 
end
--  Ef (sf ) is superadditive ∀G, F ⊆ N (where G ∩ F = ∅), 
  -- ∀X, Y ⊆ Sf : X ∈ Ef (sf )(G) and Y ∈ Ef (sf )(F ) ⇒ X ∩ Y ∈ Ef (sf )(G ∪ F )
lemma Ef_superadd {agents : Type} [hN : fintype agents] [ha : nonempty agents] (φ : formCLC agents) :
  ∀ (sf : S_f φ) (G F : set agents) (X Y : set (S_f φ)),
  X ∈ E_f sf G → Y ∈ E_f sf F → G ∩ F = ∅ → X ∩ Y ∈ E_f sf (G ∪ F) :=
begin      
  -- 5.1. Let G, F be some G, F ⊆ N , such that G ∩ F = ∅. Let X, Y be some
    -- X, Y ⊆ S such that X ∈ Ef (sf )(G) and Y ∈ Ef (sf )(F ).
  -- intros sf G F X Y hX hY hGF,
  -- 5.2. First we note that ∀s ∈ S, ∀G, F ⊆ N (where G ∩ F = ∅),  ̃φX ∈ E(s)(G) ⇒  ̃φY ∈ E(s)(F ) ⇒  ̃φX∩Y ∈ E(s)(G ∪ F )
  have hint : ∀ s G F X Y, G ∩ F = ∅ → 
    (tilde (phi_X_set φ X)) ∈ (canonical_model_CLC agents).f.E.E s G →
    (tilde (phi_X_set φ Y)) ∈ (canonical_model_CLC agents).f.E.E s F →
    (tilde (phi_X_set φ (X ∩ Y))) ∈ (canonical_model_CLC agents).f.E.E s (G ∪ F), from
  begin
    -- 5.2.1. Let s be some s ∈ S. Let G, F , be some G, F ⊂ N where G ∩ F = ∅. Assume  ̃φX ∈ E(s)(G) and  ̃φY ∈ E(s)(F ).
    intros s G F X Y hGF hG hF,
    -- 5.2.2. E(s) is superadditive so: ∀X, Y ⊆ S : X ∈ E(s)(G) and Y ∈ E(s)(F ) ⇒ X ∩ Y ∈ E(s)(G ∪ F )
    have hsuperadd := ((canonical_model_CLC agents).f.E.superadd) s G F,
    -- 5.2.3.  ̃φX ∩  ̃φY ∈ E(s)(G ∪ F ), from 5.2.1 & 5.2.2.
    specialize hsuperadd (tilde (phi_X_set φ X)) (tilde (phi_X_set φ Y)) hG hF hGF,
    -- 5.2.4.  ̃φX∩Y ∈ E(s)(G ∪ F ), from 5.2.3, because  ̃φX →  ̃φX∩Y and  ̃φY →  ̃φX∩Y .
    have h_tilde_eq : tilde (phi_X_set φ X) ∩ tilde (phi_X_set φ Y) = tilde (phi_X_set φ (X ∩ Y)), from
    begin
      ext1 s,
      simp[tilde],
      split,
      { intro h,
        apply max_ax_contains_by_set_proof_2h s.2 h.1 h.2 ,
        apply phi_X_set_inter, },
      { intro h,
        split,
        repeat 
        { apply max_ax_contains_by_set_proof s.2 h,
          apply phi_X_set_subset_Y_imp,
          simp, }, },
    end,
    
    rw h_tilde_eq at hsuperadd,
    exact hsuperadd,
  end,
  
  intros sf G F X Y hX hY hGF,

  -- 5.4. Case G = N or F = N :
  have h_G_or_F_univ : ∀ X' Y', X' ∈ E_f sf univ → Y' ∈ E_f sf ∅ → (X' ∩ Y') ∈ E_f sf univ, from
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
      { have hs := s_f_to_s φ sf,
        cases hs with s hs,
        specialize hint s G F X Y hGF (hX s @hs) (hY s @hs),
        simp[h_2] at *,
        apply exists.intro s,
        split, exact @hs, exact hint, },
      -- 5.3.5. Case G ∪ F ̸ = N : X ∩ Y ∈ Ef (sf )(G ∪ F ), from 5.3.4, by definition Ef
      { simp[h_2],
        intros t ht,
        exact hint t G F X Y hGF (hX t @ht) (hY t @ht), }, }, },
end

----------------------------------------------------------
-- Building the coplete filtered CLC model
----------------------------------------------------------
 
@[simps?] def filtered_model_CLC {agents : Type} [hN : fintype agents] [ha : nonempty agents] 
  (φ : formCLC agents) :
  modelCLK agents := 
{ f := 
  { states := S_f φ,
    hs := canonical.nonempty_S_f φ,
    ha := ha,
    E := 
    
-- ∀u∈Sc if [u]=[s] then [φ ]c ∈Ec(u)(G) G̸=N
    { E          := E_f,
      liveness   := Ef_liveness φ,
      safety     := Ef_safety φ,
      N_max      := Ef_nmax φ,
      monoticity := Ef_monoticity φ,
      superadd   := Ef_superadd φ, },
    rel   := λ i s, {t | {φ | K' (i) (φ) ∈ s} = {φ | K' (i) (φ) ∈ t}},
    rfl   := by simp,
    sym   := λ i s t ht, eq.symm ht,
    trans := λ i s t u hst htu, (rfl.congr htu).mp hst, },
  v := λ  n, {s | (formCLC.var n) ∈ s.1.1}, }

end canonical
