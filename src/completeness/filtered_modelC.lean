import completeness.filteringC


local attribute [instance] classical.prop_decidable

open set formCLC

namespace canonical

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
