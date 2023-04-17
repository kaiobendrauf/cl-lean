import completeness.completenessCLC

local attribute [instance] classical.prop_decidable

open set formCLC

noncomputable  def model_checking_CLC_C' {agents : Type} [hN : fintype agents] 
  (m : modelECL agents) [hf : fintype m.f.states] 
  (G : set agents) : ℕ → finset (m.f.states) → finset (m.f.states) 
| 0       := λ _, ∅
| (n + 1) := λ Γ,
begin
  have Γ' : finset (m.f.states), 
    from finset.filter (λ s, ∀ i t, i ∈ G → (t ∈ (m.f.rel i s)) → t ∈ Γ) Γ,
    -- have hdec := finset.card_filter_le Γ (λ s, ∀ i t, i ∈ G → (t ∈ (m.f.rel i s))),
    -- have := lt_or_eq_of_le hdec,
  apply ite (finset.card Γ' = finset.card Γ) Γ (model_checking_CLC_C' (min n (finset.card Γ')) Γ'),
end 
-- using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf finset.card⟩]}

-- noncomputable  def model_checking_CLC_C' {agents : Type} [hN : fintype agents] 
--   (m : modelECL agents) [hf : fintype m.f.states] 
--   (G : set agents) : ℕ → finset (m.f.states) → finset (m.f.states) 
-- | 0       := λ _, ∅
-- | (n + 1) := λ Γ,
-- begin
--   have Γ' : finset (m.f.states), 
--     from finset.filter (λ s, ∀ i t, i ∈ G → (t ∈ (m.f.rel i s)) → t ∈ Γ) Γ,
--     -- have hdec := finset.card_filter_le Γ (λ s, ∀ i t, i ∈ G → (t ∈ (m.f.rel i s))),
--     -- have := lt_or_eq_of_le hdec,
--   apply ite (finset.card Γ' = finset.card Γ) Γ (model_checking_CLC_C' (n) Γ'),
-- end 
-- -- using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf finset.card⟩]}

def model_checking_CLC_C {agents : Type} [hN : fintype agents] 
  (m : modelECL agents) [hf : fintype m.f.states] 
  (G : set agents) (Γ : set (m.f.states)) : set (m.f.states) :=
begin
  have Γ' : finset (m.f.states), 
     from finite.to_finset (finite.of_fintype Γ),
  exact {s | s ∈ (model_checking_CLC_C' m G (finset.card Γ') Γ')},
end

def model_checking_CLC {agents : Type} [hN : fintype agents] 
  (m : modelECL agents) [hf : fintype m.f.states] : 
  formCLC agents → set (m.f.states)
  | bot        := ∅ 
  | (var n)    := {s | m ; s '⊨ var n}
  | (imp φ ψ)  := (model_checking_CLC φ)ᶜ ∪ (model_checking_CLC ψ)
  | (and φ ψ)  := (model_checking_CLC φ)  ∩ (model_checking_CLC ψ)
  | ('[G] φ)   := {s | (model_checking_CLC φ) ∈ m.f.E.E (s) (G)}
  | ('K i φ)   := {s | ∀ t ∈ (m.f.rel i s), t ∈ (model_checking_CLC φ)}
  | ('C G φ)   := ite (G = ∅) (univ) (model_checking_CLC_C m G (model_checking_CLC φ))

lemma model_checking_CLC_iff_C_base {agents : Type} [hN : fintype agents] 
  (m : modelECL agents) [hf : fintype m.f.states] (φ : formCLC agents) {G : set agents}
  {i : agents} (hi : i ∈ G) (s : m.f.states)
  (h : (finset.card (finite.to_finset (finite.of_fintype (model_checking_CLC m φ)))) = 0)
  (ih : ∀ (s : m.f.states), s ∈ model_checking_CLC m φ ↔ (m ; s '⊨ φ)) :
  s ∈ model_checking_CLC_C m G (model_checking_CLC m φ) ↔ (m ; s '⊨ C G φ) :=
begin
  simp only [model_checking_CLC_C, model_checking_CLC_C', s_entails_CLC, h, finset.not_mem_empty, 
              set_of_false, mem_empty_eq, forall_exists_index, and_imp, false_iff, not_forall, 
              exists_prop, exists_and_distrib_right],
  apply exists.intro s,
  fconstructor,
  { apply exists.intro [i],
    split,
    { simp only [list.mem_singleton, forall_eq, hi], },
    { apply exists.intro [],
      simp [C_path],
      apply m.f.rfl, }, },
  { by_contradiction hf,
    have := (ih s).mpr hf,
    simp only [finset.card_eq_zero, finite_to_finset_eq_empty_iff] at h,
    exact eq_empty_iff_forall_not_mem.mp h s this, },
end

lemma model_checking_CLC_iff_C {agents : Type} [hN : fintype agents] 
  (m : modelECL agents) [hf : fintype m.f.states] (φ : formCLC agents) {G : set agents}
  [Γ : set  m.f.states] {i : agents} (hi : i ∈ G) (s : m.f.states) 
  {n : ℕ} (n = (finset.card (finite.to_finset (finite.of_fintype Γ))))
  (h : (finset.card (finite.to_finset (finite.of_fintype Γ))) ≠ 0)
  (ih : ∀ (s : m.f.states), s ∈ model_checking_CLC m φ ↔ (m ; s '⊨ φ)) :
  s ∈ model_checking_CLC_C' m G n (finite.to_finset (finite.of_fintype Γ)) ↔ (m ; s '⊨ C G φ) :=
begin
  induction n with n ihn hn,
  { exact false.rec _ (h (eq.symm H)), },
  { 

  }

end

lemma model_checking_CLC_iff {agents : Type} [hN : fintype agents] 
  (m : modelECL agents) [hf : fintype m.f.states] (φ : formCLC agents) : 
  ∀ s, s ∈ (model_checking_CLC m φ) ↔ (m ; s '⊨ φ) :=
begin
  induction φ with _ φ ψ ihφ ihψ φ ψ ihφ ihψ G φ ih i φ ih G φ ih,
  all_goals { intro s, },
  repeat 
    { simp only [model_checking_CLC, s_entails_CLC, mem_empty_eq, set_of_mem_eq, mem_inter_eq], },
  { simp only [ihφ, ihψ], },
  { simp only [ihφ, ihψ, mem_union_eq, mem_compl_eq, imp_iff_not_or.symm], },
  { simp only [mem_set_of_eq, ←ih, set_of_mem_eq], },
  { simp only [ih, mem_set_of_eq], },
  { split_ifs with hG hG,
    { simp only [hG, mem_univ, mem_empty_eq, forall_exists_index, and_imp, true_iff],
      intros t is his ts hC,
      cases is with i is,
      { simp [C_path] at hC,
        exact false.rec (m;t '⊨φ) hC, },
      { exact false.rec _ (his i (list.mem_cons_self i is)), }, },
    { obtain ⟨i, hi⟩ := nonempty_def.mp (not_not.mp (mt (not_nonempty_iff_eq_empty.mp) hG)), 
      -- simp [model_checking_CLC_C, model_checking_CLC_C'],
      cases (em ((finset.card (finite.to_finset (finite.of_fintype (model_checking_CLC m φ)))) = 0)),
      { have := model_checking_CLC_iff_C_base m φ hi s h ih,
        simp only [model_checking_CLC, s_entails_CLC] at this,
        exact this, },
      { 

      }
      -- induction (finset.card (finite.to_finset (finite.of_fintype (model_checking_CLC m φ)))),
      -- { simp [model_checking_CLC_C, model_checking_CLC_C'],
        

      -- },
      -- { intro h,
        
      -- }

      -- simp [model_checking_CLC_C, model_checking_CLC_C'],
      -- cases (finset.card (finite.to_finset (finite.of_fintype (model_checking_CLC m φ)))),
    --   { simp [model_checking_CLC_C, model_checking_CLC_C'],
    --     simp [←ih],

    --   }

    -- }

  }, },
  -- dsimp[model_checking_CLC, s_entails_CLC],
end