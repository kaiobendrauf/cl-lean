/-
Authors : Kai Obendrauf
Following the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley

This file contains the proof that CLK is complete.
Given completeness we also prove that CLK does not prove ⊥, 
  by coming up with a simple instance of a coalition model. 
-/

import tactic.induction
import semantics.semanticsCLK
local attribute [instance] classical.prop_decidable

open set

----------------------------------------------------------
-- Soundness
----------------------------------------------------------

---------------------- Soundness ----------------------

theorem soundnessCLK {agents: Type} (φ : formCLK agents) : 
  '⊢ φ → '⊨ φ :=
begin
  intro h,
  induction' h,

  -- Prop 1
  { intros m s h1 h2, 
    exact h1, },

  -- Prop 2
  { intros m s h1 h2 h3, 
    apply h1, 
      { exact h3,},

      { apply h2, 
        exact h3 }, },

  -- Prop 3
  { intros m s h1 h2,
    by_contradiction hf,
    exact (h1 hf) (h2 hf), },

  -- Prop 4
  { intros m s h1 h2, 
    exact and.intro h1 h2, },

  -- Prop 5
  { intros m s h1, 
    exact h1.left, },

  -- Prop 6
  { intros m s h1, 
    exact h1.right, },

  -- Prop 7
  { intros m s h1 h2,
    by_contradiction hf,
    exact h1 hf h2, },

  -- Bot
  { intros m s h1, 
    exact m.f.E.liveness s G h1, },

  -- Top
  { intros m s,
    simp [s_entails_CLK],
    exact m.f.E.safety s G, },

  -- N
  { intros m s h1,
    apply m.f.E.N_max,
    by_contradiction,
    exact h1 h, },

  -- M
  { intros m s,
    apply m.f.E.mono s G {t : m.f.states | m; t '⊨ (φ '∧ φ_1)}
      {t : m.f.states | m; t '⊨ φ},
    intros t h1,
    unfold s_entails_CLK at h1,
    exact h1.left, },

  -- S
  { intros m s h1,
    exact m.f.E.superadd s G F {t : m.f.states | m; t '⊨ φ} 
      {t : m.f.states | m; t '⊨ φ_1} h1.left h1.right hInt, },

  -- MP
  { intros m s,
    apply ih_h,
    exact ih_h_1 m s, },

  -- Eq
  { intros m s,
    have heq: {t : m.f.states | m; t '⊨ φ} = {t : m.f.states | m; t '⊨ φ_1},
    { apply set.ext,
      intros u,
      cases (ih m u),
      apply iff.intro,
      { intro hu,
        exact left hu, },
      { intro hu,
        exact right hu } },
    apply and.intro,
    { intro h1,
      simp only [s_entails_CLK, ←heq] at *,
      exact h1, },
    { intro h1,
      simp only [s_entails_CLK, heq] at *,
      exact h1, }, },

  -- K
  { intros m s h1 h2 t ht,
    exact h1 t ht (h2 t ht), },

  -- T
  { intros m s h,
    exact h s (m.f.rfl i s), },

  -- Four
  { intros m s h t ht u hu,
    exact h u (m.f.trans i s t u ht hu), },

  -- Five
  { intros m s h1 t ht ht1,
    apply h1,
    intros u hu,
    apply ht1,
    exact m.f.trans _ _ _ _ (m.f.sym _ _ _ ht) hu, },

  -- RN
  { intros m s t hst,
    apply ih, }, 
end

----------------------------------------------------------
-- CL does not prove ⊥
----------------------------------------------------------
-- create an example Model
inductive single : Type
  | one: single

lemma univ_single : (set.univ: set single) = {single.one} := 
begin
  rw eq_comm,
  rw set.eq_univ_iff_forall,
  intro x,
  cases x,
  simp,
end

instance single_nonempty : nonempty single := 
begin
  apply exists_true_iff_nonempty.mp,
  apply exists.intro single.one,
  exact trivial,
end

instance single_finite : fintype single := 
begin
  refine {elems := {single.one}, complete := _},
  intro x,
  cases x,
  exact finset.mem_singleton.mpr rfl,
end

def m_ex {agents : Type} : modelECL agents  :=
{ f := 
  { states := single,
    hs := single_nonempty,
    E  :=  truly_playable_from_finite
    { E := λ s G, {{single.one}},
      liveness := 
      begin 
        intros _ _ hf, 
        simp at hf, 
        rw set.ext_iff at hf, 
        simp at hf,
        apply hf single.one,
        refl, 
      end,
      safety:=
        begin
          intros _ _, simp at *,
          exact univ_single,
        end,
      N_max :=
        begin
          intros _ _ hxc, simp at *,
          rw ←univ_single at *,
          have hcond : {single.one} ≠ (∅: set single), 

            { intro hf,
              rw set.ext_iff at hf, 
              simp at *,
              apply hf single.one,
              refl, },
          simp [hcond] at *, by_contradiction,
          have hex: ∃ x, x ∈ X, from nonempty_def.mp (ne_empty_iff_nonempty.mp hxc),
          cases hex with s hs,
          cases s,
          rw ←singleton_subset_iff at hs,
          rw ←univ_single at hs,
          exact h (univ_subset_iff.mp hs),
        end,
      mono :=
        begin
          intros _ _ _ _ hxy hx,
          simp [←univ_single] at *,
          rw hx at hxy,
          exact univ_subset_iff.mp hxy,
        end,
      superadd :=
      begin
        intros _ _ _ _ _ hX hY hGF,
        simp at *,
        simp[hX, hY],
      end },
    rel := λ a s, {s},
    rfl := by simp,
    sym :=
    begin
      intros i s t h,
      simp at *,
      rw h,
    end,
    trans :=
    begin
      intros i s t u hst htu,
      simp at *,
      simp[hst, htu],
    end, },
  v := λ _, {}, }

lemma nprfalseCLK {agents : Type} :
  ¬ (axCLK (formCLK.bot : formCLK agents )) :=
begin
  apply (mt (soundnessCLK (@formCLK.bot agents))),
  intro hf ,
  simp[global_valid, valid_m, s_entails_CLK] at hf,
  apply hf (m_ex),
  exact single.one,
end
