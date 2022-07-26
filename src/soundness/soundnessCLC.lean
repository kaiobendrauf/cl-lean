
import syntax.syntaxCLC 
import syntax.axiomsCLC 
import semantics.semanticsCLC
import tactic.induction
local attribute [instance] classical.prop_decidable

open set list

variable {agents : Type}

---------------------- Soundness ----------------------

theorem soundnessCLC (φ : formCLC agents) : axCLC φ → global_valid φ :=
begin
intro h,
induction' h,

{ intros m s h1 h2, 
  exact h1, },

{ intros m s h1 h2 h3, 
  apply h1, 
    { exact h3,},

    { apply h2, 
      exact h3 }, },

{ intros m s h1 h2,
  by_contradiction hf,
  exact (h1 hf) (h2 hf), },

{ intros m s h1 h2, 
  exact and.intro h1 h2, },

{ intros m s h1, 
  exact h1.left, },

{ intros m s h1, 
  exact h1.right, },

{ intros m s h1 h2,
  by_contradiction hf,
  exact h1 hf h2, },

{ intros m s h1, 
  exact m.f.E.liveness s G h1, },

{ intros m s,
  simp [s_entails_CLC],
  exact m.f.E.safety s G, },

{ intros m s h1,
  apply m.f.E.N_max,
  by_contradiction,
  exact h1 h, },

{ intros m s,
  apply m.f.E.monoticity s G {t: m.f.states | s_entails_CLC m t (φ & φ_1)} {t: m.f.states | s_entails_CLC m t φ},
  intros t h1,
  exact h1.left, },

  { intros m s h1,
    exact m.f.E.superadd s G F {t: m.f.states | s_entails_CLC m t φ} {t: m.f.states | s_entails_CLC m t φ_1} h1.left h1.right hInt, },

  { intros m s,
    apply ih_h,
    exact ih_h_1 m s, },

  { intros m s,
    have heq: {t: m.f.states | s_entails_CLC m t φ} = {t: m.f.states | s_entails_CLC m t φ_1}, from
      begin
        apply set.ext,
        intros u,
        cases (ih m u),
        apply iff.intro,

        { intro hu,
          exact left hu, },

        { intro hu,
          exact right hu, }
      end,
    apply and.intro,

    { intro h1,
      simp[s_entails_CLC, ←heq] at *,
      exact h1, },

    { intro h1,
      simp[s_entails_CLC, heq] at *,
      exact h1, }, },

  { intros m s h1 h2 t ht,
    exact h1 t ht (h2 t ht), },

  { intros m s h,
    exact h s (m.f.rfl i s), },

  { intros m s h t ht u hu,
    exact h u (m.f.trans i s t u ht hu), },

  { intros m s h1 h2,
    exact h1 (h2 s (m.f.rfl i s)), },
  
  { intros m s h,
    induction' G,
    {
      simp [everyone_knows, s_entails_CLC],
    },
    {
      -- simp [s_entails_CLC] at h,
      -- cases h with hl hr,
      split,
      { intros t ht,
        split,
        {
          simp [s_entails_CLC] at h,
          apply h.left t (hd :: G),
          simp,
          -- list agents → list m.f.states →  m.f.states →  m.f.states → Prop
          have hpath: (C_path (hd :: G) (t :: list.nil) s t),
          { simp [C_path],
            apply or.inr,
            split,
            exact ht,
            cases G,
            repeat { simp [C_path], },
          },
          exact hpath,
        },
        {
          simp [s_entails_CLC] at *,
          split,
           { intros u F hF ss hC,
            apply h.left u (hd :: F) 
              begin
                intros i hi,
                cases hi, 
                exact or.inl hi,
                apply hF,
                simpa,
              end
              (t :: ss),
              simp [C_path],
              apply or.intro_right,
              split,
              { exact ht, },
              { exact hC, },
          },
          { intros i hi u F hF ss hC,
            apply h.left u (hd :: F)
            begin
                intros i hi,
                cases hi,
                exact or.inl hi_1,
                apply hF,
                simpa,
              end
              (t :: ss),
              simp [C_path],
              apply or.intro_right,
              split,
              { exact ht, },
              { exact hC, },
          },
        },
      },
      {
        simp [everyone_knows],
      }
    },
    simp [s_entails_CLC] at h,
    

  },

  { intros m s t h,
    apply h_ih, },
end

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

lemma single_nonempty : nonempty single := 
begin
  apply exists_true_iff_nonempty.mp,
  apply exists.intro single.one,
  exact trivial,
end

def m_ex (ha: nonempty agents) : modelCLC agents  :=

{ f := 
  { states := single,
    hs := single_nonempty,
    ha := ha,
    E  :=  
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
      monoticity:=
        begin
          intros _ _ _ _ hxy hx,
          simp [←univ_single] at *,
          rw hx at hxy,
          exact univ_subset_iff.mp hxy,
        end,
      superadd:=
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

lemma nprfalseCLC {agents: Type} (ha: nonempty agents): ¬ @axCLC agents (⊥) :=
begin
apply (mt (soundnessCLC (@formCLC.bot agents))),
intro hf ,
simp[global_valid, valid_m, s_entails_CLC] at hf,
apply hf (m_ex ha),
exact single.one,
end
