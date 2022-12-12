import syntax.syntaxCLC 
import syntax.axiomsCLC 
import semantics.semanticsCLC
import tactic.induction
import data.set.finite
import data.fintype.basic
local attribute [instance] classical.prop_decidable

open set list

---------------------- Soundness ----------------------

theorem soundnessCLC {agents: Type} [hN : fintype agents] (φ : formCLC agents) : 
  axCLC φ → global_valid φ :=
begin
  intro h,
  unfold global_valid valid_m s_entails_CLC,

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
    simp [s_entails_CLC],
    exact m.f.E.safety s G, },

  -- N
  { intros m s h1,
    apply m.f.E.N_max,
    by_contradiction,
    exact h1 h, },

  -- M
  { intros m s,
    apply m.f.E.monoticity s G {t: m.f.states | s_entails_CLC m t (φ & φ_1)} {t: m.f.states | s_entails_CLC m t φ},
    intros t h1,
    unfold s_entails_CLC at h1,
    exact h1.left, },

  -- S
  { intros m s h1,
    exact m.f.E.superadd s G F {t: m.f.states | s_entails_CLC m t φ} {t: m.f.states | s_entails_CLC m t φ_1} h1.left h1.right hInt, },

  -- MP
  { intros m s,
    apply ih_h,
    exact ih_h_1 m s, },

  -- Eq
  { intros m s,
    have heq: {t: m.f.states | s_entails_CLC m t φ} = {t: m.f.states | s_entails_CLC m t φ_1},
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
      simp [s_entails_CLC] at *,
      rw [← heq],
      exact h1, },
    { intro h1,
      simp [s_entails_CLC] at *,
      rw [heq],
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
  
  -- C
  { unfold s_entails_CLC,
    intros m s h,
    rw s_entails_CLC_conjunction,
    intros ψ hψ,
    simp at hψ, cases hψ with i hi, cases hi with hi hψ,
    rw [←(hψ)],
    unfold s_entails_CLC,
    intros t hts,
    split,
    { apply h,
      split,
      { split,
        { show ∀ a, a ∈ (i :: list.nil) → a ∈ G,
          simp,
          exact hi, },
        { apply exists.intro list.nil,
          unfold C_path,
          exact hts, }, }, },
    { { intros u hu, cases hu with js hu, cases hu with hjs hu, cases hu with us htu,
        apply h,
        split,
        { split,
          { show ∀ a, a ∈ (i :: js) → a ∈ G,
            simp,
            exact and.intro hi hjs, },
          { apply exists.intro (t :: us),
            unfold C_path,
            exact and.intro hts htu, }, }, }, }, },

  -- RN
  { intros m s t hst,
    apply ih, },

  -- RC
  { intros m s hs t hC,
    cases hC with is hC,
    cases hC with his hC,
    cases hC with ss hC,
    simp [s_entails_CLC] at ih,
    induction' is with i is ih_is,
    { by_contradiction,
      exact C_path_nil hC, },
    { have ih' := ih,
      specialize ih m s hs,
      rw s_entails_CLC_conjunction at ih,
      specialize ih (k i (φ & φ_1)),
      simp [s_entails_CLC] at ih,
      simp[C_path] at *,
      cases ss with u ss,
      { 
        simp[C_path] at *,
         specialize ih his.left t hC,
        exact ih.left, 
        },
      { simp[C_path] at *,
        specialize @ih_is hN _ _ _ h m u,
        apply ih_is,
        { apply and.elim_right,
          apply ih his.left u hC.left, },
          { intros m s hs,
            specialize ih' m s hs,
            simp [s_entails_CLC_conjunction, s_entails_CLC] at *,
            exact ih', },
          exact his.right,
          exact hC.right, }, }, }, 
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

def m_ex {agents : Type} [hN : fintype agents] (ha : nonempty agents) : modelCLK agents  :=
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

lemma nprfalseCLC {agents : Type} [hN : fintype agents] (ha : nonempty agents) :
  ¬ (axCLC (formCLC.bot : formCLC agents )) :=
begin
  apply (mt (soundnessCLC (@formCLC.bot agents))),
  intro hf ,
  simp[global_valid, valid_m, s_entails_CLC] at hf,
  apply hf (m_ex ha),
  exact single.one,
end
