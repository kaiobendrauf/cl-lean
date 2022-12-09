import syntax.syntaxCLC 
import syntax.axiomsCLC 
import semantics.semanticsCLC
import tactic.induction
import data.set.finite
import data.fintype.basic
local attribute [instance] classical.prop_decidable

open set list

---------------------- Soundness ----------------------

lemma soundness_E_helper_l {agents: Type} [hN : fintype agents] {φ : formCLC agents}
  {m : modelCLK agents} {s : m.f.to_frameCL.states} {G : set agents} {is : list agents} (hG : ∀ i ∈ is, i ∈ G) 
  (h : (∀ i, i ∈ G → ∀ (t : m.f.to_frameCL.states), t ∈ m.f.rel i s → s_entails_CLC.aux m φ t)) : 
  s_entails_CLC.aux m (finite_conjunction (map (λ (i : agents), k i φ) is)) s  := 
begin
  induction is with i is ih,
  { simp [finite_conjunction],
    have : s_entails_CLC.aux m (¬ ⊥) s, from by simp [s_entails_CLC.aux],
    exact this, },
  { simp [finite_conjunction],
    have : s_entails_CLC.aux m (k i φ & finite_conjunction (map (λ (i : agents), k i φ) is)) s, from
    begin
      simp at hG,
      unfold s_entails_CLC.aux,
      exact and.intro (λ t ht, h i hG.left t ht) (ih hG.right),
    end,
    exact this, },
end

lemma soundness_E_helper_r {agents: Type} [hN : fintype agents] {φ : formCLC agents}
  {m : modelCLK agents} {s t : m.f.to_frameCL.states} {G : set agents} {i : agents}  {is : list agents}
  (hi : i ∈ G) (hG : ∀ i, i ∈ is ↔ i ∈ G) (ht : t ∈ m.f.rel i s)
  (h : s_entails_CLC.aux m (finite_conjunction (map (λ (i : agents), k i φ) is)) s): 
  s_entails_CLC.aux m φ t := 
begin
  induction' is with j is ih,
  { have := (hG i).mpr hi,
    exact false.rec (s_entails_CLC.aux m φ t) this, },
  { simp [finite_conjunction] at h,
    have h : s_entails_CLC.aux m (k j φ & finite_conjunction (map (λ (i : agents), k i φ) is)) s, 
      from h,
    simp [s_entails_CLC.aux] at h,
    cases ((hG i).mpr hi) with hi' hi',
    { rw ←hi' at *,
      apply h.left,
      exact ht, },
    { apply @ih hN φ m s t {x | x ∈ is} i,
      exact hi',
      exact ht,
      simp,
      exact h.right, }, },
end

theorem soundnessCLC {agents: Type} [hN : fintype agents] (φ : formCLC agents) : 
  axCLC φ → global_valid φ :=
begin
  intro h,
  unfold global_valid valid_m s_entails_CLC,

  induction' h,

  -- Prop 1
  { unfold s_entails_CLC.aux,
    intros m s h1 h2, 
    exact h1, },

  -- Prop 2
  { unfold s_entails_CLC.aux,
    intros m s h1 h2 h3, 
    apply h1, 
      { exact h3,},

      { apply h2, 
        exact h3 }, },

  -- Prop 3
  { unfold s_entails_CLC.aux,
    intros m s h1 h2,
    by_contradiction hf,
    exact (h1 hf) (h2 hf), },

  -- Prop 4
  { unfold s_entails_CLC.aux,
    intros m s h1 h2, 
    exact and.intro h1 h2, },

  -- Prop 5
  { unfold s_entails_CLC.aux,
    intros m s h1, 
    exact h1.left, },

  -- Prop 6
  { unfold s_entails_CLC.aux,
    intros m s h1, 
    exact h1.right, },

  -- Prop 7
  { unfold s_entails_CLC.aux,
    intros m s h1 h2,
    by_contradiction hf,
    exact h1 hf h2, },

  -- Bot
  { unfold s_entails_CLC.aux,
    intros m s h1, 
    exact m.f.E.liveness s G h1, },

  -- Top
  { unfold s_entails_CLC.aux,
    intros m s,
    simp [s_entails_CLC],
    exact m.f.E.safety s G, },

  -- N
  { unfold s_entails_CLC.aux,
    intros m s h1,
    apply m.f.E.N_max,
    by_contradiction,
    exact h1 h, },

  -- M
  { intros m s,
    rw [s_entails_CLC.aux, s_entails_CLC.aux, s_entails_CLC.aux], -- Don't unfold too much, otherwise the following line won't apply.
    apply m.f.E.monoticity s G {t: m.f.states | s_entails_CLC m t (φ & φ_1)} {t: m.f.states | s_entails_CLC m t φ},
    intros t h1,
    unfold s_entails_CLC s_entails_CLC.aux at h1,
    exact h1.left, },

  -- S
  {  unfold s_entails_CLC.aux,
    intros m s h1,
    exact m.f.E.superadd s G F {t: m.f.states | s_entails_CLC m t φ} {t: m.f.states | s_entails_CLC m t φ_1} h1.left h1.right hInt, },

  -- MP
  { intros m s,
    unfold s_entails_CLC.aux at ih_h,
    apply ih_h,
    exact ih_h_1 m s, },

  -- Eq
  { intros m s,
    have heq: {t: m.f.states | s_entails_CLC m t φ} = {t: m.f.states | s_entails_CLC m t φ_1},
    { apply set.ext,
      intros u,
      unfold s_entails_CLC.aux at ih,
      cases (ih m u),
      apply iff.intro,

      { intro hu,
        exact left hu, },

      { intro hu,
        exact right hu } },
    unfold s_entails_CLC.aux,
    apply and.intro,

    { intro h1,
      simp [s_entails_CLC, s_entails_CLC.aux] at *,
      rw [← heq],
      exact h1, },

    { intro h1,
      simp [s_entails_CLC, s_entails_CLC.aux] at *,
      rw [heq],
      exact h1, }, },

  -- K
  { unfold s_entails_CLC.aux,
    intros m s h1 h2 t ht,
    exact h1 t ht (h2 t ht), },

  -- T
  { unfold s_entails_CLC.aux,
    intros m s h,
    exact h s (m.f.rfl i s), },

  -- Four
  { unfold s_entails_CLC.aux,
    intros m s h t ht u hu,
    exact h u (m.f.trans i s t u ht hu), },

  -- Five
  { unfold s_entails_CLC.aux,
    intros m s h1 t ht ht1,
    apply h1,
    intros u hu,
    apply ht1,
    exact m.f.trans _ _ _ _ (m.f.sym _ _ _ ht) hu, },

  -- E 
  { unfold s_entails_CLC.aux,
    intros m s,
    split, 
    { apply soundness_E_helper_l,
      simp, },
    { intros h i hi t ht,
      apply soundness_E_helper_r hi _ ht h,
      simp, }, },
  
  -- C
  { unfold s_entails_CLC.aux,
    intros m s hC i hi t hts,
    split,
    { apply hC t,
      apply exists.intro (i :: list.nil),
      split, simp,
      {exact hi, },
      { apply exists.intro list.nil,
        simp [C_path],
        exact hts, }, },
      { intros u hu,
        apply hC u,
        cases hu with is hu,
        cases hu with his hu,
        cases hu with ss hu,
        cases is with hd is,
        { by_contradiction,
          exact C_path_nil hu, },
        { apply exists.intro (i :: hd :: is),
          split,
          { simp at *, split, exact hi, exact his, },
          { apply exists.intro (t :: ss),
            simp [C_path] at *,
            split, exact hts, exact hu, }, }, }, },

  -- RN
  { unfold s_entails_CLC.aux,
    intros m s t hst,
    apply ih, },

  -- RC
  { unfold s_entails_CLC.aux,
    intros m s hs t hC,
    cases hC with is hC,
    cases hC with his hC,
    cases hC with ss hC,
    induction' is with i is ih_is,
    { by_contradiction,
      exact C_path_nil hC, },
    { simp[s_entails_CLC.aux, C_path] at *,
      cases ss with u ss,
      { simp[C_path] at *,
        specialize ih m s hs i his.left t hC,
        exact ih.left, },
      { simp[C_path] at *,
        specialize @ih_is hN _ _ _ h ih m u,
        apply ih_is,
        { apply and.elim_right,
          apply ih m s hs i his.left u hC.left, },
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
  simp[global_valid, valid_m, s_entails_CLC, s_entails_CLC.aux] at hf,
  apply hf (m_ex ha),
  exact single.one,
end
