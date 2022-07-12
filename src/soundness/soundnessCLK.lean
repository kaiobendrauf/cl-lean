
import syntax.syntaxCLK 
import syntax.axiomsCLK 
import semantics.semanticsCLK
local attribute [instance] classical.prop_decidable

open set

variable {agents : Type}

---------------------- Soundness ----------------------

theorem soundnessCLK (φ : formCLK agents) : axCLK φ → global_valid φ :=
begin
intro h,
induction h,

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
  exact m.f.E.liveness s h h1, },

{ intros m s,
  simp [s_entails],
  exact m.f.E.safety s h, },

{ intros m s h1,
  apply m.f.E.N_max,
  by_contradiction,
  exact h1 h, },

{ intros m s,
  apply m.f.E.monoticity s h_G {t: m.f.states | s_entails m t (h_φ & h_ψ)} {t: m.f.states | s_entails m t h_φ},
  intros t h1,
  exact h1.left, },

  { intros m s h1,
    exact m.f.E.superadd s h_G h_F {t: m.f.states | s_entails m t h_φ} {t: m.f.states | s_entails m t h_ψ} h1.left h1.right h_hInt, },

  { intros m s,
    apply h_ih_hImp,
    exact h_ih_hL m s, },

  { intros m s,
    have heq: {t: m.f.states | s_entails m t h_φ} = {t: m.f.states | s_entails m t h_ψ}, from
      begin
        apply set.ext,
        intros u,
        cases (h_ih m u),
        apply iff.intro,

        { intro hu,
          exact left hu, },

        { intro hu,
          exact right hu, }
      end,
    apply and.intro,

    { intro h1,
      simp[s_entails, ←heq] at *,
      exact h1, },

    { intro h1,
      simp[s_entails, heq] at *,
      exact h1, }, },

  { intros m s h1 h2 t ht,
    exact h1 t ht (h2 t ht), },

  { intros m s h,
    exact h s (m.f.rfl h_i s), },

  { intros m s h t ht u hu,
    exact h u (m.f.trans h_i s t u ht hu), },

  { intros m s h1 h2,
    exact h1 (h2 s (m.f.rfl h_i s)), },

  { intros m s t h2,
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

def m_ex (ha: nonempty agents) : modelCLK agents  :=

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

lemma nprfalseCLK {agents: Type} (ha: nonempty agents): ¬ @axCLK agents (⊥) :=
begin
apply (mt (soundnessCLK (@formCLK.bot agents))),
intro hf ,
simp[global_valid, valid_m, s_entails] at hf,
apply hf (m_ex ha),
exact single.one,
end