/-
Authors: Kai Obendrauf
Following the paper "Coalition Logic with Individual, Distributed and Common Knowledge 
by Thomas Ågotnes and Natasha Alechina,
and the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley

This file proves of completeness for CL, if we require the effectivity structure to be
truly playable.
In order to achieve this we first redefine a CL model, and the semantics for that model,
and prove soundness of CL. Then we define the filter for CL, to create a filtered canonical
model, for which we prove the truth lemma and finally completeness.
-/

import CLLean.Completeness.canonical_filtering
import CLLean.Syntax.syntaxCL
import CLLean.Semantics.playability
import Mathlib.Tactic
local attribute [instance] classical.prop_decidable

open formCL set axCL

----------------------------------------------------------
-- Model
----------------------------------------------------------
structure frameCLtrue (agents : Type) :=
(states : Type)
(hs     : nonempty states)
(E      : truly_playable_effectivity_struct agents states)

structure modelCLtrue (agents : Type) :=
(f : frameCLtrue agents)
(v : ℕ → set f.states)

----------------------------------------------------------
-- Semantic Entailment
----------------------------------------------------------

-- Definition of semantic entailment
def s_entails_CLtrue {agents : Type} (m : modelCLtrue agents) :
  m.f.states → formCL agents → Prop
  | s bot      := false
  | s (var n)  := s ∈ m.v n
  | s (φ '→ ψ) := (s_entails_CLtrue s φ) → (s_entails_CLtrue s ψ)
  | s (φ '∧ ψ) := (s_entails_CLtrue s φ) ∧ (s_entails_CLtrue s ψ)
  | s ('[G] φ) := {t : m.f.states | s_entails_CLtrue t φ} ∈ m.f.E.E (s) (G)

notation m `;` s `'⊨` φ := s_entails_CLtrue m s φ

----------------------------------------------------------
-- Validity
----------------------------------------------------------

-- φ is valid in a model M = (f,v), if it is entailed by every state of the model
def valid_m {agents: Type} (m : modelCLtrue agents) (φ : formCL agents) := 
  ∀ s : m.f.states, m; s '⊨ φ

notation m `'⊨` φ := valid_m m  φ

-- φ is globally valid, if it is valid in all models
def global_valid {agents: Type} (φ : formCL agents) :=
  ∀ m, valid_m m φ

notation `'⊨` φ := global_valid φ

----------------------------------------------------------
-- Soundness
----------------------------------------------------------

---------------------- Soundness ----------------------

theorem soundnessCLtrue {agents: Type} (φ : formCL agents) : 
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
    simp [s_entails_CLtrue],
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
    unfold s_entails_CLtrue at h1,
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
      simp only [s_entails_CLtrue, ←heq] at *,
      exact h1, },
    { intro h1,
      simp only [s_entails_CLtrue, heq] at *,
      exact h1, }, },
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

def m_ex {agents : Type} : modelCLtrue agents  :=
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
      end }, },
  v := λ _, {}, }

lemma nprfalseCLtrue {agents : Type} :
  ¬ (axCL (formCL.bot : formCL agents )) :=
begin
  apply (mt (soundnessCLtrue (@formCL.bot agents))),
  intro hf ,
  simp[global_valid, valid_m, s_entails_CLtrue] at hf,
  apply hf (m_ex),
  exact single.one,
end

----------------------------------------------------------
-- Filtration closure cl
----------------------------------------------------------
noncomputable def cl {agents : Type} : 
  formCL agents → finset (formCL agents)
|  '⊥      := {'⊥, '¬ '⊥}
| (var n)  := {var n, '¬ (var n), '⊥, '¬ '⊥}
| (φ '→ ψ) := cl φ ∪ cl ψ ∪ (ite (ψ = '⊥) {(imp φ '⊥)} {(imp φ ψ), '¬ (imp φ ψ)} )
| (φ '∧ ψ) := cl φ ∪ cl ψ ∪ {(and φ ψ), '¬ (and φ ψ)}
| ('[G] φ) := cl φ ∪ {('[G] φ), '¬ '[G] φ} 

----------------------------------------------------------
-- Lemmas about cl
----------------------------------------------------------
@[simp] lemma cl_contains_phi {agents : Type} (φ : formCL agents) :
  φ ∈ cl φ :=
begin
  cases φ,
  repeat { unfold cl, simp, },
  { split_ifs,
    repeat { simp[h] at *, }, },
end

@[simp] lemma cl_contains_bot {agents : Type} (φ : formCL agents) :
  '⊥ ∈ cl φ :=
begin
  induction φ,
  repeat { unfold cl, simp, },
  repeat { simp [φ_ih], },
  repeat { simp [φ_ih_φ, φ_ih_ψ], },
end

lemma cl_closed_single_neg {agents : Type} (φ x : formCL agents) (hx : x ∈ cl φ) :
  ∃ ψ, (ψ ∈ cl φ ∧ '⊢ (ψ '↔ ('¬ x))) :=
begin
  induction φ,
  repeat
    { unfold cl at *,
      simp only [finset.union_insert, finset.insert_union, finset.union_assoc, finset.mem_insert, 
                  finset.mem_union, finset.mem_singleton] at hx,
      cases hx,
      { apply exists.intro ('¬ x),
        simp only [hx, finset.mem_insert, finset.mem_union, finset.mem_singleton, eq_self_iff_true,
                    false_or, true_or, or_true, true_and] at *,
        apply @iff_iden (formCL agents) _ _, }, },
  { apply exists.intro ('⊥),
    simp only [hx, finset.mem_insert, eq_self_iff_true, finset.mem_singleton, or_false, true_and],
    apply MP,
    apply MP,
    apply Prop4,
    exact @dni (formCL agents) _ _,
    exact @nnn_bot (formCL agents) _, },
  { cases hx,
   { apply exists.intro (var φ),
      simp only [hx, finset.mem_insert, eq_self_iff_true, finset.mem_singleton, 
                  or_false, true_and] at *,
      exact @iff_dni (formCL agents) _ _, }, 
    cases hx,
    { apply exists.intro ('⊤),
      simp only [hx, finset.mem_insert, eq_self_iff_true, false_and, finset.mem_singleton, 
                  false_or, true_and],
      apply @iff_iden (formCL agents) _ _, },
    { apply exists.intro ('⊥),
      simp only [hx, finset.mem_insert, eq_self_iff_true, finset.mem_singleton, or_false, 
                  false_or, true_and],
      apply MP,
    apply MP,
    apply Prop4,
    exact @dni (formCL agents) _ _,
    exact @nnn_bot (formCL agents) _, }, },
  { cases hx,
    { specialize φ_ih_φ hx,
      cases φ_ih_φ with ψ hψ,
      apply exists.intro ψ,
      split,
      apply finset.mem_union_left,
      apply finset.mem_union_left,
      exact hψ.1,
      exact hψ.2, },
    cases hx,
    { specialize φ_ih_ψ hx,
      cases φ_ih_ψ with ψ hψ,
      apply exists.intro ψ,
      split,
      apply finset.mem_union_left,
      apply finset.mem_union_right,
      exact hψ.1,
      exact hψ.2, },
      { apply exists.intro (φ_φ '∧ φ_ψ),
        simp only [hx, finset.union_insert, finset.mem_insert, eq_self_iff_true, 
                    true_or, true_and],
        exact @iff_dni (formCL agents) _ _, }, },
  { unfold cl at *,
    simp only [finset.union_assoc, finset.mem_union] at hx,
    cases hx,
    { specialize φ_ih_φ hx,
      cases φ_ih_φ with ψ hψ,
      apply exists.intro ψ,
      split,
      apply finset.mem_union_left,
      apply finset.mem_union_left,
      exact hψ.1,
      exact hψ.2, },
    cases hx,
    { specialize φ_ih_ψ hx,
      cases φ_ih_ψ with ψ hψ,
      apply exists.intro ψ,
      split,
      apply finset.mem_union_left,
      apply finset.mem_union_right,
      exact hψ.1,
      exact hψ.2, },
    { split_ifs at hx,
      { simp only [h, eq_self_iff_true, if_true, finset.union_assoc, finset.mem_union, 
                    finset.mem_singleton] at *,
        simp only [hx],
        apply exists.intro (φ_φ),
        split,
        apply or.intro_left,
        exact cl_contains_phi φ_φ,
        exact @iff_dni (formCL agents) _ _, },
      { simp only [h, if_false, finset.union_insert, finset.union_assoc, finset.mem_insert, 
                    finset.mem_union, finset.mem_singleton, not_false_iff] at *,
        cases hx,
        { apply exists.intro ('¬ (φ_φ '→ φ_ψ)),
          simp only [hx, eq_self_iff_true, or_true, true_and],
          exact @iff_iden (formCL agents) _ _, },
        { apply exists.intro (φ_φ '→ φ_ψ),
          simp only [hx, eq_self_iff_true, true_or, true_and],
          exact @iff_dni (formCL agents) _ _, }, }, }, },
  { cases hx,
    { specialize φ_ih hx,
      cases φ_ih with ψ hψ,
      apply exists.intro ψ,
      split,
      { apply finset.mem_union_left,
        exact hψ.1, },
      { exact hψ.2, }, },
    { apply exists.intro ('[φ_G] φ_φ),
      simp only [hx, finset.union_insert, finset.mem_insert, eq_self_iff_true, finset.mem_union, 
                  false_or, true_or, true_and],
      exact @iff_dni (formCL agents) _ _, }, },
end

----------------------------------------------------------
-- Subformulas in CLK
----------------------------------------------------------
inductive subformula {agents : Type} : formCL agents → formCL agents → Prop
| refl            {φ}     : subformula φ φ
| trans           {φ ψ χ} : subformula φ ψ → subformula ψ χ → subformula φ χ
| and_left        {φ ψ}   : subformula φ (φ '∧ ψ)
| and_right       {φ ψ}   : subformula ψ (φ '∧ ψ)
| imp_left        {φ ψ}   : subformula φ (φ '→ ψ)
| imp_right       {φ ψ}   : subformula ψ (φ '→ ψ)
| effectivity {G} {φ}     : subformula φ ('[G] φ)

----------------------------------------------------------
-- if φ is a subformula of ψ, then cl φ ⊆ cl ψ
----------------------------------------------------------
lemma subformula.cl_subset_and_left {agents : Type}
  {φ ψ : formCL agents} : cl φ ⊆ cl (φ '∧ ψ) :=
begin
  intros x h,
  induction φ,
  repeat
  { simp only [cl, finset.insert_union, finset.union_insert, finset.union_assoc, finset.mem_insert,
                finset.mem_union, finset.mem_singleton] at *,
    repeat {cases h, simp only [h, eq_self_iff_true, and_self, false_or, true_or, or_true],},
    {simp only [h, eq_self_iff_true, and_self, true_or, false_or, or_true], }, },
end

lemma subformula.cl_subset_and_right {agents : Type} 
  {φ ψ : formCL agents} : cl ψ ⊆ cl (φ '∧ ψ) :=
begin
  intros x h,
  induction φ,
  repeat
  { simp [cl] at *,
    repeat {cases h, simp [h],},
    {simp [h], }, },
end

lemma subformula.cl_subset_imp_left {agents : Type}
  {φ ψ : formCL agents} : cl φ ⊆ cl (φ '→ ψ) :=
begin
  intros x h,
  induction φ,
  repeat
  { simp [cl] at *,
    repeat {cases h, simp [h],},
    {simp [h], }, },
end

lemma subformula.cl_subset_imp_right {agents : Type}
  {φ ψ : formCL agents} : cl ψ ⊆ cl (φ '→ ψ) :=
begin
  intros x h,
  induction φ,
  repeat
  { simp [cl] at *,
    repeat {cases h, simp [h],},
    {simp [h], }, },
end

lemma subformula.cl_subset_effectivity {agents : Type} 
  {φ : formCL agents} {G : set (agents)} : cl φ ⊆ cl ('[G] φ) :=
begin
  intros x h,
  induction φ,
  repeat
  { simp [cl] at *,
    repeat {cases h, simp [h],},
    {simp [h], }, },
end

lemma subformula.cl_subset {agents : Type}
  {φ ψ : formCL agents} (h : subformula φ ψ) : cl φ ⊆ cl ψ :=
begin
  induction h with _ _ _ _ _ h ih ih',
  { exact finset.subset.rfl, },
  { exact finset.subset.trans ih ih', },
  { exact subformula.cl_subset_and_left, },
  { exact subformula.cl_subset_and_right, },
  { exact subformula.cl_subset_imp_left, },
  { exact subformula.cl_subset_imp_right, },
  { exact subformula.cl_subset_effectivity, },
end

lemma subformula.mem_cl {agents : Type}
  {φ ψ : formCL agents} (h : subformula φ ψ) : φ ∈ cl ψ :=
h.cl_subset (cl_contains_phi φ)

lemma subformula.in_cl_sub {agents : Type}
  {φ ψ χ : formCL agents} (hcl : ψ ∈ cl φ) (hsub : subformula χ ψ) : χ ∈ cl φ :=
begin
  induction hsub with _ _ _ _ hsub1 hsub2 hih1 hih2,
  { exact hcl, },
  { exact hih1 (hih2 hcl), },
  all_goals
  { induction φ,
    repeat 
    { simp only [cl, finset.mem_insert, finset.mem_singleton, or_self] at hcl,
      cases hcl, }, },
  any_goals
  { simp only [cl, finset.mem_insert, finset.mem_union, finset.mem_singleton, finset.mem_image, 
                  exists_false, or_false, false_or] at hcl,
      cases hcl, },
  repeat { apply or.elim hcl, all_goals { intro hcl, }, }, 
  any_goals { split_ifs at hcl, }, 
  any_goals { rw hcl.1 at *, rw hcl.2 at *, },
  any_goals { rw h at *, },
  any_goals { simp only [cl, finset.union_assoc, finset.mem_insert, finset.mem_union, 
                          finset.mem_singleton, false_or, finset.mem_insert, finset.mem_singleton, 
                          or_self, or_false, eq_self_iff_true, and_self, or_true, true_or] 
              at hcl, },
  repeat { apply or.elim hcl, all_goals { intro hcl, }, },
  any_goals { rw hcl.1 at *, rw hcl.2 at *, },
  any_goals { rw h at *, },
  any_goals { solve1 { by_contradiction, exact hcl, }, },
  any_goals { simp only [cl, φ_ih_φ hcl, finset.mem_union, true_or, or_true], },
  any_goals { simp only [cl, φ_ih_ψ hcl, finset.mem_union, true_or, or_true], },
  any_goals { simp only [cl, finset.mem_union, cl_contains_phi, true_or, or_true], },
  any_goals { simp only [φ_ih hcl, true_or], },
  any_goals { simp only [if_true, finset.mem_insert, finset.mem_singleton, or_false, 
                          eq_self_iff_true, and_self, or_true, true_or], }, 
  any_goals { simp only [hcl.1, hcl.2, eq_self_iff_true, cl_contains_phi, and_self, or_false, 
                          or_true, true_or], },
  any_goals { simp only [h, if_false, finset.mem_insert, eq_self_iff_true, and_self, 
                          finset.mem_singleton, and_false, or_false, or_true], },
  any_goals { simp only [cl_contains_bot, or_self, true_or], },
end

namespace canonical
----------------------------------------------------------
-- Canonical Model CL
----------------------------------------------------------
@[simps] noncomputable def Mf_CL {agents : Type} [ha : nonempty agents] 
  (φ : formCL agents) : modelCLtrue agents := 
{ f := 
  { states := S_f (canonical_model_CL agents (formCL agents) nprfalseCLtrue) cl φ,
    hs := canonical.S_f.nonempty _ _ _,
    E := truly_playable_from_finite 
    { E          := E_f,
      liveness   := Ef_liveness,
      safety     := Ef_safety,
      N_max      := Ef_nmax (cl_closed_single_neg φ),
      mono       := Ef_mono,
      superadd   := Ef_superadd (cl_closed_single_neg φ), }, },
  v := λ  n, {s | (Pformula.var n) ∈ s.1.1}, }


/-- Allows us to write `φ ∈ s` instead of `φ ∈ s` -/
instance Mf_CL.f.states.set_like {agents : Type} [ha : nonempty agents] 
  {φ : formCL agents} : set_like ((Mf_CL φ).f.states) (formCL agents) :=
{ coe := λ s, s.1.1,
  coe_injective' :=
  begin
    unfold_coes,
    intros sf tf h,
    simp only [subtype.val_eq_coe, finset.set_of_mem, finset.coe_inj] at h,
    apply subtype.coe_injective,
    apply subtype.coe_injective,
    exact h,
  end, }

----------------------------------------------------------
-- Truth Lemma 
----------------------------------------------------------

-- E
----------------------------------------------------------
-- Truth Lemma: case [G]ψ, where G = N :
lemma truth_E_univ {agents : Type} [ha : nonempty agents]
  {φ ψ : formCL agents} {G : set agents} (sf : (Mf_CL φ).f.states) 
  (hφ : ψ ∈ cl φ) (hφ' : ('[G] ψ) ∈ cl φ)
  (ih : ∀ tf, ((Mf_CL φ); tf '⊨ ψ) ↔ (ψ ∈ tf)) (hG : G = univ) :
  ((Mf_CL φ); sf '⊨ ('[G] ψ)) ↔ (('[G] ψ) ∈ sf) :=
begin
  let MC' := canonical_model_CL agents (formCL agents) nprfalseCLtrue,
      --  M f , sf ⊨ ψ
  calc ((Mf_CL φ); sf '⊨ ('[G]ψ))
      -- ↔ {sf ∈ Sf | M f , sf ⊨ ψ} ∈ Ef (sf )(N ), by definition ⊨
      ↔ {tf | (Mf_CL φ); tf '⊨ ψ} ∈ (Mf_CL φ).f.E.E sf G : 
          by unfold s_entails_CLtrue
      -- ↔ ∃t ∈ SC′, sf = tf and  ̃φ{sf ∈Sf |M f ,sf ⊨ψ} ∈ EC′(t)(N ), by definition Ef.
  ... ↔ ∃ t, (sf = s_f cl φ t) ∧ 
        tilde MC'.f.states (phi_X_set {sf | (Mf_CL φ); sf '⊨ ψ}) ∈ MC'.f.E.E t G :
    begin
      dsimp [E_f, MC', hG, eq_self_iff_true, if_true] {eta := ff},
      simp only [hG, eq_self_iff_true, if_true] {eta := ff},
    end
      -- ↔ ∃t ∈ SC′, sf = tf and  ̃φ{sf ∈Sf |ψ∈sf } ∈ EC′(t)(N ), by ih.
  ... ↔ ∃ t, (sf = s_f cl φ t) ∧ 
        tilde MC'.f.states (phi_X_set {sf : (Mf_CL φ).f.states | ψ ∈ sf}) ∈ MC'.f.E.E t univ :
    by simp only [ih, hG]
      -- ↔ ∃t ∈ SC′, sf = tf and  ̃ψ ∈ EC′(t)(N ), by Lemma 6.
  ... ↔ ∃ t, (sf = s_f cl φ t) ∧ tilde MC'.f.states ψ ∈ MC'.f.E.E t (univ) :
      begin
        have hiff : '⊢ ((phi_X_set {sf : (Mf_CL φ).f.states | ψ ∈ sf}) '↔ ψ), 
          from phi_X_contains_iff_psi (cl_closed_single_neg φ) (hφ),
        have htilde := @tilde_ax_iff _ (formCL agents) _ _ _ nprfalseCLtrue _ _ hiff,
        rw htilde,
      end
  -- ↔ ∃t ∈ SC′, sf = tf and [N ] ψ ∈ t, by Lemma 7.
  ... ↔ ∃ t, (sf = s_f cl φ t) ∧ ('[univ] ψ) ∈ t :
    begin
      simp only [E_s_contains_tilde_iff_E_in_s _ univ],
      exact iff.rfl,
    end
  -- ↔ [N] ψ ∈ sf, from left to right because [N] ψ ∈ tf, and from right to left when s = t.
  ... ↔ ('[G] ψ) ∈ sf : 
      begin
        rw hG at *,
        split,
        { intro h,
          obtain ⟨t, ⟨heq, h⟩⟩ := h,
          exact (sf_eq_forall heq).mpr ⟨h, hφ'⟩, },
        { intro h,
          obtain ⟨s, hs⟩ := s_f_to_s sf,
          apply exists.intro s,
          exact ⟨sf_eq_s_f  @hs, (hs.mp h).left⟩, },
      end,
end

-- Truth Lemma: case [G]ψ, where G = N :
lemma truth_E_nuniv {agents : Type} [ha : nonempty agents]
  {φ ψ : formCL agents} {G : set agents} (sf : (Mf_CL φ).f.states) 
  (hφ : ψ ∈ cl φ) (hφ' : ('[G] ψ) ∈ cl φ)
  (ih : ∀ tf, ((Mf_CL φ); tf '⊨ ψ) ↔ (ψ ∈ tf)) (hG : G ≠ univ) :
  ((Mf_CL φ); sf '⊨ ('[G] ψ)) ↔ (('[G] ψ) ∈ sf) :=
begin
  let MC' := canonical_model_CL agents (formCL agents) nprfalseCLtrue,
      -- M f , sf ⊨ ψ
  calc ((Mf_CL φ); sf '⊨ ('[G]ψ))
      -- ↔ {sf ∈ Sf | M f , sf ⊨ ψ} ∈ Ef (sf )(G ), by definition ⊨
      ↔ {tf | (Mf_CL φ); tf '⊨ ψ} ∈ (Mf_CL φ).f.E.E sf G : 
          by unfold s_entails_CLtrue
      -- ↔ ∀t ∈ SC′, sf = tf and  ̃φ{sf ∈Sf |M f ,sf ⊨ψ} ∈ EC′(t)(G ), by definition Ef .
  ... ↔ ∀ t, (sf = s_f cl φ t) → 
          tilde MC'.f.states (phi_X_set {sf | (Mf_CL φ); sf '⊨ ψ}) ∈ MC'.f.E.E t G :
      begin
        dsimp [E_f, MC'],
        simp only [hG, if_false] {eta := ff},
      end
      -- ↔ ∀t ∈ SC′, sf = tf ⇒  ̃φ{sf ∈Sf |ψ∈sf } ∈ EC′(t)(G ), by ih.
  ... ↔ ∀ t, (sf = s_f cl φ t) → 
          tilde MC'.f.states (phi_X_set {sf : (Mf_CL φ).f.states | ψ ∈ sf}) ∈ MC'.f.E.E t G :
      by simp only [ih]
      -- ↔ ∀t ∈ SC′, sf = tf ⇒  ̃ψ ∈ EC′(t)(G ), by Lemma 6.
  ... ↔ ∀ t, (sf = s_f cl φ t) →  tilde MC'.f.states ψ ∈ MC'.f.E.E t G : 
      begin
        have hiff : '⊢ ((phi_X_set {sf : (Mf_CL φ).f.states | ψ ∈ sf}) '↔ ψ), 
          from phi_X_contains_iff_psi (cl_closed_single_neg φ) (hφ),
        have htilde := @tilde_ax_iff _ (formCL agents) _ _ _ nprfalseCLtrue _ _ hiff,
        rw htilde,
      end
      -- ↔ ∀t ∈ SC′, sf = tf ⇒ [G ]ψ ∈ t, by Lemma 7.
  ... ↔ ∀ t, (sf = s_f cl φ t) → ('[G] ψ) ∈ t :
    begin
      simp only [E_s_contains_tilde_iff_E_in_s _ G],
      exact iff.rfl,
    end
    -- ↔ [G] ψ ∈ sf , from left to right when s = t, from right to left because [G]ψ ∈ sf = tf 
  ... ↔ (('[G] ψ) ∈ sf) : 
      begin
        split,
        { intro h,
          obtain ⟨s, hs⟩ := s_f_to_s sf,
          specialize h s (eq.symm (s_f_eq_sf @hs)),
          apply hs.mpr,
          exact ⟨h, hφ'⟩, },
        { intros h t ht,
          exact ((sf_eq_forall ht).mp h).1, },
      end,
end

-- Truth Lemma
----------------------------------------------------------
lemma truth_lemma_CLK {agents : Type} [ha : nonempty agents]
  (φ ψ : formCL agents) (sf : (Mf_CL φ).f.states) (hφ : ψ ∈ cl φ) :
  ((Mf_CL φ); sf '⊨ ψ) ↔ (ψ ∈ sf) :=
begin
  -- This proof is by induction on φ.
  induction' ψ fixing ha ψ with n ψ χ _ _ ψ χ _ _, -- sf needs to vary for the modal operators
  all_goals
  { obtain ⟨s, hs⟩ := s_f_to_s sf, },

  { -- case bot
    simp [s_entails_CLtrue, explosion],
    apply s_f_n_contains,
    exact @hs, 
    apply or.intro_left,
    exact @bot_not_mem_of_ax_consistent (formCL agents) _ s.1 s.2.1, },

  { -- case var
    simpa [s_entails_CLtrue], },

  { -- case and
    have hψ := subformula.in_cl_sub hφ subformula.and_left,
    have hχ := subformula.in_cl_sub hφ subformula.and_right,
    specialize ih_ψ _ sf hψ,
    specialize ih_χ _ sf hχ,
    unfold s_entails_CLtrue at *,
    rw [ih_ψ, ih_χ, hs, hs, hs],
    simp only [hφ, hψ, hχ, and_true],
    split,
    { rintro ⟨hψs, hχs⟩,
      apply max_ax_contains_by_set_proof_2h s.2 hψs hχs axCL.Prop4 },
    { intro hψχs,
      split,
      { apply max_ax_contains_by_set_proof s.2 hψχs axCL.Prop5 },
      { apply max_ax_contains_by_set_proof s.2 hψχs axCL.Prop6 } } },

  { -- case imp
    have hψ := subformula.in_cl_sub hφ subformula.imp_left,
    have hχ := subformula.in_cl_sub hφ subformula.imp_right,
    specialize ih_ψ _ sf hψ,
    specialize ih_χ _ sf hχ,
    unfold s_entails_CLtrue at *,
    rw [ih_ψ, ih_χ, hs, hs, hs],
    simp only [hφ, hψ, hχ, and_true],
    split,
    { intro h,
      exact max_ax_contains_imp_by_proof s.2 h, },
    { intros h hφ,
      apply max_ax_contains_by_set_proof_2h s.2 hφ h likemp, }, },

  { -- case [G] ψ
    have hψ := subformula.in_cl_sub hφ subformula.effectivity,
    let ih := λ sf, ih _ sf hψ,
    cases em (G = univ) with hG hG,
    { exact truth_E_univ _ hψ hφ ih hG,},
    { exact truth_E_nuniv _ hψ hφ ih hG, }, },
end

----------------------------------------------------------
-- Completeness
----------------------------------------------------------

-- Completeness
----------------------------------------------------------
theorem completenessCLK {agents : Type} [ha : nonempty agents] 
  (φ : formCL agents) : ('⊨ φ) → '⊢ φ :=
begin
  -- rw from contrapositive
  rw ←not_imp_not, 
  -- assume ¬ ⊢ φ
  intro hnax,
  -- from ¬ ⊢ φ, have that {¬ φ} is a consistent set
  obtain ⟨s', hmax, hnφ⟩ := @exists_max_ax_consistent_neg_mem (formCL agents) _ _ hnax,
  -- show that φ is not globally valid, 
  -- by showing that there exists some model where φ is not valid.
  simp[global_valid],
  -- let that model be the canonical model
  apply exists.intro (Mf_CL φ),
  -- in the canonical model (M) there exists some state (s) where ¬ M s ⊨ φ
  simp[valid_m],
  -- let that state (s) be the maximally consistent set extended from {¬ φ}
  obtain ⟨s, hs⟩ : 
    ∃ s : (canonical_model_CL agents (formCL agents) nprfalseCLtrue).f.states, s = ⟨s', hmax⟩,
    from exists_apply_eq_apply _ _,
  obtain ⟨sf, hsf⟩ := s_to_s_f cl φ s,
  apply exists.intro sf,
  -- assume by contradiction that M s ⊨ φ
  intro hf,
  -- by the truth lemma φ ∈ s
  have hφ, from (truth_lemma_CLK φ _ sf (cl_contains_phi φ)).mp hf,
  -- in that state (s), φ ∈ s, so we do not have ¬ φ ∈ s (by consistency)
  -- contradiction with hnφ
  rw hsf at hφ,
  apply contra_contains_pr_false s.2 hφ.left,
  rw hs,
  exact hnφ,
end

end canonical
