/-
Authors: Kai Obendrauf
Following the paper "Coalition Logic with Individual, Distributed and Common Knowledge 
by Thomas Ågotnes and Natasha Alechina
and the thesis "A Formalization of Dynamic Epistemic Logic" by Paula Neeley

This file proves of completeness for CL, if we require the effectivity structure to be
truly playable.
In order to achieve this we first redefine a CL model, and the semantics for that model
and prove soundness of CL. Then we define the filter for CL, to create a filtered canonical
model, for which we prove the truth lemma and finally completeness.
-/

import CLLean.Completeness.canonical_filtering
import CLLean.Syntax.syntaxCL
import CLLean.Semantics.playability
import Mathlib.Tactic
local attribute [instance] classical.prop_decidable

open formCL Set axCL

----------------------------------------------------------
-- Model
----------------------------------------------------------
structure frameCLtrue (agents : Type) :=
(states : Type)
(hs     : Nonempty states)
(E      : truly_playable_effectivity_struct agents states)

structure modelCLtrue (agents : Type) :=
(f : frameCLtrue agents)
(v : ℕ → Set f.states)

----------------------------------------------------------
-- Semantic Entailment
----------------------------------------------------------

-- Definition of semantic entailment
def s_entails_CLtrue {agents : Type} (m : modelCLtrue agents) :
  m.f.states → formCL agents → Prop
  | s bot      := false
  | s (var n)  := s ∈ m.v n
  | s (φ _→ ψ) := (s_entails_CLtrue s φ) → (s_entails_CLtrue s ψ)
  | s (φ _∧ ψ) := (s_entails_CLtrue s φ) ∧ (s_entails_CLtrue s ψ)
  | s ('[G] φ) := {t : m.f.states | s_entails_CLtrue t φ} ∈ m.f.E.E (s) (G)

notation m `;` s `_⊨` φ := s_entails_CLtrue m s φ

----------------------------------------------------------
-- Validity
----------------------------------------------------------

-- φ is valid in a model M = (f,v), if it is entailed by every state of the model
def valid_m {agents: Type} (m : modelCLtrue agents) (φ : formCL agents) := 
  ∀ s : m.f.states, m; s _⊨ φ

notation m `_⊨` φ := valid_m m  φ

-- φ is globally valid, if it is valid in all models
def global_valid {agents: Type} (φ : formCL agents) :=
  ∀ m, valid_m m φ

notation `_⊨` φ := global_valid φ

----------------------------------------------------------
-- Soundness
----------------------------------------------------------

---------------------- Soundness ----------------------

theorem soundnessCLtrue {agents: Type} (φ : formCL agents) : 
  _⊢ φ → _⊨ φ := by
  intro h
  induction' h

  -- Prop 1
  { intro m s h1 h2
    exact h1, }

  -- Prop 2
  { intro m s h1 h2 h3
    apply h1
      { exact h3,}

      { apply h2
        exact h3 }, }

  -- Prop 3
  { intro m s h1 h2
    by_contra hf
    exact (h1 hf) (h2 hf), }

  -- Prop 4
  { intro m s h1 h2
    exact And.intro h1 h2, }

  -- Prop 5
  { intro m s h1
    exact h1.left, }

  -- Prop 6
  { intro m s h1
    exact h1.right, }

  -- Prop 7
  { intro m s h1 h2
    by_contra hf
    exact h1 hf h2, }

  -- Bot
  { intro m s h1
    exact m.f.E.liveness s G h1, }

  -- Top
  { intro m s
    simp [s_entails_CLtrue]
    exact m.f.E.safety s G, }

  -- N
  { intro m s h1
    apply m.f.E.N_max
    by_contra
    exact h1 h, }

  -- M
  { intro m s
    apply m.f.E.mono s G {t : m.f.states | m; t _⊨ (φ _∧ φ_1)}
      {t : m.f.states | m; t _⊨ φ}
    intro t h1
    unfold s_entails_CLtrue at h1
    exact h1.left, }

  -- S
  { intro m s h1
    exact m.f.E.superadd s G F {t : m.f.states | m; t _⊨ φ} 
      {t : m.f.states | m; t _⊨ φ_1} h1.left h1.right hInt, }

  -- MP
  { intro m s
    apply ih_h
    exact ih_h_1 m s, }

  -- Eq
  { intro m s
    have heq: {t : m.f.states | m; t _⊨ φ} = {t : m.f.states | m; t _⊨ φ_1}
    { apply Set.ext
      intro u
      cases (ih m u)
      apply Iff.intro
      { intro hu
        exact left hu, }
      { intro hu
        exact right hu } }
    apply And.intro
    { intro h1
      simp only [s_entails_CLtrue, ←heq] at *
      exact h1, }
    { intro h1
      simp only [s_entails_CLtrue, heq] at *
      exact h1, }, }

----------------------------------------------------------
-- CL does not prove ⊥
----------------------------------------------------------
-- create an example Model
inductive single : Type
  | one: single

lemma univ_single : (Set.univ: Set single) = {single.one} :=  by
  rw eq_comm
  rw Set.eq_univ_iff_forall
  intro x
  cases x
  simp

instance single_nonempty : Nonempty single :=  by
  apply exists_true_iff_nonempty.mp
  apply Exists.intro single.one
  exact trivial

instance single_finite : Fintype single :=  by
  refine {elems := {single.one}, complete := _}
  intro x
  cases x
  exact Finset.mem_singleton.mpr rfl

def m_ex {agents : Type} : modelCLtrue agents  :=
{ f := 
  { states := single
    hs := single_nonempty
    E  :=  truly_playable_from_finite
    { E := λ s G, {{single.one}}
      liveness :=  by
        intro _ _ hf
        simp at hf
        rw Set.ext_iff at hf
        simp at hf
        apply hf single.one
        refl
      safety:= by
          intro _ _, simp at *
          exact univ_single
      N_max := by
          intro _ _ hxc, simp at *
          rw ←univ_single at *
          have hcond : {single.one} ≠ (∅: Set single)

            { intro hf
              rw Set.ext_iff at hf
              simp at *
              apply hf single.one
              refl, }
          simp [hcond] at *, by_contra
          have hex: ∃ x, x ∈ X:= nonempty_def.mp (ne_empty_iff_nonempty.mp hxc)
          cases hex with s hs
          cases s
          rw ←singleton_subset_iff at hs
          rw ←univ_single at hs
          exact h (univ_subset_iff.mp hs)
      mono := by
          intro _ _ _ _ hxy hx
          simp [←univ_single] at *
          rw hx at hxy
          exact univ_subset_iff.mp hxy
      superadd := by
        intro _ _ _ _ _ hX hY hGF
        simp at *
        simp[hX, hY]
  v := λ _, {}, }

lemma nprfalseCLtrue {agents : Type} :
  ¬ (axCL (formCL.bot : formCL agents )) := by
  apply (mt (soundnessCLtrue (@formCL.bot agents)))
  intro hf 
  simp[global_valid, valid_m, s_entails_CLtrue] at hf
  apply hf (m_ex)
  exact single.one

----------------------------------------------------------
-- Filtration closure cl
----------------------------------------------------------
noncomputable def cl {agents : Type} : 
  formCL agents → Finset (formCL agents)
|  _⊥      := {_⊥, _¬ _⊥}
| (var n)  := {var n, _¬ (var n), _⊥, _¬ _⊥}
| (φ _→ ψ) := cl φ ∪ cl ψ ∪ (ite (ψ = _⊥) {(imp φ _⊥)} {(imp φ ψ), _¬ (imp φ ψ)} )
| (φ _∧ ψ) := cl φ ∪ cl ψ ∪ {(and φ ψ), _¬ (and φ ψ)}
| ('[G] φ) := cl φ ∪ {('[G] φ), _¬ '[G] φ} 

----------------------------------------------------------
-- Lemmas about cl
----------------------------------------------------------
@[simp] lemma cl_contains_phi {agents : Type} (φ : formCL agents) :
  φ ∈ cl φ := by
  cases φ
  repeat { unfold cl, simp, }
  { split_ifs
    repeat { simp[h] at *, }, }

@[simp] lemma cl_contains_bot {agents : Type} (φ : formCL agents) :
  _⊥ ∈ cl φ := by
  induction φ
  repeat { unfold cl, simp, }
  repeat { simp [φ_ih], }
  repeat { simp [φ_ih_φ, φ_ih_ψ], }

lemma cl_closed_single_neg {agents : Type} (φ x : formCL agents) (hx : x ∈ cl φ) :
  ∃ ψ, (ψ ∈ cl φ ∧ _⊢ (ψ _↔ (_¬ x))) := by
  induction φ
  repeat
    { unfold cl at *
      simp only [Finset.union_insert, Finset.insert_union, Finset.union_assoc, Finset.mem_insert
                  Finset.mem_union, Finset.mem_singleton] at hx
      cases hx
      { apply Exists.intro (_¬ x)
        simp only [hx, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, eq_self_iff_true
                    false_or, true_or, or_true, true_and] at *
        apply @iff_iden (formCL agents) _ _, }, }
  { apply Exists.intro (_⊥)
    simp only [hx, Finset.mem_insert, eq_self_iff_true, Finset.mem_singleton, or_false, true_and]
    apply MP
    apply MP
    apply Prop4
    exact @dni (formCL agents) _ _
    exact @nnn_bot (formCL agents) _, }
  { cases hx
   { apply Exists.intro (var φ)
      simp only [hx, Finset.mem_insert, eq_self_iff_true, Finset.mem_singleton
                  or_false, true_and] at *
      exact @iff_dni (formCL agents) _ _, }
    cases hx
    { apply Exists.intro ('⊤)
      simp only [hx, Finset.mem_insert, eq_self_iff_true, false_and, Finset.mem_singleton
                  false_or, true_and]
      apply @iff_iden (formCL agents) _ _, }
    { apply Exists.intro (_⊥)
      simp only [hx, Finset.mem_insert, eq_self_iff_true, Finset.mem_singleton, or_false
                  false_or, true_and]
      apply MP
    apply MP
    apply Prop4
    exact @dni (formCL agents) _ _
    exact @nnn_bot (formCL agents) _, }, }
  { cases hx
    { specialize φ_ih_φ hx
      cases φ_ih_φ with ψ hψ
      apply Exists.intro ψ
      split
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact hψ.1
      exact hψ.2, }
    cases hx
    { specialize φ_ih_ψ hx
      cases φ_ih_ψ with ψ hψ
      apply Exists.intro ψ
      split
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact hψ.1
      exact hψ.2, }
      { apply Exists.intro (φ_φ _∧ φ_ψ)
        simp only [hx, Finset.union_insert, Finset.mem_insert, eq_self_iff_true
                    true_or, true_and]
        exact @iff_dni (formCL agents) _ _, }, }
  { unfold cl at *
    simp only [Finset.union_assoc, Finset.mem_union] at hx
    cases hx
    { specialize φ_ih_φ hx
      cases φ_ih_φ with ψ hψ
      apply Exists.intro ψ
      split
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact hψ.1
      exact hψ.2, }
    cases hx
    { specialize φ_ih_ψ hx
      cases φ_ih_ψ with ψ hψ
      apply Exists.intro ψ
      split
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact hψ.1
      exact hψ.2, }
    { split_ifs at hx
      { simp only [h, eq_self_iff_true, if_true, Finset.union_assoc, Finset.mem_union
                    Finset.mem_singleton] at *
        simp only [hx]
        apply Exists.intro (φ_φ)
        split
        apply or.intro_left
        exact cl_contains_phi φ_φ
        exact @iff_dni (formCL agents) _ _, }
      { simp only [h, if_false, Finset.union_insert, Finset.union_assoc, Finset.mem_insert
                    Finset.mem_union, Finset.mem_singleton, not_false_iff] at *
        cases hx
        { apply Exists.intro (_¬ (φ_φ _→ φ_ψ))
          simp only [hx, eq_self_iff_true, or_true, true_and]
          exact @iff_iden (formCL agents) _ _, }
        { apply Exists.intro (φ_φ _→ φ_ψ)
          simp only [hx, eq_self_iff_true, true_or, true_and]
          exact @iff_dni (formCL agents) _ _, }, }, }, }
  { cases hx
    { specialize φ_ih hx
      cases φ_ih with ψ hψ
      apply Exists.intro ψ
      split
      { apply Finset.mem_union_left
        exact hψ.1, }
      { exact hψ.2, }, }
    { apply Exists.intro ('[φ_G] φ_φ)
      simp only [hx, Finset.union_insert, Finset.mem_insert, eq_self_iff_true, Finset.mem_union
                  false_or, true_or, true_and]
      exact @iff_dni (formCL agents) _ _, }, }

----------------------------------------------------------
-- Subformulas in CLK
----------------------------------------------------------
inductive subformula {agents : Type} : formCL agents → formCL agents → Prop
| refl            {φ}     : subformula φ φ
| trans           {φ ψ χ} : subformula φ ψ → subformula ψ χ → subformula φ χ
| and_left        {φ ψ}   : subformula φ (φ _∧ ψ)
| and_right       {φ ψ}   : subformula ψ (φ _∧ ψ)
| imp_left        {φ ψ}   : subformula φ (φ _→ ψ)
| imp_right       {φ ψ}   : subformula ψ (φ _→ ψ)
| effectivity {G} {φ}     : subformula φ ('[G] φ)

----------------------------------------------------------
-- if φ is a subformula of ψ, then cl φ ⊆ cl ψ
----------------------------------------------------------
lemma subformula.cl_subset_and_left {agents : Type}
  {φ ψ : formCL agents} : cl φ ⊆ cl (φ _∧ ψ) := by
  intro x h
  induction φ
  repeat
  { simp only [cl, Finset.insert_union, Finset.union_insert, Finset.union_assoc, Finset.mem_insert
                Finset.mem_union, Finset.mem_singleton] at *
    repeat {cases h, simp only [h, eq_self_iff_true, and_self, false_or, true_or, or_true],}
    {simp only [h, eq_self_iff_true, and_self, true_or, false_or, or_true], }, }

lemma subformula.cl_subset_and_right {agents : Type} 
  {φ ψ : formCL agents} : cl ψ ⊆ cl (φ _∧ ψ) := by
  intro x h
  induction φ
  repeat
  { simp [cl] at *
    repeat {cases h, simp [h],}
    {simp [h], }, }

lemma subformula.cl_subset_imp_left {agents : Type}
  {φ ψ : formCL agents} : cl φ ⊆ cl (φ _→ ψ) := by
  intro x h
  induction φ
  repeat
  { simp [cl] at *
    repeat {cases h, simp [h],}
    {simp [h], }, }

lemma subformula.cl_subset_imp_right {agents : Type}
  {φ ψ : formCL agents} : cl ψ ⊆ cl (φ _→ ψ) := by
  intro x h
  induction φ
  repeat
  { simp [cl] at *
    repeat {cases h, simp [h],}
    {simp [h], }, }

lemma subformula.cl_subset_effectivity {agents : Type} 
  {φ : formCL agents} {G : Set (agents)} : cl φ ⊆ cl ('[G] φ) := by
  intro x h
  induction φ
  repeat
  { simp [cl] at *
    repeat {cases h, simp [h],}
    {simp [h], }, }

lemma subformula.cl_subset {agents : Type}
  {φ ψ : formCL agents} (h : subformula φ ψ) : cl φ ⊆ cl ψ := by
  induction h with _ _ _ _ _ h ih ih'
  { exact Finset.subset.rfl, }
  { exact Finset.subset.trans ih ih', }
  { exact subformula.cl_subset_and_left, }
  { exact subformula.cl_subset_and_right, }
  { exact subformula.cl_subset_imp_left, }
  { exact subformula.cl_subset_imp_right, }
  { exact subformula.cl_subset_effectivity, }

lemma subformula.mem_cl {agents : Type}
  {φ ψ : formCL agents} (h : subformula φ ψ) : φ ∈ cl ψ :=
h.cl_subset (cl_contains_phi φ)

lemma subformula.in_cl_sub {agents : Type}
  {φ ψ χ : formCL agents} (hcl : ψ ∈ cl φ) (hsub : subformula χ ψ) : χ ∈ cl φ := by
  induction hsub with _ _ _ _ hsub1 hsub2 hih1 hih2
  { exact hcl, }
  { exact hih1 (hih2 hcl), }
  all_goals
  { induction φ
    repeat 
    { simp only [cl, Finset.mem_insert, Finset.mem_singleton, or_self] at hcl
      cases hcl, }, }
  any_goals
  { simp only [cl, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, Finset.mem_image
                  exists_false, or_false, false_or] at hcl
      cases hcl, }
  repeat { apply or.elim hcl, all_goals { intro hcl, }, }
  any_goals { split_ifs at hcl, }
  any_goals { rw hcl.1 at *, rw hcl.2 at *, }
  any_goals { rw h at *, }
  any_goals { simp only [cl, Finset.union_assoc, Finset.mem_insert, Finset.mem_union
                          Finset.mem_singleton, false_or, Finset.mem_insert, Finset.mem_singleton
                          or_self, or_false, eq_self_iff_true, and_self, or_true, true_or] 
              at hcl, }
  repeat { apply or.elim hcl, all_goals { intro hcl, }, }
  any_goals { rw hcl.1 at *, rw hcl.2 at *, }
  any_goals { rw h at *, }
  any_goals { solve1 { by_contra, exact hcl, }, }
  any_goals { simp only [cl, φ_ih_φ hcl, Finset.mem_union, true_or, or_true], }
  any_goals { simp only [cl, φ_ih_ψ hcl, Finset.mem_union, true_or, or_true], }
  any_goals { simp only [cl, Finset.mem_union, cl_contains_phi, true_or, or_true], }
  any_goals { simp only [φ_ih hcl, true_or], }
  any_goals { simp only [if_true, Finset.mem_insert, Finset.mem_singleton, or_false
                          eq_self_iff_true, and_self, or_true, true_or], }
  any_goals { simp only [hcl.1, hcl.2, eq_self_iff_true, cl_contains_phi, and_self, or_false
                          or_true, true_or], }
  any_goals { simp only [h, if_false, Finset.mem_insert, eq_self_iff_true, and_self
                          Finset.mem_singleton, and_false, or_false, or_true], }
  any_goals { simp only [cl_contains_bot, or_self, true_or], }

namespace canonical
----------------------------------------------------------
-- Canonical Model CL
----------------------------------------------------------
@[simps] noncomputable def Mf_CL {agents : Type} [ha : Nonempty agents] 
  (φ : formCL agents) : modelCLtrue agents := 
{ f := 
  { states := S_f (canonical_model_CL agents (formCL agents) nprfalseCLtrue) cl φ
    hs := canonical.S_f.Nonempty _ _ _
    E := truly_playable_from_finite 
    { E          := E_f
      liveness   := Ef_liveness
      safety     := Ef_safety
      N_max      := Ef_nmax (cl_closed_single_neg φ)
      mono       := Ef_mono
      superadd   := Ef_superadd (cl_closed_single_neg φ), }, }
  v := λ  n, {s | (Pformula.var n) ∈ s.1.1}, }


/-- Allows us to write `φ ∈ s` instead of `φ ∈ s` -/
instance Mf_CL.f.states.set_like {agents : Type} [ha : Nonempty agents] 
  {φ : formCL agents} : set_like ((Mf_CL φ).f.states) (formCL agents) :=
{ coe := λ s, s.1.1
  coe_injective' := by
    unfold_coes
    intro sf tf h
    simp only [subtype.val_eq_coe, Finset.set_of_mem, Finset.coe_inj] at h
    apply subtype.coe_injective
    apply subtype.coe_injective
    exact h

----------------------------------------------------------
-- Truth Lemma 
----------------------------------------------------------

-- E
----------------------------------------------------------
-- Truth Lemma: case [G]ψ, where G = N :
lemma truth_E_univ {agents : Type} [ha : Nonempty agents]
  {φ ψ : formCL agents} {G : Set agents} (sf : (Mf_CL φ).f.states) 
  (hφ : ψ ∈ cl φ) (hφ' : ('[G] ψ) ∈ cl φ)
  (ih : ∀ tf, ((Mf_CL φ); tf _⊨ ψ) ↔ (ψ ∈ tf)) (hG : G = univ) :
  ((Mf_CL φ); sf _⊨ ('[G] ψ)) ↔ (('[G] ψ) ∈ sf) := by
  let MC' := canonical_model_CL agents (formCL agents) nprfalseCLtrue
      --  M f , sf ⊨ ψ
  calc ((Mf_CL φ); sf _⊨ ('[G]ψ))
      -- ↔ {sf ∈ Sf | M f , sf ⊨ ψ} ∈ Ef (sf )(N ), by definition ⊨
      ↔ {tf | (Mf_CL φ); tf _⊨ ψ} ∈ (Mf_CL φ).f.E.E sf G : 
          by unfold s_entails_CLtrue
      -- ↔ ∃t ∈ SC′, sf = tf and  ̃φ{sf ∈Sf |M f ,sf ⊨ψ} ∈ EC′(t)(N ), by definition Ef.
  ... ↔ ∃ t, (sf = s_f cl φ t) ∧ 
        tilde MC'.f.states (phi_X_set {sf | (Mf_CL φ); sf _⊨ ψ}) ∈ MC'.f.E.E t G : by
      dsimp [E_f, MC', hG, eq_self_iff_true, if_true] {eta := ff}
      simp only [hG, eq_self_iff_true, if_true] {eta := ff}
      -- ↔ ∃t ∈ SC′, sf = tf and  ̃φ{sf ∈Sf |ψ∈sf } ∈ EC′(t)(N ), by ih.
  ... ↔ ∃ t, (sf = s_f cl φ t) ∧ 
        tilde MC'.f.states (phi_X_set {sf : (Mf_CL φ).f.states | ψ ∈ sf}) ∈ MC'.f.E.E t univ :
    by simp only [ih, hG]
      -- ↔ ∃t ∈ SC′, sf = tf and  ̃ψ ∈ EC′(t)(N ), by Lemma 6.
  ... ↔ ∃ t, (sf = s_f cl φ t) ∧ tilde MC'.f.states ψ ∈ MC'.f.E.E t (univ) : by
        have hiff : _⊢ ((phi_X_set {sf : (Mf_CL φ).f.states | ψ ∈ sf}) _↔ ψ)
          from phi_X_contains_iff_psi (cl_closed_single_neg φ) (hφ)
        have htilde := @tilde_ax_iff _ (formCL agents) _ _ _ nprfalseCLtrue _ _ hiff
        rw htilde
  -- ↔ ∃t ∈ SC′, sf = tf and [N ] ψ ∈ t, by Lemma 7.
  ... ↔ ∃ t, (sf = s_f cl φ t) ∧ ('[univ] ψ) ∈ t : by
      simp only [E_s_contains_tilde_iff_E_in_s _ univ]
      exact iff.rfl
  -- ↔ [N] ψ ∈ sf:= left to right because [N] ψ ∈ tf, and from right to left when s = t.
  ... ↔ ('[G] ψ) ∈ sf :  by
        rw hG at *
        split
        { intro h
          obtain ⟨t, ⟨heq, h⟩⟩ := h
          exact (sf_eq_forall heq).mpr ⟨h, hφ'⟩, }
        { intro h
          obtain ⟨s, hs⟩ := s_f_to_s sf
          apply Exists.intro s
          exact ⟨sf_eq_s_f  @hs, (hs.mp h).left⟩, }

-- Truth Lemma: case [G]ψ, where G = N :
lemma truth_E_nuniv {agents : Type} [ha : Nonempty agents]
  {φ ψ : formCL agents} {G : Set agents} (sf : (Mf_CL φ).f.states) 
  (hφ : ψ ∈ cl φ) (hφ' : ('[G] ψ) ∈ cl φ)
  (ih : ∀ tf, ((Mf_CL φ); tf _⊨ ψ) ↔ (ψ ∈ tf)) (hG : G ≠ univ) :
  ((Mf_CL φ); sf _⊨ ('[G] ψ)) ↔ (('[G] ψ) ∈ sf) := by
  let MC' := canonical_model_CL agents (formCL agents) nprfalseCLtrue
      -- M f , sf ⊨ ψ
  calc ((Mf_CL φ); sf _⊨ ('[G]ψ))
      -- ↔ {sf ∈ Sf | M f , sf ⊨ ψ} ∈ Ef (sf )(G ), by definition ⊨
      ↔ {tf | (Mf_CL φ); tf _⊨ ψ} ∈ (Mf_CL φ).f.E.E sf G : 
          by unfold s_entails_CLtrue
      -- ↔ ∀t ∈ SC′, sf = tf and  ̃φ{sf ∈Sf |M f ,sf ⊨ψ} ∈ EC′(t)(G ), by definition Ef .
  ... ↔ ∀ t, (sf = s_f cl φ t) → 
          tilde MC'.f.states (phi_X_set {sf | (Mf_CL φ); sf _⊨ ψ}) ∈ MC'.f.E.E t G : by
        dsimp [E_f, MC']
        simp only [hG, if_false] {eta := ff}
      -- ↔ ∀t ∈ SC′, sf = tf ⇒  ̃φ{sf ∈Sf |ψ∈sf } ∈ EC′(t)(G ), by ih.
  ... ↔ ∀ t, (sf = s_f cl φ t) → 
          tilde MC'.f.states (phi_X_set {sf : (Mf_CL φ).f.states | ψ ∈ sf}) ∈ MC'.f.E.E t G :
      by simp only [ih]
      -- ↔ ∀t ∈ SC′, sf = tf ⇒  ̃ψ ∈ EC′(t)(G ), by Lemma 6.
  ... ↔ ∀ t, (sf = s_f cl φ t) →  tilde MC'.f.states ψ ∈ MC'.f.E.E t G :  by
        have hiff : _⊢ ((phi_X_set {sf : (Mf_CL φ).f.states | ψ ∈ sf}) _↔ ψ)
          from phi_X_contains_iff_psi (cl_closed_single_neg φ) (hφ)
        have htilde := @tilde_ax_iff _ (formCL agents) _ _ _ nprfalseCLtrue _ _ hiff
        rw htilde
      -- ↔ ∀t ∈ SC′, sf = tf ⇒ [G ]ψ ∈ t, by Lemma 7.
  ... ↔ ∀ t, (sf = s_f cl φ t) → ('[G] ψ) ∈ t : by
      simp only [E_s_contains_tilde_iff_E_in_s _ G]
      exact iff.rfl
    -- ↔ [G] ψ ∈ sf := left to right when s = t:= right to left because [G]ψ ∈ sf = tf 
  ... ↔ (('[G] ψ) ∈ sf) :  by
        split
        { intro h
          obtain ⟨s, hs⟩ := s_f_to_s sf
          specialize h s (eq.symm (s_f_eq_sf @hs))
          apply hs.mpr
          exact ⟨h, hφ'⟩, }
        { intro h t ht
          exact ((sf_eq_forall ht).mp h).1, }

-- Truth Lemma
----------------------------------------------------------
lemma truth_lemma_CLK {agents : Type} [ha : Nonempty agents]
  (φ ψ : formCL agents) (sf : (Mf_CL φ).f.states) (hφ : ψ ∈ cl φ) :
  ((Mf_CL φ); sf _⊨ ψ) ↔ (ψ ∈ sf) := by
  -- This proof is by induction on φ.
  induction' ψ fixing ha ψ with n ψ χ _ _ ψ χ _ _, -- sf needs to vary for the modal operators
  all_goals
  { obtain ⟨s, hs⟩ := s_f_to_s sf, }

  { -- case bot
    simp [s_entails_CLtrue, explosion]
    apply s_f_n_contains
    exact @hs
    apply or.intro_left
    exact @bot_not_mem_of_ax_consistent (formCL agents) _ s.1 s.2.1, }

  { -- case var
    simpa [s_entails_CLtrue], }

  { -- case and
    have hψ := subformula.in_cl_sub hφ subformula.and_left
    have hχ := subformula.in_cl_sub hφ subformula.and_right
    specialize ih_ψ _ sf hψ
    specialize ih_χ _ sf hχ
    unfold s_entails_CLtrue at *
    rw [ih_ψ, ih_χ, hs, hs, hs]
    simp only [hφ, hψ, hχ, and_true]
    split
    { rintro ⟨hψs, hχs⟩
      apply max_ax_contains_by_set_proof_2h s.2 hψs hχs axCL.Prop4 }
    { intro hψχs
      split
      { apply max_ax_contains_by_set_proof s.2 hψχs axCL.Prop5 }
      { apply max_ax_contains_by_set_proof s.2 hψχs axCL.Prop6 } } }

  { -- case imp
    have hψ := subformula.in_cl_sub hφ subformula.imp_left
    have hχ := subformula.in_cl_sub hφ subformula.imp_right
    specialize ih_ψ _ sf hψ
    specialize ih_χ _ sf hχ
    unfold s_entails_CLtrue at *
    rw [ih_ψ, ih_χ, hs, hs, hs]
    simp only [hφ, hψ, hχ, and_true]
    split
    { intro h
      exact max_ax_contains_imp_by_proof s.2 h, }
    { intro h hφ
      apply max_ax_contains_by_set_proof_2h s.2 hφ h likemp, }, }

  { -- case [G] ψ
    have hψ := subformula.in_cl_sub hφ subformula.effectivity
    let ih := λ sf, ih _ sf hψ
    cases em (G = univ) with hG hG
    { exact truth_E_univ _ hψ hφ ih hG,}
    { exact truth_E_nuniv _ hψ hφ ih hG, }, }

----------------------------------------------------------
-- Completeness
----------------------------------------------------------

-- Completeness
----------------------------------------------------------
theorem completenessCLK {agents : Type} [ha : Nonempty agents] 
  (φ : formCL agents) : (_⊨ φ) → _⊢ φ := by
  -- rw from contrapositive
  rw ←not_imp_not
  -- assume ¬ ⊢ φ
  intro hnax
  -- from ¬ ⊢ φ, have that {¬ φ} is a consistent Set
  obtain ⟨s', hmax, hnφ⟩ := @exists_max_ax_consistent_neg_mem (formCL agents) _ _ hnax
  -- show that φ is not globally valid
  -- by showing that there exists some model where φ is not valid.
  simp[global_valid]
  -- let that model be the canonical model
  apply Exists.intro (Mf_CL φ)
  -- in the canonical model (M) there exists some state (s) where ¬ M s ⊨ φ
  simp[valid_m]
  obtain ⟨s, hs⟩ : 
    ∃ s : (canonical_model_CL agents (formCL agents) nprfalseCLtrue).f.states, s = ⟨s', hmax⟩
    from exists_apply_eq_apply _ _
  obtain ⟨sf, hsf⟩ := s_to_s_f cl φ s
  apply Exists.intro sf
  -- assume by contradiction that M s ⊨ φ
  intro hf
  -- by the truth lemma φ ∈ s
  have hφ:= (truth_lemma_CLK φ _ sf (cl_contains_phi φ)).mp hf
  -- in that state (s), φ ∈ s, so we do not have ¬ φ ∈ s (by consistency)
  -- contradiction with hnφ
  rw hsf at hφ
  apply contra_contains_pr_false s.2 hφ.left
  rw hs
  exact hnφ
end

end canonical
