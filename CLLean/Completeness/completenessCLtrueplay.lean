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
import CLLean.Semantics.model
import CLLean.Semantics.playability
import Mathlib.Tactic


open Classical formCL Set axCL

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
def s_entails_CLtrue {agents : Type} (m : modelCLtrue agents) (s : m.f.states) :
  formCL agents → Prop
  | bot      => false
  | (var n)  => s ∈ m.v n
  | (φ _→ ψ) => (s_entails_CLtrue m s φ) → (s_entails_CLtrue m s ψ)
  | (φ _∧ ψ) => (s_entails_CLtrue m s φ) ∧ (s_entails_CLtrue m s ψ)
  | (_[G] φ) => {t : m.f.states | s_entails_CLtrue m t φ} ∈ m.f.E.E (s) (G)

notation m ";" s "_⊨" φ => s_entails_CLtrue m s φ

----------------------------------------------------------
-- Validity
----------------------------------------------------------

-- φ is valid in a model M = (f,v), if it is entailed by every state of the model
def valid_m {agents: Type} (m : modelCLtrue agents) (φ : formCL agents) :=
  ∀ s : m.f.states, m; s _⊨ φ

notation m "_⊨" φ => valid_m m  φ

-- φ is globally valid, if it is valid in all models
def global_valid {agents: Type} (φ : formCL agents) :=
  ∀ m, valid_m m φ

notation "_⊨" φ => global_valid φ

----------------------------------------------------------
-- Soundness
----------------------------------------------------------

theorem soundnessCLtrue {agents : Type} (φ : formCL agents) : _⊢ φ → _⊨ φ := by
  intro h
  induction h
  -- case Prop1
  · intro m s h1 _
    exact h1
  -- case Prop2
  · intro m s h1 h2 h3
    apply h1
    · exact h3
    · apply h2
      exact h3
  -- case Prop3
  · intro m s h1 h2
    by_contra hf
    simp only [s_entails_CLtrue, imp_false] at *
    exact (h1 hf) (h2 hf)
  -- case Prop4
  · intro m s h1 h2
    simp only [s_entails_CLtrue] at *
    exact And.intro h1 h2
  -- case Prop5
  · intro m s h1
    exact h1.left
  -- case Prop6
  · intro m s h1
    exact h1.right
  -- case Prop7
  · intro m s h1 h2
    by_contra hf
    simp only [s_entails_CLtrue, imp_false] at *
    exact h1 hf h2
  -- case ⊥
  · intro m s h1
    simp only [s_entails_CLtrue, setOf_false] at *
    exact m.f.E.liveness s _ h1
  -- case ⊤
  · intro m s
    simp only [s_entails_CLtrue, IsEmpty.forall_iff, setOf_true]
    exact m.f.E.safety s _
  -- case N
  · intro m s h1
    apply m.f.E.N_max
    by_contra h
    simp only [s_entails_CLtrue, imp_false] at *
    exact h1 h
  -- case M
  · intro m s
    apply m.f.E.mono s _ _ { t | (s_entails_CLtrue m t _) }
    intro t h1
    exact h1.left
  -- case S
  · intro m s h1
    exact m.f.E.superadd s _ _ _ _ h1.left h1.right (by assumption)
  -- case MP
  case MP _ hImp ih =>
    intro m s
    apply hImp
    exact ih m s
  -- case Eq
  case Eq ih =>
    intro m s
    have heq : {t | (s_entails_CLtrue  m t _) } = {t | (s_entails_CLtrue m t _) }:= by
        apply Set.ext
        intro u
        apply Iff.intro
        · intro hu
          exact (ih m u).left hu
        · intro hu
          exact (ih m u).right hu
    apply And.intro
    · intro h1
      simp only [s_entails_CLtrue, ←heq] at *
      exact h1
    · intro h1
      simp only [s_entails_CLtrue, heq] at *
      exact h1

----------------------------------------------------------
-- CL does not prove ⊥
----------------------------------------------------------

def m_ex_CLtrue {agents : Type} : modelCLtrue agents  :=
{ f :=
  { states := single
    hs := single_nonempty
    E  :=  truly_playable_from_finite e_ex }
  v := λ _ => {} }

lemma nprfalseCLtrue {agents : Type} : ¬ (_⊢ (_⊥ : formCL agents)) := by
  -- prove with the contrapositive of soundness : ¬ ⊨ ⊥
  apply (mt (soundnessCLtrue (@formCL.bot agents)))
  -- assume by contradiction : ⊨ ⊥
  intro hf
  -- ⊨ ⊥ only holds if no model with states exists
  simp[global_valid, valid_m, s_entails_CLtrue] at hf
  -- we create an example model with a single state to prove a contradiction
  exact hf (m_ex_CLtrue) single.one


----------------------------------------------------------
-- Filtration closure cl
----------------------------------------------------------
noncomputable def cl {agents : Type} [Fintype agents] :
  formCL agents → Finset (formCL agents)
|  _⊥              => {_⊥, _¬ _⊥}
| (var n)          => {var n, _¬ (var n), _⊥, _¬ _⊥}
| (φ _→ ψ)         => cl φ ∪ cl ψ ∪ (ite (ψ = _⊥) {(φ _→ _⊥)} {(φ _→ ψ), _¬ (φ _→ ψ)})
| (φ _∧ ψ)         => cl φ ∪ cl ψ ∪ {(φ _∧ ψ), _¬ (φ _∧ ψ)}
| (_[G] φ)         => cl φ ∪ {(_[G] φ), _¬ _[G] φ}

----------------------------------------------------------
-- Lemmas about cl
----------------------------------------------------------
@[simp] lemma cl_contains_phi {agents : Type} [hN : Fintype agents] (φ : formCL agents) :
  φ ∈ cl φ := by
  cases' φ
  any_goals
    simp_all only [cl, Finset.union_insert, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_false,
    eq_self_iff_true, and_self, or_true, true_or, Finset.mem_union, Finset.union_assoc]
  · unfold cl
    simp only [Finset.mem_singleton, imp.injEq, Finset.union_assoc, Finset.mem_union]
    split_ifs with h
    simp only [Finset.mem_singleton, imp.injEq, h, and_false, Finset.mem_insert,
      or_false, or_true]
    simp only [Finset.mem_singleton, imp.injEq, Finset.mem_insert, true_or, or_true]

@[simp] lemma cl_contains_bot {agents : Type} [hN : Fintype agents] (φ : formCL agents) :
  _⊥ ∈ cl φ := by
  induction' φ with _ _ _ ih_φ ih_ψ _ _ ih_φ ih_ψ _ _ ih _ _ ih _ _ ih
  any_goals simp [cl]
  any_goals simp [ih]
  any_goals simp [ih_φ, ih_ψ]

lemma cl_closed_single_neg {agents : Type} [hN : Fintype agents]
  (φ x : formCL agents) (hx : x ∈ cl φ) :
  ∃ ψ, (ψ ∈ cl φ ∧ _⊢ (ψ _↔ (_¬ x))) := by
  induction' φ with n φ ψ ih_φ ih_ψ φ ψ ih_φ ih_ψ G φ ih i φ ih G φ ih
  all_goals try
    unfold cl at hx ⊢
    simp only [Finset.union_insert, Finset.insert_union, Finset.union_assoc, Finset.mem_insert,
                Finset.mem_union, Finset.mem_singleton] at hx
    cases' hx with hx hx
    apply Exists.intro (_¬ x)
    simp only [hx, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, eq_self_iff_true
                false_or, true_or, or_true, true_and] at *
    apply @iff_iden (formCL agents) _ _

  · apply Exists.intro (_⊥)
    simp only [hx, Finset.mem_insert, eq_self_iff_true, Finset.mem_singleton, or_false, true_and]
    apply MP
    apply MP
    apply Prop4
    exact @dni (formCL agents) _ _
    exact @nnn_bot (formCL agents) _
  · cases' hx with hx hx
    · apply Exists.intro (var n)
      simp only [hx, Finset.mem_insert, eq_self_iff_true, Finset.mem_singleton,
                  or_false, true_and] at *
      exact @iff_dni (formCL agents) _ _
    cases' hx with hx hx
    · apply Exists.intro (_⊤)
      simp only [Finset.mem_singleton, Finset.mem_insert, imp.injEq, and_true, or_self, or_true, hx,
        true_and]
      apply @iff_iden (formCL agents) _ _
    · apply Exists.intro (_⊥)
      simp only [hx, Finset.mem_insert, eq_self_iff_true, Finset.mem_singleton, or_false,
                  false_or, true_and]
      apply MP
      apply MP
      apply Prop4
      exact @dni (formCL agents) _ _
      exact @nnn_bot (formCL agents) _
  · cases' hx with hx hx
    · specialize ih_φ hx
      cases' ih_φ with ψ hψ
      apply Exists.intro ψ
      apply And.intro
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact hψ.1
      exact hψ.2
    cases' hx with hx hx
    · specialize ih_ψ hx
      cases' ih_ψ with ψ hψ
      apply Exists.intro ψ
      apply And.intro
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact hψ.1
      exact hψ.2
    · apply Exists.intro (φ _∧ ψ)
      simp only [Finset.mem_singleton, Finset.union_insert, Finset.union_assoc, Finset.mem_union,
        or_false, Finset.mem_insert, true_or, hx, true_and]
      exact @iff_dni (formCL agents) _ _
  · unfold cl at hx ⊢
    simp only [Finset.union_assoc, Finset.mem_union] at hx
    cases' hx with hx hx
    · specialize ih_φ hx
      cases' ih_φ with ψ hψ
      apply Exists.intro ψ
      apply And.intro
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact hψ.1
      exact hψ.2
    cases' hx with hx hx
    · specialize ih_ψ hx
      cases' ih_ψ with ψ hψ
      apply Exists.intro ψ
      apply And.intro
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact hψ.1
      exact hψ.2
    · split_ifs at hx with h
      · simp only [h, eq_self_iff_true, if_true, Finset.union_assoc, Finset.mem_union,
                    Finset.mem_singleton] at *
        simp only [hx]
        apply Exists.intro (φ)
        apply And.intro
        apply Or.intro_left
        exact cl_contains_phi φ
        exact @iff_dni (formCL agents) _ _
      · simp only [h, if_false, Finset.union_insert, Finset.union_assoc, Finset.mem_insert,
                    Finset.mem_union, Finset.mem_singleton, not_false_iff] at *
        cases' hx with hx hx
        · apply Exists.intro (_¬ (φ _→ ψ))
          simp only [hx, eq_self_iff_true, or_true, true_and]
          exact @iff_iden (formCL agents) _ _
        · apply Exists.intro (φ _→ ψ)
          simp only [hx, eq_self_iff_true, true_or, true_and]
          exact @iff_dni (formCL agents) _ _
  · cases' hx with hx hx
    · specialize ih hx
      cases' ih with ψ hψ
      apply Exists.intro ψ
      apply And.intro
      apply Finset.mem_union_left
      exact hψ.1
      exact hψ.2
    · apply Exists.intro (_[G] φ)
      simp only [hx, Finset.union_insert, Finset.mem_insert, eq_self_iff_true, Finset.mem_union,
                  false_or, true_or, true_and]
      exact @iff_dni (formCL agents) _ _

----------------------------------------------------------
-- Subformulas in CLtrue
----------------------------------------------------------
inductive subformula {agents : Type} : formCL agents → formCL agents → Prop
| refl            {φ}     : subformula φ φ
| trans           {φ ψ χ} : subformula φ ψ → subformula ψ χ → subformula φ χ
| and_left        {φ ψ}   : subformula φ (φ _∧ ψ)
| and_right       {φ ψ}   : subformula ψ (φ _∧ ψ)
| imp_left        {φ ψ}   : subformula φ (φ _→ ψ)
| imp_right       {φ ψ}   : subformula ψ (φ _→ ψ)
| effectivity {G} {φ}     : subformula φ (_[G] φ)

----------------------------------------------------------
-- if φ is a subformula of ψ, then cl φ ⊆ cl ψ
----------------------------------------------------------
lemma subformula.cl_subset_and_left {agents : Type} [hN : Fintype agents]
  {φ ψ : formCL agents} : cl φ ⊆ cl (φ _∧ ψ) := by
  intro x h
  induction φ
  repeat
    simp only [cl, Finset.insert_union, Finset.union_insert, Finset.union_assoc, Finset.mem_insert,
                Finset.mem_union, Finset.mem_singleton] at *
    repeat
      cases' h with h h
      simp only [h, eq_self_iff_true, and_self, false_or, true_or, or_true]
    simp only [h, eq_self_iff_true, and_self, true_or, false_or, or_true]

lemma subformula.cl_subset_and_right {agents : Type} [hN : Fintype agents]
  {φ ψ : formCL agents} : cl ψ ⊆ cl (φ _∧ ψ) := by
  intro x h
  induction φ
  all_goals
    · simp_all [cl]

lemma subformula.cl_subset_imp_left {agents : Type} [hN : Fintype agents]
  {φ ψ : formCL agents} : cl φ ⊆ cl (φ _→ ψ) := by
  intro x h
  induction φ
  all_goals
    simp_all [cl]
    repeat
      cases' h with h h
      simp [h]
    simp [h]

lemma subformula.cl_subset_imp_right {agents : Type} [hN : Fintype agents]
  {φ ψ : formCL agents} : cl ψ ⊆ cl (φ _→ ψ) := by
  intro x h
  induction φ
  all_goals
  · simp [cl] at *
    repeat
      cases h
    simp [h]


lemma subformula.cl_subset_effectivity {agents : Type} [hN : Fintype agents]
  {φ : formCL agents} {G : Set (agents)} : cl φ ⊆ cl (_[G] φ) := by
  intro x h
  induction φ
  repeat
  · simp [cl] at *
    repeat
      cases' h with h h
      simp [h]
    simp [h]

lemma subformula.cl_subset {agents : Type} [hN : Fintype agents]
  {φ ψ : formCL agents} (h : subformula φ ψ) : cl φ ⊆ cl ψ := by
  induction' h with _ _ _ _ _ _ ih ih'
  · exact Finset.Subset.refl _
  · exact Finset.Subset.trans ih ih'
  · exact subformula.cl_subset_and_left
  · exact subformula.cl_subset_and_right
  · exact subformula.cl_subset_imp_left
  · exact subformula.cl_subset_imp_right
  · exact subformula.cl_subset_effectivity

lemma subformula.mem_cl {agents : Type} [Fintype agents]
  {φ ψ : formCL agents} (h : subformula φ ψ) : φ ∈ cl ψ :=
h.cl_subset (cl_contains_phi φ)

lemma subformula.in_cl_sub {agents : Type} [hN : Fintype agents]
  {φ ψ χ : formCL agents} (hcl : ψ ∈ cl φ) (hsub : subformula χ ψ) : χ ∈ cl φ := by
  induction' hsub with _ _ _ _ hsub1 hsub2 hih1 hih2
  · exact hcl
  · exact hih1 (hih2 hcl)
  all_goals
    induction' φ with n φ ψ ih_φ ih_ψ φ ψ ih_φ ih_ψ G φ ih i φ ih
    all_goals
      try unfold cl at hcl
      try unfold cl
    repeat
      simp only [cl, Finset.mem_insert, Finset.mem_singleton, or_self] at hcl
      cases' hcl with hcl
  all_goals
    try simp only [Finset.mem_singleton, Finset.union_insert, Finset.union_assoc, Finset.mem_union,
      or_false, Finset.mem_insert, and.injEq] at hcl
    try cases' hcl with hcl hcl
    try rw [hcl.1] at *
    try rw [hcl.2] at *
    try rw [hcl]
  any_goals
    simp only [Finset.mem_union, Finset.mem_image, exists_false, or_self, or_false, cl,
      Finset.union_assoc, false_or, Finset.mem_insert, Finset.mem_singleton, or_self, or_false,
      eq_self_iff_true, and_self, or_true, true_or] at hcl
  any_goals
    simp only [Finset.mem_singleton, Finset.union_insert, Finset.union_assoc, Finset.mem_union,
      or_false, Finset.mem_insert, cl_contains_phi, true_or, or_true]
  repeat
    all_goals
      try cases' hcl with hcl hcl
      try split_ifs with h1
      try split_ifs at hcl with h3
      try simp only [ih_φ hcl]
      try simp only[ih_ψ hcl]
      try simp only [ih hcl]
    any_goals
      · simp only [true_or, or_true]
  any_goals
    rename_i _ _ _ h
    by_contra
    exact List.ne_nil_of_mem h (by rfl)
  any_goals
    simp only [cl, Finset.mem_union, Finset.mem_singleton, imp.injEq, cl_contains_phi,
      cl_contains_bot, if_true, Finset.mem_insert, Finset.mem_singleton, or_false,  or_self,
      eq_self_iff_true, and_self, true_or, or_true] at *
  all_goals
    try cases' hcl with hcl hcl
    try simp_all only [hcl.1, true_or, or_true]
    try simp_all only [hcl.2, true_or, or_true]
  · rename_i h
    simp only [h, true_or, or_true]
  any_goals
    simp_all only [cl_contains_phi, cl_contains_bot, implies_true, not_false_eq_true, and_self,
      mem_toFinset, false_or, Finset.mem_union, Finset.mem_image, and_true,
      exists_eq_right, and_false, exists_false, or_false, or_true, true_or, or_self]


namespace canonical
----------------------------------------------------------
-- Canonical Model CL
----------------------------------------------------------
noncomputable def filtered_E {agents : Type} [Nonempty agents] [Fintype agents]
  (φ : formCL agents) :
  playable_effectivity_struct agents
  (S_f (canonical_model_CL agents (formCL agents) nprfalseCLtrue) cl φ) :=
{ E          := E_f
  liveness   := Ef_liveness
  safety     := Ef_safety
  N_max      := Ef_nmax (cl_closed_single_neg φ)
  mono       := Ef_mono
  superadd   := Ef_superadd (cl_closed_single_neg φ) }

@[simps!] noncomputable def Mf_CLtrue {agents : Type}  [Nonempty agents] [Fintype agents]
  (φ : formCL agents) :
  modelCLtrue agents :=
{ f :=
  { states := S_f (canonical_model_CL agents (formCL agents) nprfalseCLtrue) cl φ
    hs := canonical.S_f.Nonempty _ _ _
    E := truly_playable_from_finite (filtered_E φ)}
  v := λ  n => {s | (formCL.var n) ∈ s.1.1} }

/-- Allows us to write `φ ∈ s` instead of `φ ∈ s` -/
instance Mf_CLtrue.f.states.SetLike {agents : Type} [ha : Nonempty agents] [hN : Fintype agents]
  {φ : formCL agents} : SetLike ((Mf_CLtrue φ).f.states) (formCL agents) :=
{ coe := λ s => s.1.1
  coe_injective' := by
    intro sf tf h
    simp only [Finset.setOf_mem, Finset.coe_inj, s_f_eq] at h
    exact h }

----------------------------------------------------------
-- Truth Lemma
----------------------------------------------------------

-- E
----------------------------------------------------------
-- Truth Lemma: case [G]ψ, where G = N :
lemma truth_E_univ {agents : Type} [ha : Nonempty agents] [hN : Fintype agents]
  {φ ψ : formCL agents} {G : Set agents} (sf : (Mf_CLtrue φ).f.states)
  (hφ : ψ ∈ cl φ) (hφ' : (_[G] ψ) ∈ cl φ)
  (ih : ∀ tf, (s_entails_CLtrue (Mf_CLtrue φ) tf ψ) ↔ (ψ ∈ tf)) (hG : G = univ) :
  (s_entails_CLtrue (Mf_CLtrue φ) sf (_[G] ψ)) ↔ ((_[G] ψ) ∈ sf) := by
  let MC' := canonical_model_CL agents (formCL agents) nprfalseCLtrue
  --  M f , sf ⊨ ψ
  calc
    (s_entails_CLtrue (Mf_CLtrue φ) sf (_[G]ψ))
    -- ↔ {sf ∈ Sf | M f , sf ⊨ ψ} ∈ Ef (sf )(N ), by definition ⊨
    ↔ {tf | s_entails_CLtrue (Mf_CLtrue φ) tf ψ} ∈ (Mf_CLtrue φ).f.E.E sf G := by
        simp only [s_entails_CLtrue]
    -- ↔ ∃t ∈ SC′, sf = tf and  ̃φ{sf ∈Sf |M f ,sf ⊨ψ} ∈ EC′(t)(N ), by definition Ef.
    _ ↔ ∃ t, (sf = s_f cl φ t) ∧
          tilde MC'.f.states (phi_X_set {sf | s_entails_CLtrue (Mf_CLtrue φ) sf ψ}) ∈ MC'.f.E.E t G := by
        -- simp? [hG, E_f]
        simp only [Mf_CLtrue_f_states, hG, Mf_CLtrue_f_E_E, E_f, ite_true, mem_setOf_eq]
    -- ↔ ∃t ∈ SC′, sf = tf and  ̃φ{sf ∈Sf |ψ∈sf } ∈ EC′(t)(N ), by ih.
    _ ↔ ∃ t, (sf = s_f cl φ t) ∧ tilde MC'.f.states
          (phi_X_set {sf : (Mf_CLtrue φ).f.states | ψ ∈ sf}) ∈ MC'.f.E.E t univ := by
        simp only [Mf_CLtrue_f_states, ih, mem_mk, Finset.setOf_mem, hG]
        -- ↔ ∃t ∈ SC′, sf = tf and  ̃ψ ∈ EC′(t)(N ), by Lemma 6.
    _ ↔ ∃ t, (sf = s_f cl φ t) ∧ tilde MC'.f.states ψ ∈ MC'.f.E.E t (univ) := by
        have hiff : _⊢ ((phi_X_set {sf : (Mf_CLtrue φ).f.states | ψ ∈ sf}) _↔ ψ) :=
          phi_X_contains_iff_psi (cl_closed_single_neg φ) (hφ)
        have htilde := @tilde_ax_iff _ (formCL agents) _ _ _ nprfalseCLtrue _ _ hiff
        rw [htilde]
    -- ↔ ∃t ∈ SC′, sf = tf and [N ] ψ ∈ t, by Lemma 7.
    _ ↔ ∃ t, (sf = s_f cl φ t) ∧ (_[univ] ψ) ∈ t := by
        simp only [Mf_CLtrue_f_states, E_s_contains_tilde_iff_E_in_s _ univ]
        exact Iff.rfl
    -- ↔ [N] ψ ∈ sf:= left to right because [N] ψ ∈ tf, and from right to left when s = t.
    _ ↔ (_[G] ψ) ∈ sf := by
        rw [hG] at hφ' ⊢
        apply Iff.intro
        · intro h
          obtain ⟨t, ⟨heq, h⟩⟩ := h
          exact (sf_eq_forall heq).mpr ⟨h, hφ'⟩
        · intro h
          obtain ⟨s, hs⟩ := s_f_to_s sf
          apply Exists.intro s
          exact ⟨sf_eq_s_f  @hs, (hs.mp h).left⟩

-- Truth Lemma: case [G]ψ, where G = N :
lemma truth_E_nuniv {agents : Type} [ha : Nonempty agents] [hN : Fintype agents]
  {φ ψ : formCL agents} {G : Set agents} (sf : (Mf_CLtrue φ).f.states)
  (hφ : ψ ∈ cl φ) (hφ' : (_[G] ψ) ∈ cl φ)
  (ih : ∀ tf, (s_entails_CLtrue (Mf_CLtrue φ) tf ψ) ↔ (ψ ∈ tf)) (hG : G ≠ univ) :
  (s_entails_CLtrue (Mf_CLtrue φ) sf (_[G] ψ)) ↔ ((_[G] ψ) ∈ sf) := by
  let MC' := canonical_model_CL agents (formCL agents) nprfalseCLtrue
  -- M f , sf ⊨ ψ
  calc
    (s_entails_CLtrue (Mf_CLtrue φ) sf (_[G]ψ))
    -- ↔ {sf ∈ Sf | M f , sf ⊨ ψ} ∈ Ef (sf )(G ), by definition ⊨
    ↔ {tf | s_entails_CLtrue (Mf_CLtrue φ) tf ψ} ∈ (Mf_CLtrue φ).f.E.E sf G := by
        simp only [s_entails_CLtrue, Mf_CLtrue_f_states, Mf_CLtrue_f_E_E]
    -- ↔ ∀t ∈ SC′, sf = tf and  ̃φ{sf ∈Sf |M f ,sf ⊨ψ} ∈ EC′(t)(G ), by definition Ef .
    _ ↔ ∀ t, (sf = s_f cl φ t) →
          tilde MC'.f.states (phi_X_set {sf | s_entails_CLtrue (Mf_CLtrue φ) sf ψ}) ∈ MC'.f.E.E t G := by
        simp only [Mf_CLtrue_f_states, Mf_CLtrue_f_E_E, E_f, hG, ite_false, mem_setOf_eq]
        -- simp only [hG, if_false]
    -- ↔ ∀t ∈ SC′, sf = tf ⇒  ̃φ{sf ∈Sf |ψ∈sf } ∈ EC′(t)(G ), by ih.
    _ ↔ ∀ t, (sf = s_f cl φ t) →
          tilde MC'.f.states (phi_X_set {sf : (Mf_CLtrue φ).f.states | ψ ∈ sf}) ∈ MC'.f.E.E t G := by
        simp only [Mf_CLtrue_f_states, ih, mem_mk, Finset.setOf_mem]
    -- ↔ ∀t ∈ SC′, sf = tf ⇒  ̃ψ ∈ EC′(t)(G ), by Lemma 6.
    _ ↔ ∀ t, (sf = s_f cl φ t) →  tilde MC'.f.states ψ ∈ MC'.f.E.E t G := by
        have hiff : _⊢ ((phi_X_set {sf : (Mf_CLtrue φ).f.states | ψ ∈ sf}) _↔ ψ) :=
           phi_X_contains_iff_psi (cl_closed_single_neg φ) (hφ)
        have htilde := @tilde_ax_iff _ (formCL agents) _ _ _ nprfalseCLtrue _ _ hiff
        rw [htilde]
    -- ↔ ∀t ∈ SC′, sf = tf ⇒ [G ]ψ ∈ t, by Lemma 7.
    _ ↔ ∀ t, (sf = s_f cl φ t) → (_[G] ψ) ∈ t := by
        simp only [E_s_contains_tilde_iff_E_in_s _ G]
        exact Iff.rfl
    -- ↔ [G] ψ ∈ sf := left to right when s = t:= right to left because [G]ψ ∈ sf = tf
    _ ↔ ((_[G] ψ) ∈ sf) := by
        apply Iff.intro
        · intro h
          obtain ⟨s, hs⟩ := s_f_to_s sf
          specialize h s (Eq.symm (s_f_eq_sf @hs))
          apply hs.mpr
          exact ⟨h, hφ'⟩
        · intro h t ht
          exact ((sf_eq_forall ht).mp h).1

-- Truth Lemma
----------------------------------------------------------
lemma truth_lemma_CLtrue {agents : Type} [ha : Nonempty agents] [hN : Fintype agents]
  (φ ψ : formCL agents) (sf : (Mf_CLtrue φ).f.states) (hφ : ψ ∈ cl φ) :
  (s_entails_CLtrue (Mf_CLtrue φ) sf ψ) ↔ (ψ ∈ sf) := by
  -- This proof is by induction on φ.
  induction' ψ with n ψ χ ih_ψ ih_χ ψ χ ih_ψ ih_χ G ψ ih generalizing sf φ -- sf needs to vary for the modal operators
  all_goals
    obtain ⟨s, hs⟩ := s_f_to_s sf

  · -- case bot
    simp [s_entails_CLtrue, explosion]
    apply s_f_n_contains
    exact @hs
    apply Or.intro_left
    exact @bot_not_mem_of_ax_consistent (formCL agents) _ s.1 s.2.1

  · -- case var
    simp_all only [mem_mk, Finset.setOf_mem, s_entails_CLtrue, Mf_CLtrue_f_states, Mf_CLtrue_v, mem_setOf_eq,
      and_true]

  · -- case and
    have hψ := subformula.in_cl_sub hφ subformula.and_left
    have hχ := subformula.in_cl_sub hφ subformula.and_right
    specialize ih_ψ _ sf hψ
    specialize ih_χ _ sf hχ
    unfold s_entails_CLtrue
    rw [ih_ψ, ih_χ, hs, hs, hs]
    simp only [hφ, hψ, hχ, and_true]
    apply Iff.intro
    · rintro ⟨hψs, hχs⟩
      apply max_ax_contains_by_set_proof_2h s.2 hψs hχs axCL.Prop4
    · intro hψχs
      apply And.intro
      · apply max_ax_contains_by_set_proof s.2 hψχs axCL.Prop5
      · apply max_ax_contains_by_set_proof s.2 hψχs axCL.Prop6

  · -- case imp
    have hψ := subformula.in_cl_sub hφ subformula.imp_left
    have hχ := subformula.in_cl_sub hφ subformula.imp_right
    specialize ih_ψ _ sf hψ
    specialize ih_χ _ sf hχ
    unfold s_entails_CLtrue
    rw [ih_ψ, ih_χ, hs, hs, hs]
    simp only [hφ, hψ, hχ, and_true]
    apply Iff.intro
    · intro h
      exact max_ax_contains_imp_by_proof s.2 h
    · intro h hφ
      apply max_ax_contains_by_set_proof_2h s.2 hφ h likemp

  · -- case [G] ψ
    have hψ := subformula.in_cl_sub hφ subformula.effectivity
    let ih := λ sf => ih _ sf hψ
    cases' Classical.em (G = univ) with hG hG
    · exact truth_E_univ _ hψ hφ ih hG
    · exact truth_E_nuniv _ hψ hφ ih hG

----------------------------------------------------------
-- Completeness
----------------------------------------------------------

-- Completeness
----------------------------------------------------------
theorem completenessCLtrue {agents : Type} [ha : Nonempty agents] [hN : Fintype agents]
  (φ : formCL agents) : (_⊨ φ) → _⊢ φ := by
  -- rw from contrapositive
  rw [←not_imp_not]
  -- assume ¬ ⊢ φ
  intro hnax
  -- from ¬ ⊢ φ, have that {¬ φ} is a consistent Set
  obtain ⟨s', hmax, hnφ⟩ := @exists_max_ax_consistent_neg_mem (formCL agents) _ _ hnax
  -- show that φ is not globally valid
  -- by showing that there exists some model where φ is not valid.
  simp[global_valid]
  -- let that model be the canonical model
  apply Exists.intro (Mf_CLtrue φ)
  -- in the canonical model (M) there exists some state (s) where ¬ M s ⊨ φ
  simp[valid_m]
  obtain ⟨s, hs⟩ :
    ∃ s : (canonical_model_CL agents (formCL agents) nprfalseCLtrue).f.states, s = ⟨s', hmax⟩ :=
      exists_apply_eq_apply _ _
  obtain ⟨sf, hsf⟩ := s_to_s_f cl φ s
  apply Exists.intro sf
  -- assume by contradiction that M s ⊨ φ
  intro hf
  -- by the truth lemma φ ∈ s
  have hφ:= (truth_lemma_CLtrue φ _ sf (cl_contains_phi φ)).mp hf
  -- in that state (s), φ ∈ s, so we do not have ¬ φ ∈ s (by consistency)
  -- contradiction with hnφ
  rw [hsf] at hφ
  have := contra_contains_pr_false s.2 hφ.left
  simp only at this
  apply this
  rw [hs]
  exact hnφ

end canonical
