/-
Authors: Kai Obendrauf
Following the paper "Coalition Logic with Individual, Distributed and Common Knowledge
by Thomas Ågotnes and Natasha Alechina

This file defines how a model, where states contain formulas form
 might be filtered through some closure cl into a Finite model.
We define S_f as the filtered Set of states, and s_f as the filtered state s ∩ cl(φ)).
  We prove several lemmas about these filtered states, and the Set of all filtered states.
  We also define phi_s_f as the conjunction of all formulas in some filtered state s_f, and
  phi_X_set for some Set of filtered states in X as the disjunction of phi_s_f
  for all filtered states in X and then prove several lemmas related to these definitions.
Lastly we prove that given that cl is closed under single negations
  the filtered model is playable. Using this we define an epistemic coalition model by filtering
  the canonical model for CL through some closure.
-/

import CLLean.Completeness.canonical
import Mathlib.Tactic.SplitIfs

open Set Logic Classical

namespace canonical

----------------------------------------------------------
-- Defining Sf
----------------------------------------------------------
-- S_f := {(s ∩ cl(φ)) | s ∈ S}
def S_f {agents form : Type} (m : modelCL agents) [SetLike m.f.states form]
  (cl : form → Finset (form)) (φ : form) : Type :=
Finset.attach (Finset.filter
  (λ sf => ∃ s: m.f.states, {x | x ∈ cl φ ∧ x ∈ s} = {x | x ∈ sf})
  (Finset.powerset (cl φ)))

/-- Allows us to write `φ ∈ sf` instead of `φ ∈ sf.1.1` -/
protected instance S_f.SetLike {agents form : Type} (m : modelCL agents) [hm : SetLike m.f.states form]
  (cl : form → Finset (form)) (φ : form) :
  SetLike (S_f m cl φ) (form) :=
{ coe            := λ sf => sf.1.1
  coe_injective' := λ x y h => Subtype.coe_injective (Subtype.coe_injective
                    (by simpa only [Finset.setOf_mem,Finset.coe_inj] using h)) }

-- Sf is  Finite
protected noncomputable instance S_f.Fintype {agents form : Type}
  (m : modelCL agents) [SetLike m.f.states form]
  (cl : form → Finset (form)) (φ : form) : Fintype (S_f m cl φ) :=
inferInstanceAs (Fintype (Additive _))

@[simp] lemma mem_mk {agents form : Type} [Nonempty agents]
  [Pformula_ax form] [CLformula agents form]
  (hnpr : ¬ ⊢' (⊥' : form)) (cl : form → Finset (form)) {φ ψ : form}
  {sf : S_f (canonical_model_CL agents form hnpr) cl φ} :
  (Membership.mem ψ sf) ↔ ψ ∈ sf.1.1 :=
Iff.rfl

@[simp] lemma mem_mk' {agents form : Type} [Nonempty agents]
  [Pformula_ax form] [CLformula agents form]
  (hnpr : ¬ ⊢' (⊥' : form)) (cl : form → Finset (form))
  {φ ψ : form} {s} (hs₁ hs₂) :
  @Membership.mem _ (S_f (canonical_model_CL agents form hnpr) cl φ) _ ψ ⟨⟨s, hs₁⟩, hs₂⟩ ↔ ψ ∈ s :=
Iff.rfl

----------------------------------------------------------
-- Getting sf from s
----------------------------------------------------------
noncomputable def s_f {agents form : Type} {m : modelCL agents} [hm : SetLike m.f.states form]
  (cl : form → Finset (form)) (φ : form) (s : m.f.states) :
  (S_f m cl φ) := by
  fconstructor
  fconstructor
  exact Finset.filter (λ ψ => ψ ∈ s) (cl φ)
  simp only [Finset.setOf_mem, Finset.filter_congr_decidable, Finset.mem_powerset, not_exists,
    Finset.mem_filter, Finset.filter_subset, Finset.coe_filter, exists_apply_eq_apply, and_self]
  simp only [Finset.mem_attach]

-- get sf from s
lemma s_to_s_f {agents form : Type} {m : modelCL agents} [hm : SetLike m.f.states form]
  (cl : form → Finset (form)) (φ : form) (s : m.f.states) :
  ∃ sf : (S_f m cl φ), ∀ {ψ}, ψ ∈ sf ↔ ψ ∈ s ∧ ψ ∈ cl φ := by
  fconstructor
  fconstructor
  fconstructor
  · exact Finset.filter (λ ψ => ψ ∈ s) (cl φ)
  · simp only [Finset.setOf_mem, Finset.filter_congr_decidable, Finset.mem_powerset, not_exists,
    Finset.mem_filter, Finset.filter_subset, Finset.coe_filter, exists_apply_eq_apply, and_self]
  · simp only [Finset.mem_attach]
  · intro x
    apply Iff.intro
    · intro h
      exact And.comm.mp (Finset.mem_filter.mp h)
    · intro h
      exact Finset.mem_filter.mpr (And.comm.mp h)

----------------------------------------------------------
-- Getting s from sf
----------------------------------------------------------
-- for each sf, there exists some s which filters to sf
lemma s_f_to_s {agents form : Type} {m : modelCL agents} [hm : SetLike m.f.states form]
  {cl : form → Finset (form)} {φ : form} (sf : (S_f m cl φ)) :
  ∃ s: m.f.states, ∀ {ψ}, ψ ∈ sf ↔ ψ ∈ s ∧ ψ ∈ cl φ := by
  have hs := (Finset.mem_filter.mp sf.1.2).2
  cases' hs with s hs
  apply Exists.intro s
  rw [Set.ext_iff] at hs
  simp only [mem_setOf_eq, Finset.setOf_mem, Finset.mem_coe] at hs
  intro ψ
  specialize hs ψ
  apply Iff.intro
  · intro h
    exact And.comm.mp (hs.mpr h)
  · intro h
    exact hs.mp (And.comm.mp h)

----------------------------------------------------------
-- Lemmas about sf
----------------------------------------------------------
-- Sf is not empty
instance S_f.Nonempty {agents form : Type} (m : modelCL agents) [hm : SetLike m.f.states form]
  (cl : form → Finset (form)) (φ : form) :
  Nonempty (S_f m cl φ) := by
  have hs := m.f.hs
  cases' hs with s
  have sf := s_f cl φ s
  exact Nonempty.intro sf

-- sf ⊆ s
lemma s_f_subset_s {agents form : Type} {m : modelCL agents} [hm : SetLike m.f.states form]
  (cl : form → Finset (form)) (φ : form) (s : m.f.states) :
  ∀ ψ, ψ ∈ s_f cl φ s → ψ ∈ s := by
  unfold s_f
  intro ψ hψ
  exact (Finset.mem_filter.mp hψ).2

-- sf ⊆ cl φ
lemma s_f_subset_cl {agents form : Type} {m : modelCL agents} [hm : SetLike m.f.states form]
  {cl : form → Finset (form)} {φ : form} (sf : (S_f m cl φ)) :
  ∀ ψ, ψ ∈ sf → ψ ∈ cl φ := by
  have hs := (Finset.mem_filter.mp sf.1.2).2
  cases' hs with s hs
  rw [Set.ext_iff] at hs
  intro ψ hψ
  exact ((hs ψ).mpr hψ).1

-- all sf are consistent, if M is the defined canonincal model
lemma s_f_ax {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} (cl : form → Finset (form)) (φ : form)
  (sf : (S_f (canonical_model_CL agents form hnpr) cl φ)) :
  ax_consistent {x | x ∈ sf} := by
  cases' (s_f_to_s sf) with s hs
  have hax := s.2.1
  simp only [mem_mk, Finset.setOf_mem, ax_consistent, set_proves,
    canonical_model_CL.f.states.val_eq_coe, SetLike.mem_coe, not_exists, not_and,
    Finset.mem_coe] at *
  intro ψs hψs hcon
  apply hax ψs _ hcon
  intro χ hχs
  have hs : ∀ x ∈ sf, x ∈ s :=
    λ x hx => (hs.mp hx).1
  apply hs
  apply hψs
  exact hχs

-- sf = tf iff they have the same Finset
@[simp] lemma s_f_eq {agents form : Type} {m : modelCL agents} [hm : SetLike m.f.states form]
  {cl : form → Finset (form)} {φ : form} {sf tf : (S_f m cl φ)} :
  sf.1.1 = tf.1.1 ↔ sf = tf := by
  constructor
  · intro h
    cases' sf with sf_val _
    cases' tf with tf_val _
    cases' sf_val
    cases' tf_val
    simp_all only [Finset.setOf_mem]
  · intro h
    rw [h]


-- if sf = s ∩ cl(φ), then it is s filtered
lemma s_f_eq_sf {agents form : Type} {m : modelCL agents} [hm : SetLike m.f.states form]
  {cl : form → Finset (form)} {φ : form} {sf : (S_f m cl φ)} {s : m.f.states}
  (hs : ∀ {x}, x ∈ sf ↔ (x ∈ s ∧ x ∈ cl φ)) : (s_f cl φ s) = sf := by
  rw [←s_f_eq]
  unfold s_f
  ext1 x
  apply Iff.intro
  · intro h
    exact hs.mpr (And.comm.mp (Finset.mem_filter.mp h))
  · intro h
    apply Finset.mem_filter.mpr
    exact (And.comm.mp (hs.mp h))

-- sf = s ∩ cl(φ)
lemma sf_eq_forall {agents form : Type} {m : modelCL agents} [hm : SetLike m.f.states form]
  {cl : form → Finset (form)} {φ : form} {sf : (S_f m cl φ)} {s : m.f.states}
  (hs : sf = (s_f cl φ s)) : ∀ {x}, x ∈ sf ↔ (x ∈ s ∧ x ∈ cl φ) := by
  intro ψ
  apply Iff.intro
  · intro h
    apply And.intro
    · rw [hs] at h
      exact s_f_subset_s cl φ s ψ h
    · exact s_f_subset_cl sf ψ h
  · intro h
    rw [hs]
    unfold s_f
    apply Finset.mem_filter.mpr
    apply And.comm.mp h

-- if sf = s ∩ cl(φ), then it is s filtered
lemma sf_eq_s_f {agents form : Type} {m : modelCL agents} [SetLike m.f.states form]
  {cl : form → Finset (form)} {φ : form} {sf : (S_f m cl φ)} {s : m.f.states}
  (hs : ∀ {x}, x ∈ sf ↔ (x ∈ s ∧ x ∈ cl φ)) : sf = (s_f cl φ s) :=
(Eq.symm (s_f_eq_sf @hs))

-- ψ ∈ s → ψ ∈ cl(φ) → ψ ∈ sf
lemma s_f_contains {agents form : Type} {m : modelCL agents} [SetLike m.f.states form]
  {cl : form → Finset (form)} {φ ψ : form} (sf : (S_f m cl φ)) (s : m.f.states)
  (hs : ∀ {x}, x ∈ sf ↔ x ∈ s ∧ x ∈ cl φ) :
  ψ ∈ s → ψ ∈ cl φ → ψ ∈ sf :=
λ h1 h2 => hs.mpr (And.intro h1 h2)

-- (ψ ∉ s) ∨ (ψ ∉ cl(φ)) → ψ ∉ sf
lemma s_f_n_contains {agents form : Type} {m : modelCL agents} [hm : SetLike m.f.states form]
  {cl : form → Finset (form)} {φ ψ : form} {sf : (S_f m cl φ)} {s : m.f.states}
  (hs : ∀ {x}, x ∈ sf ↔ x ∈ s ∧ x ∈ cl φ) :
  (ψ ∉ s ∨ ψ ∉ cl φ) → ψ ∉ sf := λ _ => by rwa [hs, not_and_or]

lemma s_n_contains {agents form : Type} {m : modelCL agents} [hm : SetLike m.f.states form]
  {cl : form → Finset (form)} {φ ψ : form} {sf : (S_f m cl φ)} {s : m.f.states}
  (hs : ∀ {x}, x ∈ sf ↔ x ∈ s ∧ x ∈ cl φ) (hcl : ψ ∈ cl φ):
  ψ ∉ sf → ψ ∉ s := by
  intro h
  by_contra hf
  exact h (hs.mpr ⟨hf, hcl⟩)

-- ψ ∈ cl φ ⇒ ((∀ sf, ψ ∉ sf) ⇔ (⊢ ψ ↔ ⊥)) when M = canonical model
lemma S_f_empty_iff_false_sf {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {cl : form → Finset (form)} {φ ψ : form} (hψ : ψ ∈ cl φ)
  (hempty : {sf : (S_f (canonical_model_CL agents form hnpr) cl φ) | ψ ∈ sf} = ∅) :
  ⊢' (ψ ↔' ⊥') := by
  apply set_empty_iff_false
  rw [subset_empty_iff]
  rw [eq_empty_iff_forall_not_mem] at *
  intro s hf
  have hsf := @s_to_s_f _ _ (canonical_model_CL agents form hnpr) _ cl φ s
  cases' hsf with sf hsf
  apply hempty sf (hsf.mpr (And.intro hf hψ))

-- x ∉ sf ⇒ ∃ y ∈ sf, ⊢ (y ↔ ¬ x) when M = canonical model
lemma s_f_closed {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {cl : form → Finset (form)} {φ ψ : form}
  (hcl : ∀ ψ, ψ ∈ cl φ → ∃ χ, (χ ∈ cl φ ∧ ⊢' (χ ↔' (¬' ψ))))
  {sf : (S_f (canonical_model_CL agents form hnpr) cl φ)} (hnf : ψ ∉ sf) (hψcl : ψ ∈ cl φ) :
  ∃ χ, χ ∈ sf ∧ ⊢' (χ ↔' ¬' ψ) := by
  -- χ ∉ s, by definition Sf, because χ ∈ cl(φ).
  have hns := s_f_to_s sf
  cases' hns with s hns
  have hn : ψ ∉ s:= by
      by_contra hf
      apply hnf
      exact hns.mpr (And.intro hf hψcl)
  -- ¬ψ ∈ s:= hs, because v is maximally consistent.
  have hnx : ((¬' ψ) ∈ s) := not_in_from_notin s.2 hn
  -- ∃χ, (⊢ χ ↔ ¬ψ) ∧ (χ ∈ cl(φ)), because cl is closed under single negations.
  obtain ⟨χ, hχ⟩  := hcl ψ hψcl
  -- χ ∈ s, because s is maximally consistent.
  have hs : χ ∈ s := by
    apply max_ax_contains_by_set_proof s.2 hnx (iff_r hχ.2)
  -- χ ∈ sf := 7 & 8, by definition Sf.
  have hsf : χ ∈ sf := hns.mpr (And.intro hs hχ.1)
  apply Exists.intro χ
  apply And.intro
  · exact hsf
  · exact hχ.right

@[simp] lemma set_of_S_f {agents form : Type} {m : modelCL agents} [SetLike m.f.states form]
  {cl : form → Finset (form)} {φ ψ : form} (sf : S_f m cl φ) :
  sf ∈ {sf : S_f m cl φ | ψ ∈ sf} ↔ (ψ ∈ sf) := mem_setOf


----------------------------------------------------------
-- phi sf
----------------------------------------------------------
noncomputable def phi_s_f {agents form : Type} [Pformula form]
  {m : modelCL agents} [SetLike m.f.states form]
  {cl : form → Finset (form)} {φ : form} (sf : S_f m cl φ) : form :=
finite_conjunction (Finset.toList (sf.1))

-- phi sf ∈ s when M = canonical model
lemma phi_s_f_in_s {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {cl : form → Finset (form)} {φ : form}
  (s : (canonical_model_CL agents form hnpr).f.states):
  phi_s_f ((s_f cl φ s)) ∈ s := by
  simp only [phi_s_f, Finset.setOf_mem]
  have hinduct : ∀ fs : List (form),
    (fs ⊆ ((s_f cl φ s).1 : Finset (form)).toList) → finite_conjunction fs ∈ s := by
    intro fs hfs
    induction' fs with f fs ih
    · unfold finite_conjunction
      apply max_ax_contains_taut s.2 prtrue
    · simp only [Finset.setOf_mem, List.cons_subset, Finset.mem_toList,
      finite_conjunction_cons] at *
      cases' hfs with hf hfs
      have hf_in_s : f ∈ s:= s_f_subset_s cl φ s f hf
      have hfs_in_s : finite_conjunction fs ∈ s:= ih hfs
      apply max_ax_contains_by_set_proof_2h s.2 hf_in_s hfs_in_s
      apply p4
  apply hinduct
  simp only [Finset.setOf_mem, List.Subset.refl]

-- ⊢ phi sf ⇔ ∀ x ∈ sf, ⊢ x
lemma phi_s_f_forall_iff {agents form : Type} [pf : Pformula_ax form]
  {m : modelCL agents} [hm : SetLike m.f.states form]
  {cl : form → Finset (form)} {φ : form} (sf : S_f m cl φ) :
  (∀ x : form, x ∈ sf → ⊢' x) ↔ ⊢' (phi_s_f sf) := by
  unfold phi_s_f
  apply Iff.intro
  · intro h
    apply finite_conj_forall_iff.mp
    intro x hx
    apply h
    exact (Multiset.mem_toList).mp hx
  · intro h x hx
    apply finite_conj_forall_iff.mpr
    exact h
    exact (Multiset.mem_toList).mpr hx

-- ∀ x ∈ sf, ⊢ ((phi_s_f φ sf) → x
lemma phi_s_f_forall_imp {agents form : Type} [pf : Pformula_ax form]
  {m : modelCL agents} [hm : SetLike m.f.states form] {cl : form → Finset (form)} {φ : form}
  {sf : S_f m cl φ} : (∀ x ∈ sf, ⊢' ((phi_s_f sf) →' x)) :=  by
  unfold phi_s_f
  intro x hx
  have hx : x ∈ sf.1.1.toList:= (Multiset.mem_toList).mpr hx
  exact finite_conj_forall_imp x (hx)

-- ⊢ ¬ ψ → ¬ phi sf
lemma notin_nphi_s_f {agents form : Type} [pf : Pformula_ax form]
  {m : modelCL agents} [hm : SetLike m.f.states form] {cl : form → Finset (form)} {φ ψ : form}
  {sf : S_f m cl φ} (h : ψ ∈ sf) : ⊢' ((¬' ψ) →' (¬' (phi_s_f sf))) := by
  unfold phi_s_f
  apply noin_imp_nfin_con
  simp only [Finset.setOf_mem, Finset.mem_toList]
  apply h

-- ∀ ψ ∈ sf ⇒ (⊢ phi sf ↔ (ψ ∧ phi sf))
lemma phi_s_f_conj_contains {agents form : Type} [pf : Pformula_ax form]
  {m : modelCL agents} [hm : SetLike m.f.states form] {cl : form → Finset (form)} {φ ψ : form}
  {sf : S_f m cl φ} (hψ : ψ ∈ sf) : ⊢' ((phi_s_f sf) ↔' (ψ ∧' (phi_s_f sf))) := by
  apply ax_iff_intro
  · apply imp_imp_and
    exact phi_s_f_forall_imp _ hψ
    exact iden
  · apply imp_and_r
    exact iden


----------------------------------------------------------
-- phi X (given a List)
----------------------------------------------------------
noncomputable def phi_X_list {agents form : Type} [Pformula form]
  {m : modelCL agents} [SetLike m.f.states form] {cl : form → Finset (form)} {φ : form} :
  List (S_f m cl φ) → List (form)
| List.nil   => List.nil
| (sf :: ss) => ((phi_s_f sf) :: phi_X_list ss)

-- if sf ∈ X, then phi sf is one of the disjuncts in phi X
lemma phi_X_list_contains {agents form : Type} [pf : Pformula form]
  {m : modelCL agents} [hm : SetLike m.f.states form] {cl : form → Finset (form)} {φ : form}
  {sfs : List (S_f m cl φ)} {sf : (S_f m cl φ)} (hsf : sf ∈ sfs) :
  (phi_s_f sf) ∈ phi_X_list sfs := by
  induction' sfs with hd sfs ih
  · by_contra
    simp only [List.find?_nil, List.not_mem_nil] at *
  · cases' hsf with _ _ _ hsf
    · simp only [phi_X_list, Bool.not_eq_true, List.mem_cons, true_or]
    · simp only [phi_X_list, Bool.not_eq_true, List.mem_cons] at *
      apply Or.intro_right
      exact ih hsf

-- if sf ⊆ sfs', then phi_list sfs ⊆ phi_list sfs'
lemma phi_X_list_subset {agents form : Type} [pf : Pformula form]
  {m : modelCL agents} [hm : SetLike m.f.states form] {cl : form → Finset (form)} {φ : form}
  {sfs sfs' : List (S_f m cl φ)} (h : sfs ⊆ sfs') :
  phi_X_list sfs ⊆ phi_X_list sfs' := by
  induction' sfs with hd sfs ih
  · simp only [phi_X_list, List.nil_subset]
  · simp only [List.cons_subset, phi_X_list] at *
    apply And.intro
    · exact phi_X_list_contains h.left
    · exact ih h.right

-- phi_list (X ++ Y) ⊆ phi_list φ X ++ phi_list φ Y
lemma phi_X_list_append {agents form : Type} [pf : Pformula form]
  {m : modelCL agents} [hm : SetLike m.f.states form] {cl : form → Finset (form)} {φ : form}
  (X Y : List (S_f m cl φ)) :
  phi_X_list (X ++ Y) ⊆ phi_X_list X ++ phi_X_list Y := by
  induction' X with hd X ih
  · simp only [List.nil_append, phi_X_list, List.Subset.refl]
  · simp only [phi_X_list, List.append_eq, List.cons_append, List.cons_subset, Bool.not_eq_true,
      List.mem_cons, List.mem_append, true_or, true_and]
    exact List.subset_cons_of_subset _ ih

-- ⊢ phi sf ↔ phi {sf}
lemma phi_X_list_single {agents form : Type} [pf : Pformula_ax form]
  {m : modelCL agents} [hm : SetLike m.f.states form] {cl : form → Finset (form)} {φ : form}
  (sf : (S_f m cl φ)) : ⊢' ((phi_s_f sf) ↔' finite_disjunction (phi_X_list [sf])) := by
  apply ax_iff_intro
  · unfold phi_X_list finite_disjunction
    apply cut
    exact dni
    exact iden
  · unfold phi_X_list finite_disjunction
    exact dne

-- ∀ sf, sf ∈ X → ψ ∈ sf ⇒ ⊢ phi X ↔ ψ ∧ phi X
lemma phi_X_list_conj_contains {agents form : Type} [pf : Pformula_ax form]
  {m : modelCL agents} [hm : SetLike m.f.states form] {cl : form → Finset (form)} {φ ψ : form}
  {X : List (S_f m cl φ)} (hψ : ∀ sf, sf ∈ X → ψ ∈ sf) :
  ⊢' (finite_disjunction (phi_X_list X) ↔' (ψ ∧' finite_disjunction (phi_X_list X))) := by
  induction' X with sf X ih
  · simp only [phi_X_list, finite_disjunction, ax_and, explosion, true_and]
    apply imp_and_r
    exact explosion
  · simp only [phi_X_list, finite_disjunction, ax_and]
    apply And.intro
    · apply or_cases
      · apply imp_imp_and
        · apply cut
          apply iff_l
          apply phi_s_f_conj_contains
          apply hψ
          simp only [List.mem_cons, eq_self_iff_true, true_or]
          exact p5 _ _
        · exact contra_explosion
      · have hψ' : ∀ sf, sf ∈ X → ψ ∈ sf:= by
          intro tf htf
          apply hψ
          simp only [Bool.not_eq_true, List.mem_cons, htf, or_true]
        specialize ih hψ'
        have ih := ax_and.mp ih
        apply imp_imp_and
        · apply cut
          exact ih.left
          exact p5 _ _
        · exact p1 _ _
    · exact p6 _ _

-- ∀ sf ∈ X, phi sf ∉ s ⇒ ¬ phi X ∈ s, when M = canonical model
lemma phi_X_list_exists {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form] {hnpr : ¬ ⊢' (⊥' : form)}
  {cl : form → Finset (form)} {φ : form}
  {X : List (S_f (canonical_model_CL agents form hnpr) cl φ)}
  {s : (canonical_model_CL agents form hnpr).f.states}
  (hfa : ∀ sf, sf ∈ X → phi_s_f sf ∉ s) : (¬' (finite_disjunction (phi_X_list X))) ∈ s := by
  induction' X with x X ih
  · simp only [phi_X_list, finite_disjunction]
    apply max_ax_contains_taut s.2 iden
  · simp only [phi_X_list, finite_disjunction] at *
    simp only [List.mem_cons, List.mem_cons] at hfa
    apply max_ax_contains_by_set_proof s.2 _ (iff_r demorgans'''')
    apply max_ax_contains_by_set_proof_2h s.2 _ _ (p4 _ _)
    · apply not_in_from_notin s.2
      apply hfa x
      simp only [eq_self_iff_true, true_or]
    · apply ih
      intro y hy
      apply hfa
      exact Or.intro_right _ hy

-- ∀ s, ∀ sf ∈ X, ¬' (K' i (¬'(phi sf))) ∉ s ⇒
-- (¬' (∨ {¬' K' i ¬' φ : φ ∈ phi_X_list X} ∈ s
lemma nk_phi_X_list_exists {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form] [kf : Kformula agents form] {hnpr}
  {cl : form → Finset (form)} {φ : form} (i : agents)
  {X : List (S_f (canonical_model_CL agents form hnpr) cl φ)}
  {s : (canonical_model_CL agents form hnpr).f.states}
  (hfa : ∀ sf, sf ∈ X → ¬' (K' i (¬'(phi_s_f sf))) ∉ s) :
  (¬' (finite_disjunction (List.map (λ φ => ¬' (K' i (¬' φ))) (phi_X_list X)))) ∈ s := by
  induction' X with x X ih
  · unfold phi_X_list finite_disjunction
    apply max_ax_contains_taut s.2 iden
  · unfold phi_X_list finite_disjunction
    simp only [List.mem_cons, s_f_eq] at hfa
    apply max_ax_contains_by_set_proof s.2 _ (iff_r demorgans'''')
    apply max_ax_contains_by_set_proof_2h s.2 _ _ (p4 _ _)
    · apply not_in_from_notin s.2
      apply hfa x
      simp only [eq_self_iff_true, true_or]
    · apply ih
      intro y hy
      apply hfa
      exact Or.intro_right _ hy

----------------------------------------------------------
-- phi X (given a Finset)
----------------------------------------------------------
noncomputable def phi_X_finset {agents form : Type} [Pformula form]
  {m : modelCL agents} [SetLike m.f.states form] {cl : form → Finset (form)} {φ : form}
  (X : Finset (S_f m cl φ)) : form :=
finite_disjunction (phi_X_list (Finset.toList X))

-- X ⊆ Y ⇒ ⊢ phi X → phi Y
lemma phi_X_subset_Y_imp {agents form : Type} [pf : Pformula_ax form]
  {m : modelCL agents} [hm : SetLike m.f.states form] {cl : form → Finset (form)} {φ : form}
  (X Y : Finset (S_f m cl φ)) (hXY : X ⊆ Y) :
  ⊢' ((phi_X_finset X) →' (phi_X_finset Y)) := by
  unfold phi_X_finset
  apply imp_finite_disjunction_subset
  apply phi_X_list_subset
  intro f hf
  rw [Finset.mem_toList] at *
  exact Finset.subset_iff.mp hXY hf

-- phi (X ++ Y) ⊆ phi (X ∪ Y)
lemma phi_X_finset_app_subseteq_un {agents form : Type} [pf : Pformula_ax form]
  {m : modelCL agents} [hm : SetLike m.f.states form] {cl : form → Finset (form)} {φ : form}
  (X Y : Finset (S_f m cl φ)) :
  phi_X_list X.toList ++ phi_X_list Y.toList ⊆ phi_X_list (X ∪ Y).toList := by
  rw [List.append_subset]
  apply And.intro
  · apply phi_X_list_subset
    intro f hf
    rw [Finset.mem_toList] at *
    exact Finset.mem_union_left Y hf
  · apply phi_X_list_subset
    intro f hf
    rw [Finset.mem_toList] at *
    exact Finset.mem_union_right X hf

-- phi (X ∪ Y) ⊆ phi (X ++ Y)
lemma phi_X_finset_un_subseteq_app {agents form : Type} [pf : Pformula_ax form]
  {m : modelCL agents} [hm : SetLike m.f.states form] {cl : form → Finset (form)} {φ : form}
  (X Y : Finset (S_f m cl φ)) :
  phi_X_list (X ∪ Y).toList ⊆ phi_X_list X.toList ++ phi_X_list Y.toList := by
  have h2 : phi_X_list (X ∪ Y).toList ⊆ phi_X_list (X.toList ++ Y.toList):= by
    apply phi_X_list_subset
    intro f hf
    simp only [Finset.mem_toList, Finset.mem_union, List.mem_append] at *
    exact hf
  exact List.Subset.trans h2 (phi_X_list_append X.toList Y.toList)

-- ⊢ (¬ phi X → phi Y) → phi (X ∪ Y)
lemma phi_X_finset_union {agents form : Type} [pf : Pformula_ax form]
  {m : modelCL agents} [hm : SetLike m.f.states form] {cl : form → Finset (form)} {φ : form}
  (X Y : Finset (S_f m cl φ)) :
  ⊢' ((¬' (phi_X_finset X) →' (phi_X_finset Y)) →' (phi_X_finset (X ∪ Y))) := by
  unfold phi_X_finset
  apply cut
  apply disjunc_disjunct
  apply imp_finite_disjunction_subset
  exact phi_X_finset_app_subseteq_un _ _

-- ⊢ (¬ phi X → phi Y) ⇔ ⊢ phi (X ∪ Y)
lemma phi_X_finset_disjunct_of_disjuncts {agents form : Type} [pf : Pformula_ax form]
  {m : modelCL agents} [hm : SetLike m.f.states form] {cl : form → Finset (form)} {φ : form}
  (X Y : Finset (S_f m cl φ)) :
  ⊢' (¬' (phi_X_finset X) →' (phi_X_finset Y)) ↔ ⊢' (phi_X_finset (X ∪ Y)) := by
  have hax := @ax_iff_disjunc_disjunct _ _ (phi_X_list X.toList) (phi_X_list Y.toList)
  unfold phi_X_finset
  apply Iff.intro
  · intro h
    apply MP' (hax.mp h)
    apply imp_finite_disjunction_subset
    exact phi_X_finset_app_subseteq_un _ _
  · intro h
    apply hax.mpr
    apply MP' h
    apply imp_finite_disjunction_subset
    exact phi_X_finset_un_subseteq_app _ _

----------------------------------------------------------
-- phi X (given a Set)
----------------------------------------------------------

/-- `phi_X_set φ X` is a Finite disjunction of all elements of `X`. -/
noncomputable def phi_X_set {agents form : Type} [Pformula form]
  {m : modelCL agents} [SetLike m.f.states form] {cl : form → Finset (form)} {φ : form}
  (X : Set (S_f m cl φ)) : form :=
phi_X_finset (Finite.toFinset (Set.toFinite X))

-- phi (X ∪ Y) ⊆ phi (X ++ Y)
lemma phi_X_set_subset_Y_imp {agents form : Type} [pf : Pformula_ax form]
  {m : modelCL agents} [hm : SetLike m.f.states form] {cl : form → Finset (form)} {φ : form}
  {X Y : Set (S_f m cl φ)} (hXY : X ⊆ Y) :
  ⊢' ((phi_X_set X) →' (phi_X_set Y)) := by
  unfold phi_X_set
  apply phi_X_subset_Y_imp
  exact Finite.toFinset_subset_toFinset.mpr hXY


-- ⊢ (¬ phi X → phi Y) → phi (X ∪ Y)
lemma phi_X_set_disjunct {agents form : Type} [pf : Pformula_ax form]
  {m : modelCL agents} [hm : SetLike m.f.states form] {cl : form → Finset (form)} {φ : form}
  (X Y : Set (S_f m cl φ)) :
  ⊢' ((¬' (phi_X_set X) →' (phi_X_set Y)) →' (phi_X_set (X ∪ Y))) := by
  unfold phi_X_set
  apply cut
  apply phi_X_finset_union
  apply phi_X_subset_Y_imp
  apply Finset.union_subset
  repeat
  · simp only [Finite.toFinset_subset_toFinset, subset_union_left, subset_union_right]

-- ⊢ (¬ phi X → phi Y) ⇔ ⊢ phi (X ∪ Y)
lemma phi_X_set_disjunct_of_disjuncts {agents form : Type} [pf : Pformula_ax form]
  {m : modelCL agents} [hm : SetLike m.f.states form] {cl : form → Finset (form)} {φ : form}
  (X Y : Set (S_f m cl φ)) :
  ⊢' (¬' (phi_X_set X) →' (phi_X_set Y)) ↔ ⊢' (phi_X_set (X ∪ Y)) := by
  unfold phi_X_set
  apply Iff.intro
  · intro h
    apply MP' ((phi_X_finset_disjunct_of_disjuncts _ _).mp h)
    apply phi_X_subset_Y_imp
    apply Finset.union_subset
    repeat
    · simp only [Finite.toFinset_subset_toFinset, subset_union_left, subset_union_right]
  · intro h
    apply (phi_X_finset_disjunct_of_disjuncts _ _).mpr
    apply MP' h
    apply phi_X_subset_Y_imp
    apply Finset.subset_iff.mpr
    intro f hf
    simp only [Finite.toFinset_setOf, Finset.mem_univ, forall_true_left, Finset.mem_filter,
      true_and, Finset.mem_union] at *
    exact hf

-- phi X ∈ s ⇒ ∃ tf, phi tf ∈ s, when M is the defined canonical model
lemma phi_X_set_exists {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {cl : form → Finset (form)} {φ : form}
  {X : Set (S_f (canonical_model_CL agents form hnpr) cl φ)}
  {s : (canonical_model_CL agents form hnpr).f.states} (h : phi_X_set X ∈ s) :
  ∃ tf ∈ X, phi_s_f tf ∈ s := by
  by_contra hfa
  simp only [exists_prop, not_exists, not_and] at hfa
  apply in_from_not_notin s.2 h
  apply phi_X_list_exists
  intro sf hsf
  apply hfa
  simp only [Finite.toFinset_setOf, Finset.mem_univ, forall_true_left, Finset.mem_toList,
    Finset.mem_filter, true_and] at hsf
  exact hsf

-- tilde phi ∅ = empty, when M is the defined canonical model
@[simp] lemma tilde_phi_empty {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {cl : form → Finset (form)} {φ : form} :
  tilde ((canonical_model_CL agents form hnpr).f.states)
    (phi_X_set (∅ : Set (S_f (canonical_model_CL agents form hnpr) cl φ))) = ∅ := by
  -- 1.1.1. φ∅ = ⊥, because φ∅ is an empty disjunction, thus  ̃φ∅ =  ̃⊥.
  simp only [phi_X_set, phi_X_finset, phi_X_list, finite_disjunction, tilde,
    Finite.toFinset_empty, Finset.toList_empty]
  -- 1.1.2.  ̃⊥ = ∅, because all s ∈ S are consistent.
  simp only [eq_empty_iff_forall_not_mem, mem_setOf_eq]
  intro s
  exact bot_not_mem_of_ax_consistent s.1 s.2.1

--  sf ∈ X ⇒ ⊢ (phi sf → phi X)
lemma ax_phi_s_f_imp_phi_X_set_of_mem {agents form : Type} [pf : Pformula_ax form]
  {m : modelCL agents} [hm : SetLike m.f.states form] {cl : form → Finset (form)} {φ : form}
  {sf : S_f m cl φ} {X : Set (S_f m cl φ)} (h : sf ∈ X) : ⊢' (phi_s_f (sf) →' phi_X_set X) := by
  unfold phi_X_set
  apply imp_finite_disjunction
  apply phi_X_list_contains
  simpa only [Finite.toFinset_setOf, Finset.mem_univ, forall_true_left, Finset.mem_toList,
    Finset.mem_filter, true_and]


----------------------------------------------------------
-- Lemmas about Sf
----------------------------------------------------------
section lemmas

-- Lemma 4
----------------------------------------------------------
-- ⊢ phi Sf
lemma univ_disjunct_provability {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  (hnpr : ¬ ⊢' (⊥' : form)) (cl : form → Finset (form)) (φ : form) :
  ⊢' (phi_X_set (univ : Set (S_f (canonical_model_CL agents form hnpr) cl φ))) := by
  -- 1. By contradiction, assume that ⊬ phi Sf
  by_contra h
  -- 2.∃t ∈ SC′, ¬ phi Sf ∈ t, because ¬ phi Sf is consistent:= 1.
  obtain ⟨t', hexn, htn⟩ := exists_max_ax_consistent_neg_mem h
  have ht : ∃ t : (canonical_model_CL agents form hnpr).f.states, t = ⟨t', hexn⟩ :=
    exists_apply_eq_apply _ _
  cases' ht with t ht_h
  -- 3. ⊢ phi tf → phi Sf , by propositional logic.
  have himp : ⊢' (phi_s_f (s_f cl φ t) →' phi_X_set univ) :=
    ax_phi_s_f_imp_phi_X_set_of_mem (mem_univ (s_f cl φ t))
  -- 4. phi tf ∈ t, by propositional logic, because all tf ⊆ t.
  have hphitf : phi_s_f (s_f cl φ t) ∈ t.1:= phi_s_f_in_s t
  -- 5. (phi Sf ∈ t, by propositional logic:= 3 & 4.
  have ht : phi_X_set univ ∈ t.1 := max_ax_contains_by_set_proof t.2 hphitf himp
  -- 6. Contradiction from 2 and 5.
  have := contra_contains_pr_false t.2 ht
  simp only [canonical_model_CL.f.states.val_eq_coe, SetLike.mem_coe, ht_h] at this
  exact this htn

-- Lemma 5
----------------------------------------------------------

lemma unique_s_f_helper {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {cl : form → Finset (form)} {φ ψ : form}
  (hcl : ∀ χ, χ ∈ cl φ → ∃ ψ, (ψ ∈ cl φ ∧ ⊢' (ψ ↔' (¬' χ))))
  {sf tf : (S_f (canonical_model_CL agents form hnpr) cl φ)}
  (hsf : ψ ∈ sf) (htf : ψ ∉ tf) : ⊢' (¬' (phi_s_f sf ∧' phi_s_f tf)) :=  by
  -- 6-9. ∃χ, (⊢ χ ↔ ¬ψ) ∧ χ ∈ tf
  obtain ⟨χ, ⟨hχ, hψχ⟩⟩ : ∃ (χ : form), χ ∈ tf ∧ ⊢'(χ ↔' ¬' ψ) :=
    s_f_closed hcl htf (Finset.subset_iff.mp (s_f_subset_cl _) hsf)
  -- 10. {ψ, χ} ⊆ sf ∪ tf := 4 & 9.
  -- 11. φsf ∧ φtf → ⊥, by propositional logic:= 5, 8 _∧ 10.
  apply contra_con_cons hψχ
  repeat
  · simp_all only [mem_mk, Finset.setOf_mem, Finset.mem_toList]

-- sf ≠ tf ⇒ ⊢ phi sf → ¬ phi tf
lemma unique_s_f {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {cl : form → Finset (form)} {φ : form}
  (hcl : ∀ χ, χ ∈ cl φ → ∃ ψ, (ψ ∈ cl φ ∧ ⊢' (ψ ↔' (¬' χ))))
  {sf tf : (S_f (canonical_model_CL agents form hnpr) cl φ)} (hneq : sf ≠ tf) :
  ⊢' (phi_s_f sf →' ¬' (phi_s_f tf)) := by
  -- 1. Assume by contradiction ⊬ phi sf → ¬ phi tf
  by_contra h
  -- 2. ∃u ∈ SC′, ¬(phi sf → ¬ phi tf) ∈ u, because ¬(phi sf → ¬ phi tf) is consistent:= 1.
  obtain ⟨u', hexn, hun⟩ := exists_max_ax_consistent_neg_mem h
  have hu : ∃ u : (canonical_model_CL agents form hnpr).f.states, u = ⟨u', hexn⟩ :=
    exists_apply_eq_apply _ _
  cases' hu with u hu
  have hun : ¬' (phi_s_f sf →' ¬' (phi_s_f tf)) ∈ u:=  by
    rw [hu]
    exact hun
  -- 3. phi sf ∧ phi tf ∈ u, by propositional logic:= 2.
  have hand : (phi_s_f sf ∧' (phi_s_f tf)) ∈ u := by
    apply max_ax_contains_by_set_proof u.2 hun demorgans''
  -- 4. ∃ψ ∈ sf ∪ tf , ψ ∉ sf ∨ ψ  tf , because sf ≠ tf . Let vf be either sf or tf
  have : ¬ (sf.1.1 ⊆ tf.1.1) ∨ ¬ (tf.1.1 ⊆ sf.1.1) := by
    rw [←not_and_or]
    rintro ⟨hst, hts⟩
    apply hneq
    have := subset_antisymm hst hts
    simp_all only [ne_eq, Finset.setOf_mem, Finset.Subset.refl, s_f_eq]
  obtain ⟨ψ, hun, hneq'⟩ : ∃ ψ, ψ ∈ (sf.1.1 ∪ tf.1.1) ∧ ((ψ ∉ sf.1.1) ∨ (ψ ∉ tf.1.1))
  · simp only [Finset.not_subset] at this
    rcases this with ⟨x, hxu, hxn⟩ | ⟨x, hxu, hxn⟩;
    · use x;
      simp_all only [ne_eq, Finset.setOf_mem, Finset.mem_union, or_false, not_true_eq_false,
        not_false_eq_true, or_true, and_self]
    · simp only [ne_eq, Finset.setOf_mem, Finset.mem_union]
      apply Exists.intro
      apply And.intro
      apply Or.inr
      exact hxu
      simp_all only [not_false_eq_true, not_true_eq_false, or_false]

  rw [Finset.mem_union] at hun
  -- 5-11. ⊢ phi sf ∧ phi tf → ⊥, using helper (steps 5-11)
  have hcontra : ⊢' phi_s_f sf ∧' phi_s_f tf →' ⊥':= by
    cases' hun with hxf hxf
    · cases' hneq' with hnf hnf
      · by_contra
        exact hnf hxf
      · apply unique_s_f_helper hcl hxf hnf
    · cases' hneq' with hnf hnf
      · apply cut (iff_l and_switch)
        apply unique_s_f_helper hcl hxf hnf
      · by_contra
        exact hnf hxf
  -- 12. ⊥ ∈ u, by propositional logic:= 4 _∧ 11, which contradicts the consistency of u.
  have := ax_neg_contains_pr_false u.2 hand hcontra
  simp only at this

-- Lemma 6
----------------------------------------------------------

lemma contra_fin_disjunct_psi_and_not {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {cl : form → Finset (form)} {φ ψ : form}
  (hcl : ∀ χ, χ ∈ cl φ → ∃ ψ, (ψ ∈ cl φ ∧ ⊢' (ψ ↔' (¬' χ))))
  (hψ : ψ ∈ cl φ) (sfs : List (S_f (canonical_model_CL agents form hnpr) cl φ))
  (hsfs : ∀ sf : (S_f (canonical_model_CL agents form hnpr) cl φ), sf ∈ sfs → ψ ∉ sf) :
  ⊢' (⊥' ↔' (ψ ∧' finite_disjunction (phi_X_list sfs))) := by
  apply ax_iff_intro
  exact explosion
  induction' sfs with sf sfs ih
  · unfold phi_X_list finite_disjunction
    exact p6 _ _
  · have hsfs' : ∀ sf : (S_f (canonical_model_CL agents form hnpr) cl φ), sf ∈ sfs → ψ ∉ sf := by
      intro sf hsf
      apply hsfs
      simp only [Bool.not_eq_true, List.mem_cons, hsf, or_true]
    specialize ih hsfs'
    apply and_right_imp.mpr
    apply or_cases
    · have hχ :=
      s_f_closed hcl (hsfs sf (by simp only [Bool.not_eq_true, List.mem_cons, true_or])) hψ
      cases' hχ with χ hχ
      apply cut
      apply iff_l
      apply phi_s_f_conj_contains hχ.left
      apply imp_and_l
      apply cut
      apply iff_l
      apply hχ.2
      exact iden
    · apply and_right_imp.mp
      exact ih


-- Lemma 6. ∀ ψ ∈ cl(φ), phi {sf | ψ ∈ sf} ↔ ψ
lemma phi_X_contains_iff_psi_list {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {cl : form → Finset (form)} {φ ψ : form}
  (hcl : ∀ χ, χ ∈ cl φ → ∃ ψ, (ψ ∈ cl φ ∧ ⊢' (ψ ↔' (¬' χ)))) (hψ : ψ ∈ cl φ)
  {sfs tfs : List (S_f (canonical_model_CL _ _ hnpr) cl φ)}
  (hsfs : ∀ sf, sf ∈ sfs → ψ ∈ sf) (htfs : ∀ tf, tf ∈ tfs → ψ ∉ tf)
  (hSf : ⊢' (finite_disjunction (phi_X_list tfs)) ∨' (finite_disjunction (phi_X_list sfs))) :
  ⊢' ((finite_disjunction (phi_X_list sfs)) ↔' ψ) := by
  -- phi {sf |ψ ∈ sf }
  -- ↔ ∨ {sf |ψ ∈ sf } (ψ ∧ φsf), by propositional logic.
  apply iff_cut
  exact (phi_X_list_conj_contains hsfs)
  -- ↔ ⊥ ∨ (∨{sf |ψ ∈ sf }(ψ ∧ φsf)), by propositional logic.
  apply iff_cut
  exact and_switch_ax.mp (ax_not_bot_imp_iff _)
  -- ↔ (∨ {tf |¬ ψ ∈tf} (ψ ∧ φtf)) ∨ (∨ {sf |ψ∈sf }(ψ ∧ φsf)), by propositional logic.
  apply iff_cut
  apply or_cut_l
  exact contra_fin_disjunct_psi_and_not hcl hψ tfs htfs
   -- ↔ ψ ∧ ((∨ {tf |_¬ψ∈tf } φtf ) ∨ (∨ {sf |ψ∈sf } φsf )), by propositional logic.
  apply iff_cut
  exact distr_or_and
  -- ↔ ψ ∧ (∨ {sf ∈ Sf } φsf ), because {tf | ¬ ψ ∈ tf } ∪ {sf | ψ ∈ sf } = Sf.
  -- ↔ ψ ∧ ⊤:= Lemma 4.
  apply iff_cut
  apply and_cut_r
  exact pr_iff_true hSf
  -- ↔ ψ, by propositional logic.
  apply ax_and_top_iff

lemma phi_X_contains_iff_psi_finset {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {cl : form → Finset (form)} {φ ψ : form}
  (hcl : ∀ χ, χ ∈ cl φ → ∃ ψ, (ψ ∈ cl φ ∧ ⊢' (ψ ↔' (¬' χ)))) (hψ : ψ ∈ cl φ)
  {sfs : Finset (S_f (canonical_model_CL agents form hnpr) cl φ)}
  (hsfs : ∀ sf, sf ∈ sfs → ψ ∈ sf) (htfs : ∀ tf, tf ∉ sfs → ψ ∉ tf)
  (hSf : ⊢' ((phi_X_finset sfsᶜ) ∨' (phi_X_finset sfs))):
  ⊢' ( (phi_X_finset sfs) ↔' ψ) := by
  unfold phi_X_finset
  apply phi_X_contains_iff_psi_list hcl hψ
  simp only [Finset.mem_toList]
  exact hsfs
  show ∀ tf, tf ∈ sfsᶜ.toList → ψ ∉ tf
  simp only [Finset.mem_toList, Finset.mem_compl]
  exact htfs
  exact hSf


lemma phi_X_contains_iff_psi {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {cl : form → Finset (form)} {φ ψ : form}
  (hcl : ∀ χ, χ ∈ cl φ → ∃ ψ, (ψ ∈ cl φ ∧ ⊢' (ψ ↔' (¬' χ)))) (hψ : ψ ∈ cl φ) :
  ⊢' (phi_X_set {sf : (S_f (canonical_model_CL _ _ hnpr) cl φ) | ψ ∈ sf} ↔' ψ) := by
  apply phi_X_contains_iff_psi_finset hcl hψ
  -- ∀ sf, sf ∈ phi {sf | ψ ∈ sf } → ψ ∈ sf
  simp only [Finite.mem_toFinset, mem_setOf_eq, imp_self, forall_const]
  -- ∀ tf, tf ∉ phi {sf | ψ ∈ sf } → ψ ∉ sf
  simp only [Finite.mem_toFinset, mem_setOf_eq, imp_self, forall_const]
  -- ⊢ (phi sfsᶜ) ∨ (phi sfs) ↔ ⊢ phi (sfsᶜ ∪ sfs)
  apply (phi_X_finset_disjunct_of_disjuncts _ _).mpr
  -- ⊢ phi Sf → phi sfsᶜ ∪ sfs and we have ⊢ phi Sf
  apply MP' (univ_disjunct_provability hnpr cl φ)
  -- Sf ⊆ sfsᶜ ∪ sfs ⇒ ⊢ phi Sf → phi sfsᶜ ∪ sfs
  apply phi_X_subset_Y_imp
  -- Sf ⊆ sfsᶜ ∪ sfs
  intro sf hsf
  simp only [Finset.mem_union, Finset.mem_compl, Finite.mem_toFinset, mem_setOf_eq,
    ax_and, mem_univ] at *
  rw [Or.comm]
  exact (Classical.em (ψ ∈ sf))

-- Lemma 7
----------------------------------------------------------

-- Lemma 7.  ̃ψ ∈ EC′ (s)(G) iff [G]ψ ∈ s
lemma E_s_contains_tilde_iff_E_in_s {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {ψ : form}
  (s : (canonical_model_CL agents form hnpr).f.states) (G : Set agents) :
  (((tilde (canonical_model_CL agents form hnpr).f.states) ψ) ∈
    ((canonical_model_CL agents form hnpr).f.E.E s G)) ↔ ((['G] ψ) ∈ s) := by
  let hE : (canonical_model_CL agents form hnpr).f.E.E = λ s G => {X | ite (G = univ)
    (∀ φ, ({t | φ ∈ t} ⊆ Xᶜ) → (['∅] φ) ∉ s.val) (∃ φ, {t | φ ∈ t} ⊆ X ∧ (['G] φ) ∈ s.val)} := rfl
  -- We consider the case when G = N and G ≠ N separately.
  cases' (Classical.em (G = univ)) with hG hG
  · -- 1. case G = N
    rw [hG]
    apply Iff.intro
    -- 1.1. ⇒
    · -- 1.1.1. Assume  ̃ψ ∈ EC′ (s)(N).
      intro h
      -- 1.1.2. ∀ ̃χ ⊆  ̃ψᶜ : [∅]χ ∉ s:= 1.1.1, by definition EC′.
      simp only [hE, eq_self_iff_true, canonical_model_CL.f.states.val_eq_coe, SetLike.mem_coe,
                  if_true, mem_setOf_eq] at h
      clear hE
      -- 1.1.3. ∀ ̃χ ⊆  ̃¬ψ : [∅]χ ∉ s:= 1.1.2, because  ̃ψᶜ =  ̃¬ψ.
      have h_subeq : {t : (canonical_model_CL agents form hnpr).f.states | (¬' ψ) ∈ t} ⊆
        (tilde ((canonical_model_CL agents form hnpr).f.states) ψ)ᶜ:= by
        intro t ht hf
        simp only [tilde, mem_setOf_eq] at *
        have := contra_contains_pr_false t.2 hf ht
        simp only at this
      specialize h (¬' ψ) h_subeq
      -- 1.1.4. [N ]ψ ∈ s:= 1.1.3, by axiom N.
      have hin := not_in_from_notin s.2 h
      apply max_ax_contains_by_set_proof s.2 hin (N _)
    · -- 1.2. ⇐
      -- 1.2.1. Assume [N ]ψ ∈ s.
      intro h
      -- 1.2.2. ¬[∅]¬ψ ∈ s:= 1.2.1
      have hin : (¬' (['∅] (¬' ψ))) ∈ s := by
        apply max_ax_contains_by_set_proof s.2 h (iff_l univ_iff_empty)
      -- 1.2.3. ¬∃χ,  ̃χ ⊆  ̃¬ψ : [∅]χ ∈ s:= proof by contradiction
        -- else by definition E we would have [∅]_¬ψ ∈ s, which contradicts with 1.2.2.
      have hne : ¬ ∃ χ , (tilde ((canonical_model_CL agents form hnpr).f.states) χ) ⊆
        (tilde ((canonical_model_CL agents form hnpr).f.states) (¬' ψ)) ∧ (['∅] χ) ∈ s:=  by
        intro hf
        cases' hf with χ hf
        cases' hf with himp hf
        simp only [tilde, setOf_subset_setOf] at himp
        have hax : ⊢' (χ →' (¬' ψ)):= ax_imp_from_ex himp
        have hf : (['∅] (¬' ψ)) ∈ s := by
          apply max_ax_contains_by_set_proof s.2 hf (derived_monoticity_rule hax)
        have := contra_contains_pr_false s.2 hf hin
        simp only at this
      -- 1.2.4. ∀χ,  ̃χ ⊆  ̃¬ψ : [∅]χ ∉ s:= 1.2.3, by first order logic.
      simp only [not_exists, not_and] at hne
      -- 1.2.5. ∀χ,  ̃χ ⊆  ̃ψ : [∅]χ ∉ s, because all s ∈ S are maximally consistent.
      simp only [h_tilde_compl hnpr ψ] at hne
      -- 1.2.6.  ̃ψ ∈ E(s)(N ):= 1.2.5, by definition E.
      simp only [hE, eq_self_iff_true, canonical_model_CL.f.states.val_eq_coe, SetLike.mem_coe,
        if_true, mem_setOf_eq]
      exact hne
  · -- 2. case G ≠ N
    apply Iff.intro
    · -- 2.1. ⇒
      -- 2.1.1. Assume  ̃ψ ∈ E(s)(G).
      intro h
      -- 2.1.2. ∃ ̃χ ⊆  ̃ψ : [G]χ ∈ s:= 2.1.1, by definition E.
      simp only [hE, hG, canonical_model_CL.f.states.val_eq_coe, SetLike.mem_coe, if_false
                  mem_setOf_eq] at h
      -- 2.1.3. ⊢ χ → ψ:= 2.1.2.
      cases' h with χ h
      cases' h with himp h
      simp only [tilde, setOf_subset_setOf] at himp
      have hax : ⊢' (χ →' ψ):= ax_imp_from_ex himp
      -- 2.1.4. [G]ψ ∈ s:= 2.1.2 & 2.1.3, by lemma 2.
      apply max_ax_contains_by_set_proof s.2 h (derived_monoticity_rule hax)
    · -- 2.2. ⇐ is immediate by definition.
      simp only [hE, hG, canonical_model_CL.f.states.val_eq_coe, SetLike.mem_coe, if_false,
        mem_setOf_eq]
      clear hE
      intro h
      apply Exists.intro ψ
      simp only [tilde, setOf_subset_setOf, imp_self, implies_true, true_and]
      exact h

-- Extra Helper Lemmas
----------------------------------------------------------
 -- tilde phi Sf = S, when M is the defined canonical model
@[simp] lemma tilde_univ {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {cl : form → Finset (form)} {φ : form} :
  (tilde (canonical_model_CL agents form hnpr).f.states
    (phi_X_set (univ : Set (S_f (canonical_model_CL agents form hnpr) cl φ)))) =
  (univ : Set (canonical_model_CL agents form hnpr).f.states) := by
  unfold tilde
  ext1 x
  apply iff_of_true _ trivial
  rw [mem_setOf_eq]
  apply max_ax_contains_taut x.2
  apply univ_disjunct_provability

lemma phi_X_list_unique {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {cl : form → Finset (form)} {φ : form}
  (hcl : ∀ χ, χ ∈ cl φ → ∃ ψ, (ψ ∈ cl φ ∧ ⊢' (ψ ↔' (¬' χ))))
  {sfs tfs : List (S_f (canonical_model_CL agents form hnpr) cl φ)}
  (hdis : sfs.Disjoint tfs) :
  ⊢' ((finite_disjunction (phi_X_list sfs)) →' (¬' (finite_disjunction (phi_X_list tfs)))) := by
  induction' sfs with sf sfs ihsfs generalizing tfs
  · simp only [phi_X_list, finite_disjunction, explosion]
  · simp only [phi_X_list, finite_disjunction]
    apply or_cases
    -- ⊢ phi sf → ¬ phi tfs
    · induction' tfs with tf tfs ihtfs
      · simp only [phi_X_list, finite_disjunction]
        exact mp _ _ (p1 _ _) iden
      · simp only [List.disjoint_cons_left, and_imp, List.disjoint_cons_right, finite_disjunction,
        Bool.not_eq_true, List.mem_cons] at *
        -- ⊢ phi tfs → ¬ phi sf ⇒ ⊢ phi sf → ¬ phi tfs
        -- ⊢ phi tfs → ¬ phi sf ⇒ ⊢ phi sf → ¬ phi tfs
        apply contrapos.mp
        apply cut (dne)
        apply or_cases
        -- ⊢ phi tf → ¬ phi sf
        · apply unique_s_f hcl
          by_contra h
          simp only [h, true_or, not_true_eq_false, false_and] at hdis
        -- ⊢ phi tfs' → ¬ phi sf (proved with ihtfs)
        · rw [←contrapos]
          apply cut
          apply dne
          apply ihtfs
          exact hdis.2.1
          exact hdis.2.2
    -- ⊢ phi sfs' → ¬ phi tfs (proved with ihsfs)
    · apply ihsfs
      apply List.disjoint_of_disjoint_cons_left hdis

lemma phi_X_finset_unique {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {cl : form → Finset (form)} {φ : form}
  (hcl : ∀ χ, χ ∈ cl φ → ∃ ψ, (ψ ∈ cl φ ∧ ⊢' (ψ ↔' (¬' χ))))
  {X Y : Finset (S_f (canonical_model_CL agents form hnpr) cl φ)} (hXY : X ∩ Y = ∅) :
  ⊢' ((phi_X_finset X) →' ¬' (phi_X_finset (Y))) := by
  unfold phi_X_finset
  apply phi_X_list_unique hcl
  rw [List.disjoint_left]
  intro f hf
  simp only [Finset.mem_toList, ax_and] at *
  by_contra h
  exact Finset.eq_empty_iff_forall_not_mem.mp hXY f (Finset.mem_inter_of_mem hf h)

lemma phi_X_set_unique {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {cl : form → Finset (form)} {φ : form}
  (hcl : ∀ χ, χ ∈ cl φ → ∃ ψ, (ψ ∈ cl φ ∧ ⊢' (ψ ↔' (¬' χ))))
  {X Y : Set (S_f (canonical_model_CL agents form hnpr) cl φ)} (hXY : X ∩ Y = ∅) :
  ⊢' ((phi_X_set X) →' ¬' (phi_X_set (Y))) := by
  unfold phi_X_set
  apply phi_X_finset_unique hcl
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro f hf
  simp only [Finset.mem_inter, Finite.mem_toFinset] at *
  exact eq_empty_iff_forall_not_mem.mp hXY f ((mem_inter_iff f X Y).mpr hf)

lemma phi_X_list_inter {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {cl : form → Finset (form)} {φ : form}
  (hcl : ∀ χ, χ ∈ cl φ → ∃ ψ, (ψ ∈ cl φ ∧ ⊢' (ψ ↔' (¬' χ))))
  {X Y : List (S_f (canonical_model_CL agents form hnpr) cl φ)}
  (hX : List.Nodup X) (hY : List.Nodup Y) :
  ⊢' (finite_disjunction (phi_X_list X)→' finite_disjunction (phi_X_list Y) →'
        finite_disjunction (phi_X_list (X ∩ Y))) := by
  induction' X with x X ihx
  · simp only [phi_X_list, finite_disjunction, explosion]
  · simp only [finite_disjunction]
    apply or_cases
    · cases' (Classical.em (x ∈ Y)) with h h
      · apply cut
        apply iff_l
        apply phi_X_list_single
        apply cut _ (p1 _ _)
        apply imp_finite_disjunction_subset
        apply phi_X_list_subset
        simp only [List.cons_subset, List.mem_inter_iff, Bool.not_eq_true, List.mem_cons, true_or,
          true_and, List.nil_subset, and_true]
        exact h
      · apply cut
        apply iff_l
        apply phi_X_list_single
        apply cut1
        apply phi_X_list_unique hcl
        exact List.singleton_disjoint.mpr h
        exact explosion
    · simp only [List.nodup_cons] at hX
      apply cut1
      apply ihx
      exact hX.right
      apply imp_finite_disjunction_subset
      apply phi_X_list_subset
      intro y hy
      simp only [List.mem_inter_iff, Bool.not_eq_true, List.mem_cons] at *
      apply And.intro
      apply Or.intro_right
      exact hy.1
      exact hy.2

lemma phi_X_finset_inter {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {cl : form → Finset (form)} {φ : form}
  (hcl : ∀ χ, χ ∈ cl φ → ∃ ψ, (ψ ∈ cl φ ∧ ⊢' (ψ ↔' (¬' χ))))
  {X Y : Finset (S_f (canonical_model_CL agents form hnpr) cl φ)} :
  ⊢' ((phi_X_finset X) →' phi_X_finset Y →' (phi_X_finset (X ∩ Y))) := by
  unfold phi_X_finset
  apply cut1
  apply phi_X_list_inter hcl
  repeat · exact Finset.nodup_toList _
  apply imp_finite_disjunction_subset
  apply phi_X_list_subset
  intro x hx
  simp only [List.mem_inter_iff, Finset.mem_toList, Finset.mem_inter] at *
  exact hx

set_option maxHeartbeats 4000000

lemma phi_X_set_inter {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {cl : form → Finset (form)} {φ : form}
  (hcl : ∀ χ, χ ∈ cl φ → ∃ ψ, (ψ ∈ cl φ ∧ ⊢' (ψ ↔' (¬' χ))))
  (X Y : Set (S_f (canonical_model_CL agents form hnpr) cl φ)) :
  ⊢' ((phi_X_set X) →' (phi_X_set Y) →' (phi_X_set (X ∩ Y))) := by
  unfold phi_X_set
  apply cut1
  apply phi_X_finset_inter hcl
  apply phi_X_subset_Y_imp
  intro x hx
  simp only [Finite.mem_toFinset, mem_inter_iff, Finset.mem_inter] at *
  exact hx

end lemmas

----------------------------------------------------------
-- Effectivity
----------------------------------------------------------

def E_f {agents form : Type} [Nonempty agents]
[Pformula_ax form] [CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {cl : form → Finset (form)} {φ : form} :
  (S_f (canonical_model_CL agents form hnpr) cl φ) → (Set agents) →
    (Set (Set (S_f (canonical_model_CL agents form hnpr) cl φ))) :=
λ sf G => {X | ite (G = univ)
  -- condition G = N
  -- ∃t ∈ S, sf = tf and  ̃φX ∈ E(t)(N)
  (∃ t, sf = (s_f cl φ t) ∧ (tilde (canonical_model_CL agents form hnpr).f.states (phi_X_set X)) ∈
    (canonical_model_CL agents form hnpr).f.E.E (t) (G))
  -- condition G ≠ N
  -- ∀t ∈ S, sf = tf ⇒  ̃phiX ∈ E(t)(G)
  (∀ t, sf = (s_f cl φ t) → (tilde (canonical_model_CL agents form hnpr).f.states (phi_X_set X)) ∈
    (canonical_model_CL agents form hnpr).f.E.E (t) (G))}


----------------------------------------------------------
-- Playability
----------------------------------------------------------
-- Ef (sf) is live: ∀G ⊆ N : ∅ ∉ Ef (sf)(G)
lemma Ef_liveness {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {cl : form → Finset (form)} {φ : form}
  (sf : S_f (canonical_model_CL agents form hnpr) cl φ) (G : Set (agents)) :
  ∅ ∉ (E_f sf G) :=  by
  let M := canonical_model_CL agents form hnpr
  -- 1.1. First we note that  ̃φ∅ =  ̃⊥ = ∅. Proved by tilde_phi_empty
  -- 1.2. Assume by contradiction ∅ ∈ Ef (sf)(G).
  intro hf
  unfold E_f at hf
  split_ifs at hf with h
  -- 1.3. Case: G = N
  · -- 1.3.1. ∃t ∈ S, sf = tf and  ̃φ∅ ∈ E(t)(N):= 1.2, by definition Ef .
    simp only [h, mem_setOf_eq] at hf
    -- 1.3.2. ∃t ∈ S, sf = tf and ∅ ∈ E(t)(N):= 1.3.1 & 1.1.
    rw [tilde_phi_empty] at hf
    cases' hf with t hf
    -- 1.3.3. ∀t, ∅ ∉ E(t)(N) because E(t) is live.
    have hlive := M.f.E.liveness t univ
    -- 1.3.4. Contradiction from 1.3.2 & 1.3.3.
    exact hlive hf.right
  -- 1.4. Case: G ≠ N
  · -- 1.4.1. ∀t ∈ S, sf = tf ⇒  ̃φ∅ ∈ E(t)(G):= 1.2, by definition Ef
    simp only [mem_setOf_eq] at hf
    -- 1.4.2. ∀t ∈ S, sf = tf ⇒ ∅ ∈ E(t)(G):= 1.4.1 & 1.1
    rw [tilde_phi_empty] at hf
    -- 1.4.3. ∅ ∈ E(s)(G):= 1.4.2
    cases' (s_f_to_s sf) with s hs
    specialize hf s (sf_eq_s_f @hs)
    -- 1.4.4. ∅ ∉ E(s)(G) because E(s) is live.
    have hlive := M.f.E.liveness s G
    -- 1.4.5. Contradiction from 1.4.3 & 1.4.4.
    exact hlive hf

-- 2. Ef (sf ) is safe: ∀G ⊆ N : Sf ∈ Ef (sf )(G)
lemma Ef_safety {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {cl : form → Finset (form)} {φ : form}
  (sf : S_f (canonical_model_CL agents form hnpr) cl φ) (G : Set (agents)) :
  univ ∈ E_f sf G := by
  let M := canonical_model_CL agents form hnpr
  -- 2.1. First we note that  ̃φSf =  ̃⊤ = SC′:= Lemma 4. Proved by tilde_univ.
  cases' (s_f_to_s sf) with s hs
  -- 2.2. Case: G = N
  cases' Classical.em (G = univ) with hG hG
  · -- 2.2.1. Sf ∈ Ef (sf )(N ) iff ∃t ∈ SC′, sf = tf and  ̃φSf ∈ EC′(t)(N ), by definition Ef .
    simp only [E_f, hG, eq_self_iff_true, if_true, mem_setOf_eq]
    -- 2.2.2. Sf ∈ Ef (sf )(N ) iff ∃t ∈ SC′, sf = tf and SC′ ∈ EC′(t)(N ):= 2.1 & 2.2.1.
    rw [tilde_univ]
    -- 2.2.3. ∃t ∈ SC′ , sf = tf and S ∈ EC′ (t)(N ), when t = s, because SC′ ∈ EC′ (t)(N )
      -- because EC′ is safe.
    apply Exists.intro s
    -- 2.2.4. Sf ∈ Ef sf )(N ):= 2.2.2 & 2.2.3.
    exact ⟨sf_eq_s_f @hs, M.f.E.safety s univ⟩
  -- 2.3. Case: G ≠ N
  · -- 2.3.1. Sf ∈ Ef (sf )(G) iff ∀t ∈ SC′ , sf = tf ⇒  ̃φSf ∈ EC′ (t)(G), by definition Ef .
    simp only [E_f, hG, if_false, mem_setOf_eq]
    -- 2.3.2. Sf ∈ Ef (sf )(G) iff ∀t ∈ SC′ , sf = tf ⇒ SC′ ∈ EC′ (t)(G):= 2.1 & 2.3.1.
    rw [tilde_univ]
    -- Sf ∈ Ef (sf )(G):= 2.3.2, because EC′ (s) is safe, so ∀t, SC′ ∈ EC′ (t)(G).
    intro t _
    exact M.f.E.safety t G

-- 3. Ef (sf) is N-maximal: ∀X ⊆ Sf : Xᶜ ∉ Ef(sf)(∅) ⇒ X ∈ Ef(sf)(N)
lemma Ef_nmax {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {cl : form → Finset (form)} {φ : form}
  (hcl : ∀ χ, χ ∈ cl φ → ∃ ψ, (ψ ∈ cl φ ∧ ⊢' (ψ ↔' (¬' χ)))) :
  N_max (@E_f agents form ha pf clf hnpr cl φ)  := by
  let M := canonical_model_CL agents form hnpr
  -- 3.1. Assume some X ⊆ Sf such that Xᶜ ∉ Ef(sf)(∅).
  intro sf X hXc
  -- 3.2. ¬(Xᶜ ∈ Ef sf ∅) := 3.1.
  -- 3.3. ¬(∀t ∈ SC′, sf = tf ⇒ ~φXᶜ ∈ EC′(t)(∅)):= 3.2, by definition Ef .
  simp only [E_f, empty_ne_univ, ite_false, mem_setOf_eq, not_forall, ite_true] at *
  -- 3.4. ∃t ∈ SC′, sf = tf and ~φXᶜ ∉ EC′(t)(∅):= 3.3, by first order logic.
  simp only [not_forall, exists_prop] at hXc
  obtain ⟨s, hs, hXc⟩ := hXc
  -- 3.5. Note that ⊢ φX ↔ ¬φX := Lemma 4 and Lemma 5.
  have h_tilde: tilde (M.f.states) (phi_X_set Xᶜ) = tilde (M.f.states) (¬' (phi_X_set X)):= by
    unfold tilde phi_X_set
    ext1 u
    apply Iff.intro
    · intro hu
      apply max_ax_contains_by_set_proof u.2 hu (phi_X_set_unique hcl (compl_inter_self X))
    · intro hu
      apply max_ax_contains_by_set_proof u.2 hu
      apply (phi_X_set_disjunct_of_disjuncts _ _).mpr
      rw [(union_compl_self X)]
      apply univ_disjunct_provability
  -- 3.6. ∃t ∈ SC′, sf = tf and ~¬φX ∉ EC′(t)(∅)):= 3.4 & 3.5
  rw [h_tilde] at hXc
  -- 3.7. ∃t ∈ SC′, sf = tf and (~φX)ᶜ ∉ EC′(t)(∅)):= 3.6
    -- because all s ∈ S are maximally consistent.
  rw [h_tilde_compl hnpr] at hXc
  -- 3.8. ∃t ∈ SC′, sf = tf and  ̃φX ∈ EC′ ∈ EC′(t)(N)), when s = t from 3.7
    --  because EC′(s) is N-maximal
  apply Exists.intro s
  -- 3.9. Ef (sf )(N):= 3.8, by definition Ef .
  exact ⟨hs, M.f.E.N_max s (tilde (M.f.states) (phi_X_set X)) hXc⟩


-- 4. Ef (sf) is outcome monotonic: ∀G ⊆ N, ∀X ⊆ Y ⊆ Sf : X ∈ Ef (sf)(G) ⇒ Y ∈ Ef (sf)(G)
lemma Ef_mono {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {cl : form → Finset (form)} {φ : form}
  (sf : S_f (canonical_model_CL agents form hnpr) cl φ) {G : Set (agents)}
  {X Y : Set _} (hXY : X ⊆ Y) (hX : X ∈ E_f sf G) : Y ∈ E_f sf G := by
  let M := canonical_model_CL agents form hnpr
  -- 4.1. Let G be some G ⊆ N and X and Y be some X ⊆ Y ⊆ Sf . Assume X ∈ Ef (sf )(G).
  -- 4.2. First we note that ∀s ∈ SC′ , ∀G ⊆ N,  ̃φX ∈ EC′(s)(G) ⇒  ̃φY ∈ EC′(s)(G)
  have himp : ∀ s G, (tilde (M.f.states) (phi_X_set X)) ∈ M.f.E.E s G →
    (tilde (M.f.states) (phi_X_set Y)) ∈ M.f.E.E s G := by
    -- 4.2.1. ⊢ φX → φY := 4.1 (X ⊆ Y ).
    have hax : ⊢' ((phi_X_set X) →' (phi_X_set Y)) := phi_X_set_subset_Y_imp hXY
    -- 4.2.2.  ̃φX ⊆  ̃φY := 4.3.1, because all s ∈ SC′ are maximally consistent.
    have h_phiXY : (tilde (M.f.states) (phi_X_set X)) ⊆ (tilde (M.f.states) (phi_X_set Y)) :=
      λ t ht => by apply max_ax_contains_by_set_proof t.2 ht hax
    -- 4.2.3. ∀s ∈ SC′ , ∀G ⊆ N,  ̃φX ∈ EC′ (s)(G) ⇒  ̃φY ∈ EC′ (s)(G):= 4.2.2
      --  because EC′ (s) is outcome monotonic.
    exact λ s G => M.f.E.mono s G _ _ h_phiXY
  -- 4.3. Case G = N
  cases' Classical.em (G = univ) with hG hG
  · -- 4.3.1. ∃t ∈ SC′, sf = tf and  ̃φX ∈ EC′ (t)(N ):= 4.1, by definition Ef .
    simp only [E_f, hG, eq_self_iff_true, mem_mk, if_true, mem_setOf_eq,
                eq_self_iff_true, if_true, mem_setOf_eq] at *
    -- 4.3.2. ∃t ∈ SC′, sf = tf and  ̃φY ∈ EC′ (t)(N ):= 4.2 & 4.3.1.
    obtain ⟨t, ⟨ht, hX⟩⟩ := hX
    have hY : tilde M.f.states (phi_X_set Y) ∈ M.f.E.E t univ := himp _ _ hX
    -- 4.3.3. Y ∈ Ef (sf )(N ):= 4.2.2, by definition Ef .
    apply Exists.intro t
    exact ⟨ht, hY⟩
  -- 4.4. Case: G ≠ N
  · -- 4.4.1. ∀t ∈ SC′, sf = tf ⇒  ̃φX ∈ EC′(t)(N ):= 4.1, by definition Ef .
    simp only [E_f, hG, mem_setOf_eq, if_false, not_false_iff] at *
    -- 4.4.2. ∀t ∈ SC′, sf = tf ⇒  ̃φY ∈ EC′(t)(N ):= 4.2 & 4.4.1.

    -- 4.4.3. Y ∈ Ef (sf )(G):= 4.4.2, by definition Ef .
    intro t ht
    exact himp t G (hX t @ht)

-- 5.2. First we note that ∀s ∈ SC′ , ∀G, F ⊆ N,such that G ∩ F = ∅
  --  ̃φX ∈ EC′ (s)(G) ⇒  ̃φY ∈ EC′ (s)(F ) ⇒  ̃φX∩Y ∈ EC′ (s)(G ∪ F ).
lemma Ef_superadd_helper {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {cl : form → Finset (form)} {φ : form}
  (hcl : ∀ χ, χ ∈ cl φ → ∃ ψ, (ψ ∈ cl φ ∧ ⊢' (ψ ↔' (¬' χ))))
  (s : (canonical_model_CL agents form hnpr).f.states) (G F : Set (agents))
  (X Y : Set (S_f (canonical_model_CL agents form hnpr) cl φ)) (hGF : G ∩ F = ∅)
  (hG : (tilde ((canonical_model_CL agents form hnpr).f.states) (phi_X_set X)) ∈
    (canonical_model_CL agents form hnpr).f.E.E s G)
  (hF : (tilde ((canonical_model_CL agents form hnpr).f.states) (phi_X_set Y)) ∈
    (canonical_model_CL agents form hnpr).f.E.E s F) :
  (tilde ((canonical_model_CL agents form hnpr).f.states) (phi_X_set (X ∩ Y))) ∈
    (canonical_model_CL agents form hnpr).f.E.E s (G ∪ F) := by
  let M := canonical_model_CL agents form hnpr
  -- 5.2.1. Let s be some s ∈ S. Let G, F , be some G, F ⊂ N where G ∩ F = ∅.
    -- Assume  ̃φX ∈ EC′ (s)(G) and  ̃φY ∈ EC′ (s)(F ).
  -- 5.2.2.  ̃φX ∩  ̃φY ∈ EC′(s)(G ∪ F ):= 5.2.1, because EC′ (s) is supperadditive.
  have hsuperadd := ((canonical_model_CL agents form hnpr).f.E.superadd) s G F _ _ hG hF hGF
  -- 5.2.3.  ̃φX∩Y ∈ EC′ (s)(G ∪ F ):= 5.2.2, because  ̃φX ∩  ̃φY =  ̃φX∩Y .
  have h_tilde_eq : tilde (M.f.states) (phi_X_set X) ∩ tilde (M.f.states) (phi_X_set Y) =
    tilde (M.f.states) (phi_X_set (X ∩ Y)):= by
    ext1 s
    simp only [tilde, mem_inter_iff, mem_setOf_eq]
    apply Iff.intro
    · intro h
      apply max_ax_contains_by_set_proof_2h s.2 h.1 h.2
      apply phi_X_set_inter hcl
    · intro h
      apply And.intro
      repeat
      · apply max_ax_contains_by_set_proof s.2 h
        apply phi_X_set_subset_Y_imp
        simp only [inter_subset_left]
  -- 5.2.3.  ̃φX∩Y ∈ EC′ (s)(G ∪ F ):= 5.2.2, because  ̃φX ∩  ̃φY =  ̃φX∩Y .
  rw [h_tilde_eq] at hsuperadd
  exact hsuperadd


-- 5. Ef (sf ) is superadditive ∀G, F ⊆ N (where G ∩ F = ∅), ∀X, Y ⊆ Sf :
  -- X ∈ Ef (sf )(G) and Y ∈ Ef (sf )(F ) ⇒ X ∩ Y ∈ Ef (sf )(G ∪ F )
lemma Ef_superadd {agents form : Type} [ha : Nonempty agents]
  [pf : Pformula_ax form] [clf : CLformula agents form]
  {hnpr : ¬ ⊢' (⊥' : form)} {cl : form → Finset (form)} {φ : form}
  (hcl : ∀ χ, χ ∈ cl φ → ∃ ψ, (ψ ∈ cl φ ∧ ⊢' (ψ ↔' (¬' χ))))
  (sf : S_f (canonical_model_CL agents form hnpr) cl φ) {G F : Set (agents)}
  {X Y : Set _} (hX : X ∈ E_f sf G ) (hY : Y ∈ E_f sf F) (hGF : G ∩ F = ∅) :
  X ∩ Y ∈ E_f sf (G ∪ F) := by
  let M := canonical_model_CL agents form hnpr
  -- 5.1. Let G, F be some G, F ⊆ N , such that G ∩ F = ∅.
    -- Let X, Y be some X, Y ⊆ SC′ such that X ∈ Ef (sf )(G) and Y ∈ Ef (sf )(F ).
  -- 5.2. First we note that ∀s ∈ SC′ , ∀G, F ⊆ N,such that G ∩ F = ∅
    --  ̃φX ∈ EC′ (s)(G) ⇒  ̃φY ∈ EC′ (s)(F ) ⇒  ̃φX∩Y ∈ EC′ (s)(G ∪ F)
  have hint := @Ef_superadd_helper _ form ha pf clf hnpr _ _ hcl

  -- 5.3. Case G = N or F = N :
  have h_G_or_F_univ : ∀ X' Y', X' ∈ E_f sf univ → Y' ∈ E_f sf ∅ → (X' ∩ Y') ∈ E_f sf univ:= by
    -- 5.3.1. Note that the G or F that is not N , must be ∅.
      -- Thus, rename X & Y to X′ & Y ′, such that X′ ∈ Ef (sf )(N ) and Y ′ ∈ Ef (sf )(∅).
    clear hX hY
    intro X' Y'
    -- 5.3.2. ∃t ∈ SC′, sf = tf and  ̃φX′ ∈ EC′(t)(N ), and ∀u ∈ SC′, sf = tf ⇒
      --  ̃φY ′ ∈ EC′(t)(∅) from 5.3.1 by definition Ef.
    intro hX hY
    -- 5.3.3. ∃t ∈ SC′, sf = tf and  ̃φX′∩Y ′ ∈ EC′(t)(N ):= 5.2 & 5.3.3.
    simp only [E_f, empty_ne_univ, eq_self_iff_true, if_true, mem_setOf_eq, if_false] at *
    cases' hX with t hX
    specialize hint t univ ∅ X' Y' top_inf_eq hX.right (hY t hX.left)
    rw [univ_union] at hint
    -- 5.3.4. X′ ∩ Y ′ ∈ Ef (sf )(N = G′ ∪ F ′):= 5.3.3, by definition Ef
    exact ⟨t, ⟨hX.left, hint⟩⟩
  cases' Classical.em (G = univ) with h h
  -- case G = N
  · simp only [h, univ_union, univ_inter, eq_self_iff_true] at *
    simp only [hGF, eq_self_iff_true] at *
    exact h_G_or_F_univ X Y hX hY
  -- case G ≠ N
  · cases' Classical.em (F = univ) with h_1 h_1
    -- case F = N
    · simp only [h_1, union_univ, inter_univ, eq_self_iff_true] at *
      simp only [hGF, eq_self_iff_true] at *
      rw [inter_comm X Y]
      exact h_G_or_F_univ Y X hY hX
    -- 5.4. Case G ≠ N and F ≠ N
    · -- 5.4.1. ∀t ∈ SC′, sf = tf ⇒  ̃φX ∈ EC′(t)(G), and
        -- ∀t ∈ SC′, sf = tf ⇒  ̃φY ∈ EC′(t)(F ):= 5.1, by definition Ef .
      simp only [E_f, h, h_1, mem_setOf_eq, if_false, eq_self_iff_true, if_true
                  forall_exists_index, and_imp, not_false_iff] at *
      cases' Classical.em (G ∪ F = univ) with h_2 h_2
      -- 5.4.2. Case G ∪ F = N : ∃t ∈ SC′, sf = tf and  ̃φX∩Y ∈ EC′(s)(G ∪ F)
        -- when t = s from 5.2 & 5.4.1. Thus, X ∩ Y ∈ Ef (sf )(G ∪ F = N ), by definition Ef.
      · obtain ⟨s, hs⟩  := s_f_to_s sf
        specialize hint s G F X Y hGF (hX s (sf_eq_s_f @hs)) (hY s (sf_eq_s_f @hs))
        simp only [h_2, eq_self_iff_true, if_true] at *
        exact ⟨s, ⟨(sf_eq_s_f @hs), hint⟩⟩
      -- 5.4.3. Case G ∪ F ≠ N : ∀t ∈ SC′, sf = tf ⇒  ̃φX∩Y ∈ EC′(t)(G ∪ F ):= 5.2 & 5.4.1.
        -- Thus X ∩ Y ∈ Ef (sf )(G ∪ F ), by definition Ef .
      · simp only [h_2, if_false]
        exact λ t ht => hint t G F X Y hGF (hX t @ht) (hY t @ht)

----------------------------------------------------------
-- Building the coplete filtered model
----------------------------------------------------------

noncomputable def filtered_modelECL_E (agents form : Type) [Nonempty agents]
  [Pformula_ax form] [CLformula agents form] [Kformula agents form]
  (hnpr : ¬ ⊢' (⊥' : form)) (cl : form → Finset (form))
  (hcl : ∀ φ χ, χ ∈ cl φ → ∃ ψ, (ψ ∈ cl φ ∧ ⊢' (ψ ↔' (¬' χ)))) (φ : form) :
  playable_effectivity_struct agents (S_f (canonical_model_CL agents form hnpr) cl φ) :=
{ E          := E_f
  liveness   := Ef_liveness
  safety     := Ef_safety
  N_max      := Ef_nmax (hcl φ)
  mono       := Ef_mono
  superadd   := Ef_superadd (hcl φ) }


  noncomputable def filtered_modelECL (agents form : Type) [Nonempty agents]
  [Pformula_ax form] [CLformula agents form] [Kformula agents form]
  (hnpr : ¬ ⊢' (⊥' : form)) (cl : form → Finset (form))
  (hcl : ∀ φ χ, χ ∈ cl φ → ∃ ψ, (ψ ∈ cl φ ∧ ⊢' (ψ ↔' (¬' χ)))) (φ : form) :
  modelECL agents :=
{ f :=
  { states := S_f (canonical_model_CL agents form hnpr) cl φ
    hs := canonical.S_f.Nonempty _ _ _
    E := truly_playable_from_finite (filtered_modelECL_E agents form hnpr cl hcl φ)
    rel   := λ i s => {t | {φ | K' (i) (φ) ∈ s} = {φ | K' (i) (φ) ∈ t}}
    rfl   := λ _ _ => rfl
    sym   := λ _ _ _ ht => Eq.symm ht
    trans := λ _ _ _ _ hst htu => Eq.trans hst htu }
  v := λ  n => {s | (Pformula.var n) ∈ s.1.1} }

end canonical
