import syntax.consistency
import tactic.induction

-- -- Motivation: easier to prove Lean's `and` than in `ax`
-- @[simp] lemma ax_and {form : Type} [ft : formula form] {φ ψ : form} :
--   ax (φ ∧' ψ) ↔ ax φ ∧ ax ψ :=
-- ⟨λ h, ⟨mp _ _ (p5 _ _) h, mp _ _ (p6 _ _) h⟩,
--  λ ⟨h1, h2⟩, mp _ _ (mp _ _ (p4 _ _) h1) h2⟩

-- -- Motivation: corresponds to Lean's `iff.intro`
-- @[simp] lemma ax_iff_intro {form : Type} [ft : formula form] {φ ψ : form}
--   (h1 : ax (φ →' ψ)) (h2 : ax (ψ →' φ)) : ax (φ ↔' ψ) :=
-- begin
--   simp only [ft.iffdef, ax_and],
--   exact ⟨h1, h2⟩
-- end

-- -- Motivation: corresponds more or less to Lean's `imp_congr`
-- @[simp] lemma ax_imp_congr_left {form : Type} [ft : formula form] {φ φ' ψ : form}
--   (hl : ax (φ ↔' φ')) : ax ((φ →' ψ) ↔' (φ' →' ψ)) :=
-- ax_iff_intro
--   (mp _ _ (imp_switch hs1) (iff_r hl))
--   (mp _ _ (imp_switch hs1) (iff_l hl))

-- /-- `φ` is provable iff `ψ` is, if it's provable `φ` and `ψ` are equivalent.

-- If we have the deduction theorem, the converse is also true: formulas are provably equivalent iff
-- their provability is equivalent. -/
-- -- Motivation: allows rewriting after proving equivalence
-- lemma ax_iff_mp {form : Type} [ft : formula form] {φ ψ : form} (hiff : ax (φ ↔' ψ)) :
--   ax φ ↔ ax ψ :=
-- ⟨mp _ _ (iff_l hiff), mp _ _ (iff_r hiff)⟩

-- -- Motivation: for simplication in combination with `ax_iff_mp`
-- @[simp] lemma ax_and_top_iff {form : Type} [ft : formula form] {φ : form} :
--   ax ((φ ∧' ⊤') ↔' φ) :=
-- by simpa [ft.topdef, ft.notdef] using @phi_and_true _ _ φ

-- -- Motivation: for simplication in combination with `ax_iff_mp`
-- @[simp] lemma ax_top_imp_iff {form : Type} [ft : formula form] (φ : form) :
--   ax ((⊤' →' φ) ↔' φ) :=
-- ax_iff_intro
--   (combS combI (combK prtrue)) -- λ h, h prtrue
--   (p1 _ _)

-- -- Motivation: useful simplification lemma
-- @[simp] lemma ax_top_imp {form : Type} [ft : formula form] {φ : form} :
--   ax (⊤' →' φ) ↔ ax φ :=
-- ax_iff_mp (ax_top_imp_iff φ)

-- -- Motivation: corresponds to Lean's `false.elim`
-- @[simp] lemma ax_bot_elim {form : Type} [ft : formula form] {φ : form} :
--   ax (⊥' →' φ) :=
-- (ax_iff_mp (ax_imp_congr_left contra_equiv_false)).mp (p5 _ _)

-- Motivation: a lot of places assume `¬ ax ⊥'` so it's worth trying to reduce these assumptions.
lemma ax_consistent.not_ax_bot {form : Type} [ft : formula form] {s : set form}
  (h : ax_consistent s) : ¬ ax (⊥' : form) :=
begin
  simpa [ax_consistent, finite_ax_consistent] using (h list.nil (λ _ h, h.elim))
end

/-- An empty set of formulas is consistent iff the theory is consistent. -/
-- Motivation: a lot of places assume `¬ ax ⊥'` so it's worth trying to reduce these assumptions.
@[simp] lemma ax_consistent_empty {form : Type} [ft : formula form] :
  ax_consistent ({} : set form) ↔ ¬ ax (⊥' : form) :=
begin
  split; intro h,
  { exact h.not_ax_bot },
  { intros fs hfs,
    cases fs with f fs,
    { simpa [ax_consistent, finite_ax_consistent] using hfs },
    { cases hfs f (list.mem_cons_self _ _) } }
end

/-- If there is any formula that cannot be proven, the theory is consistent. -/
-- Motivation: a lot of places assume `¬ ax ⊥'` so it's worth trying to reduce these assumptions.
lemma consistent_of_not_ax {form : Type} [ft : formula form] {φ : form}
  (hφ : ¬ ax φ) : ¬ ax (⊥' : form) :=
mt (mp _ _ ax_bot_elim) hφ

lemma contra_con_cons {form : Type} [ft : formula form] (fs gs : list (form)) (x y : form) 
  (hax : ax (y ↔' ¬' x)) (hx : x ∈ fs) (hy : y ∈ gs) :
  ax (¬' ((finite_conjunction fs) ∧' (finite_conjunction gs))) :=
begin
  induction' fs with f fs ihf,
  { finish, },
  { induction gs with g gs ihg,
    { finish, },
    { cases hx,
      { cases hy,
        { rw[←hx, ←hy],
          simp[finite_conjunction],
          rw ft.notdef,
          apply cut (iff_r and_commute),
          apply imp_and_l,
          apply cut (iff_l and_switch),
          apply cut (iff_r and_commute),
          apply imp_and_l,
          rw ←contra_iff_false_ax_not,
          rw demorgans,
          apply iff_l,
          exact hax, },
        { simp[finite_conjunction],
          rw ft.notdef,
          apply cut (iff_r and_commute),
          apply cut (iff_l and_switch),
          apply cut (iff_r and_commute),
          apply imp_and_l,
          apply cut (iff_l and_switch),
          rw ←contra_iff_false_ax_not,
          apply ihg hy, }, },
      { rw ft.notdef,
        apply cut (iff_l and_switch),
        apply cut (iff_r and_commute),
        apply cut (iff_l and_switch),
        apply cut (iff_r and_commute),
        apply imp_and_l,
        specialize @ihf ft (g :: gs) x y hax hy hx,
        rw ft.notdef at ihf,
        exact ihf, }, }, },
end

/-- A singleton set is consistent iff the theory is consistent and the formula is not disprovable.
-/
-- Motivation: `comphelper` seemed to be slightly too specific, this is a more general form I found
@[simp] lemma ax_consistent_singleton {form : Type} [ft : formula form] {φ : form} :
  ax_consistent ({φ} : set form) ↔ ¬ ax (¬' φ) :=
begin
  split,
  { intros h,
    have := h (φ :: list.nil) (by simp),
    simp only [finite_ax_consistent, ft.notdef, finite_conjunction_cons, finite_conjunction_nil]
      at ⊢ this,
    exact mt (ax_iff_mp (ax_imp_congr_left ax_and_top_iff)).2 this },
  { rintros hφ fs hfs,
    cases fs with f fs,
    { simp only [ax_consistent, finite_ax_consistent, finite_conjunction_nil, ax_top_imp] at ⊢,
      exact consistent_of_not_ax hφ },
    { intro h,
      simp only [ft.notdef] at *,
      exact hφ (mp _ _ (mp _ _ hs1 h) (fin_conj_repeat_helper hfs)) } }
end

-- Completeness helper
----------------------------------------------------------

lemma comphelper {form : Type} [ft : formula form] {φ : form} (h : ¬ ax φ) :
  ax_consistent ({¬' φ} : set form) :=
ax_consistent_singleton.mpr (mt (mp _ _ dne) h)

/-- If `φ` cannot be proved, there is a maximal consistent set containing `¬ φ` -/
-- Motivation: `lindenbaum` is applied in a few places to `comphelper`,
-- and `simp` can simplify the conditions slightly.
lemma exists_max_ax_consistent_neg_mem {form : Type} [ft : formula form] {φ : form} (hφ : ¬ ax φ) :
  ∃ (Γ : set form), max_ax_consistent Γ ∧ ¬' φ ∈ Γ :=
by simpa using lindenbaum _ (comphelper hφ)
