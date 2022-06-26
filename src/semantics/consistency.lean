------------------------------
/-
Copyright (c) 2021 Paula Neeley. All rights reserved.
Author: Paula Neeley
Following the textbook "Dynamic Epistemic Logic" by 
Hans van Ditmarsch, Wiebe van der Hoek, and Barteld Kooi
-/

-- import del.languageDEL del.syntax.syntaxDEL 
-- import del.semantics.semanticsDEL del.syntax.syntaxlemmasDEL
-- import del.syntax.soundnessDEL order.zorn data.set.basic data.list.basic
-- local attribute [instance] classical.prop_decidable

-- variables {agents : Type}
-- open prfS5
-- open S5lemma

import syntax.syntaxCL syntax.axiomsCL semantics.semanticsCL syntax.propLemmas
import data.set.basic data.set.finite order.zorn data.list.basic

open set 

variables {agents : Type}


---------------------- Consistency ----------------------


-- def sem_cons (agents: Type):= ¬ global_valid (@formCL.bot agents) 
-- attribute [class] sem_cons


-- lemma sem_consS5 : sem_cons (∅ : ctx agents) equiv_class :=
-- begin
-- rw sem_cons,
-- rw global_sem_csq,
-- push_neg,
-- let f : frame agents := 
-- { states := ℕ,
--   h := ⟨0⟩,
--   rel := λ a x y, x = y},
-- use f, let v := λ n x, true,
-- split,
-- intro a,
-- split,
-- intro x,
-- exact rfl,
-- split,
-- intros x y h1,
-- exact eq.symm h1,
-- intros x y z h1 h2,
-- exact (rfl.congr h2).mp h1,
-- use v,
-- split,
-- intros φ x h1,
-- exact false.elim h1, 
-- let x := 42,
-- use x,
-- rw forces, 
-- trivial
-- end


-- The S5 axiom system does not prove false
-- lemma nprfalse {form: Type} (ft: formula form) (h_sound: ∀ φ, ft.ax φ → global_valid φ): ¬ ft.ax (ft.bot) :=
-- begin
-- have h1 : ¬ global_valid formCL.bot → ¬ axCL formCL.bot,
-- {have h2 := soundnessS5,
-- rw ←not_imp_not at h2, exact h2},
-- apply h1, exact hax
-- end


-- lemma prnot_to_notpr (φ : form agents) (hax : sem_cons (∅ : ctx agents) equiv_class) : 
--   prfS5 ∅ (¬φ) → ¬ prfS5 ∅ φ :=
-- begin
-- intro h1, by_contradiction h2,
-- exact absurd (mp (mp pl5 contra_equiv_false) (mp (mp pl4 h2) h1)) (nprfalse hax)
-- end 


-- lemma pr_to_notprnot (φ : form agents) (hax : sem_cons (∅ : ctx agents) equiv_class) : 
--   prfS5 ∅ φ → ¬ prfS5 ∅ (¬φ) :=
-- begin
-- have h1 := prnot_to_notpr φ hax,
-- rw ←not_imp_not at h1, intro h2, apply h1, rw not_not, exact h2,
-- end 


-- finite conjunction of formulas

-- def fin_conj : list (formCL agents) → formCL agents
--   | nil     := ¬formCL.bot
--   | (φ::φs) := φ & (fin_conj φs)

-- finite conjunction of formulas
-- def finite_conjunction {formula : Type}: (formula → formula → formula) → formula → (list formula) → formula
--   | _ t list.nil   := t
--   | a t (f::fs)  := a f (finite_conjunction a t fs)

def finite_conjunction {form: Type} (ft : formula form): (list form) → form
  | list.nil   := ft.top
  | (f::fs)    := ft.and f (finite_conjunction fs)


-- a few helper lemmas about finite conjunctions
lemma fin_conj_simp {form: Type} {ft : formula form}: 
∀ ψ : form, ft.ax (ft.not (finite_conjunction ft ((ψ :: (ft.not ψ :: list.nil))))) :=
begin
intro ψ,
simp [finite_conjunction],
rw not_and_subst,
exact not_contra,
simp[topnotbot],
exact phi_and_true,
end


lemma imp_conj_imp_imp {form: Type} {ft : formula form} {Γ : set form} {φ ψ χ : form} {L : list (form)} 
  (h_and_right_imp: (∀ φ ψ χ : form, ft.ax (ft.imp (ft.and φ ψ) χ) ↔ ft.ax (ft.imp ψ (ft.imp φ χ)))): 
  ft.ax (ft.imp (finite_conjunction ft (φ::L)) ψ) ↔ ft.ax (ft.imp (finite_conjunction ft L) (ft.imp φ ψ)) :=
begin
split, 
intro h, dsimp [finite_conjunction] at h, rw h_and_right_imp at h, exact h,
intro h, dsimp [finite_conjunction], rw h_and_right_imp, exact h
end


lemma fin_conj_s_imp {form: Type} {ft : formula form} {Γ : set form} {φ b : form } {L : list form} : 
 ft.ax (ft.imp (finite_conjunction ft (φ :: L))  (ft.imp φ b)) → ft.ax (ft.imp (finite_conjunction ft L) (ft.imp φ b)) :=
begin
intro h, rw imp_conj_imp_imp at h, rw imp_imp_iff_imp at h, exact h, exact Γ, exact φ,
intros _ _ _,
exact and_right_imp,
end




lemma fin_conj_append {form: Type} {ft : formula form} {Γ : set form} {L L' : list (form)} :
  ft.ax (ft.iff (ft.and (finite_conjunction ft L') (finite_conjunction ft L)) (finite_conjunction ft (L' ++ L))) :=
begin
induction L', rw finite_conjunction,
simp [ft.iffdef, topnotbot] at *,
exact (ft.mp _ _ (ft.mp _ _ (ft.p4 _ _) (cut (ft.mp _ _ (ft.p6 _ _) and_switch') (ft.mp _ _ (ft.p5 _ _) phi_and_true'))) 
  (cut (ft.mp _ _ (ft.p6 _ _) phi_and_true') (ft.mp _ _ (ft.p5 _ _) and_switch'))),
simp [ft.iffdef, topnotbot] at *,
exact ft.mp _ _ (ft.mp _ _ (ft.p4 _ _) (cut (ft.mp _ _ (ft.p5 _ _) and_commute') (imp_and_imp (ft.mp _ _ (ft.p5 _ _) L'_ih)))) 
  (cut iden (cut (imp_and_imp (ft.mp _ _ (ft.p6 _ _) L'_ih)) (ft.mp _ _ (ft.p6 _ _) and_commute')))
end 

lemma fin_conj_append' {form: Type} {ft : formula form} {Γ : set form} {L L' : list (form)} :
  ft.ax (ft.and (ft.imp (ft.and (finite_conjunction ft L') (finite_conjunction ft L)) (finite_conjunction ft (L' ++ L))) (ft.imp (finite_conjunction ft (L' ++ L)) (ft.and (finite_conjunction ft L') (finite_conjunction ft L)))) :=
begin
induction L', rw finite_conjunction,
simp [ft.iffdef, topnotbot] at *,
exact (ft.mp _ _ (ft.mp _ _ (ft.p4 _ _) (cut (ft.mp _ _ (ft.p6 _ _) and_switch') (ft.mp _ _ (ft.p5 _ _) phi_and_true'))) 
  (cut (ft.mp _ _ (ft.p6 _ _) phi_and_true') (ft.mp _ _ (ft.p5 _ _) and_switch'))),
simp [ft.iffdef, topnotbot] at *,
exact ft.mp _ _ (ft.mp _ _ (ft.p4 _ _) (cut (ft.mp _ _ (ft.p5 _ _) and_commute') (imp_and_imp (ft.mp _ _ (ft.p5 _ _) L'_ih)))) 
  (cut iden (cut (imp_and_imp (ft.mp _ _ (ft.p6 _ _) L'_ih)) (ft.mp _ _ (ft.p6 _ _) and_commute')))
end 

-- lemma fin_conj_empty {L : list (form agents)} 
--   (hax : sem_cons (∅ : ctx agents) equiv_class) :
--   L = [] → ¬ prfS5 ∅ (fin_conj L ⊃ ⊥) :=
-- begin
-- intro h1, subst h1,
-- by_contradiction h2,
-- exact absurd (mp h2 iden) (nprfalse hax)
-- end 


-- lemma fin_conj_repeat_helper {θ : form agents} {L : list (form agents)} 
--   (hax : sem_cons (∅ : ctx agents) equiv_class) :
--   (∀ ψ ∈ L, ψ = θ) → prfS5 ∅ (θ ⊃ fin_conj L) :=
-- begin
-- intros h1, induction L,
-- exact mp pl1 iden,
-- rw fin_conj, simp at *,
-- cases h1 with h1 h2,
-- subst h1,
-- exact cut (mp double_imp pl4) (imp_and_and_imp (mp (mp pl4 iden) (L_ih h2))),
-- end


-- lemma fin_conj_repeat {φ : form agents} {L : list (form agents)}
--   (hax : sem_cons (∅ : ctx agents) equiv_class) :
--   (∀ ψ ∈ L, ψ = ¬φ) → prfS5 ∅ (¬fin_conj L) → prfS5 ∅ φ :=
-- begin
-- intros h1 h2, induction L,
-- exact absurd (mp dne h2) (nprfalse hax),
-- repeat {rw fin_conj at *}, simp at *,
-- cases h1 with h1 h3, 
-- have h5 := contrapos.mpr (fin_conj_repeat_helper hax h3),
-- subst h1,
-- exact (mp (mp pl3 (contrapos.mpr (cut h5 dne))) 
--   (contrapos.mpr (cut ((demorgans.mp) (mp (mp pl6 (iff_not and_switch)) h2)) dne)))
-- end


-- lemma fin_conj_box2 {φ ψ : form agents} {a : agents} : 
--   prfS5 ∅ (((K a φ) & K a ψ) ⊃ K a (φ & ψ)) :=
-- begin
-- exact (mp double_imp (cut2 pl6 (cut pl5 (cut (mp kdist (nec pl4)) kdist))))
-- end


-- lemma fin_conj_boxn {L : list (form agents)} {a : agents} : 
--   prfS5 ∅ ((fin_conj (list.map (K a) L)) ⊃ (K a (fin_conj L))) :=
-- begin
-- induction L,
-- exact (mp pl1 (nec prtrue)),
-- exact (cut (imp_and_imp L_ih) fin_conj_box2)
-- end


lemma listempty {form : Type} (ft: formula form) {fs : list form} {Γ : set form}:
  (∀ φ ∈ fs, φ ∈ Γ) → Γ = ∅ → fs = list.nil := 
begin
intros h1 h2,
by_contradiction h3,
have h4 := list.length_pos_of_ne_nil,
have h5 := list.exists_mem_of_length_pos,
cases h5 (h4 h3) with φ h5,
exact absurd (h1 φ h5) (set.eq_empty_iff_forall_not_mem.mp h2 φ)
end


-- Consistency for a finite set of formulas L
def finite_ax_consistent {form : Type} (ft: formula form) (fs: list (form)): 
Prop := 
  ¬ ft.ax (ft.imp (finite_conjunction ft fs) ft.bot)


-- Consistency for an arbitrary set of formulas Γ
def ax_consistent {form : Type} (ft: formula form) (Γ: set (form)) : 
Prop :=
  ∀ fs : list (form), (∀ ψ ∈ fs, ψ ∈ Γ) → (finite_ax_consistent ft fs)


-- Γ is maximally ax-consistent
def max_ax_consistent {form : Type} (ft: formula form) (Γ: set (form)):
Prop := 
  (ax_consistent ft Γ) ∧ (∀ Γ', Γ ⊂ Γ' → ¬ (ax_consistent ft Γ'))

-- lemma max_ax_top {form : Type} (ft: formula form) (Γ: set (form)) 
--   (h: max_ax_consistent ft Γ):
--   ft.top ∈ Γ :=
-- begin
--   cases h,
--   by_contradiction,
--   apply h_right (Γ ∪ {ft.top}),
--   {
--     rw set.ssubset_iff_of_subset,
--     apply exists.intro ft.top,
--     {
--       apply exists.intro,
--       { simp, },
--       { exact h, },
--     },
--     { exact subset_union_left Γ {ft.top}, },
--   },
--   {
--     intros fs hψ haxψ,
--     simp [ax_consistent, finite_ax_consistent] at *,
--     apply h_left fs,
--     intros ψ hψ',
--     apply or.elim (hψ ψ hψ'),
--     {

--     }
--   }
-- end

-- lemma fin_consistent_or_top {form : Type} (ft: formula form) (fs: list form)
--  ()

-- lemma temp {form : Type} (ft: formula form) (fs fs': list form)
--   (h: ∀ ψ, ψ ∈ fs' → (ψ = ft.top ∨ ψ ∈ fs)) :
--   ft.ax (finite_conjunction ft fs) ↔ ft.ax (finite_conjunction ft fs') :=
--   sorry

-- lemma temp2 {form : Type} (ft: formula form) (φ ψ: form)
--   (h: ft.ax φ ↔ ft.ax ψ) :
--   ∀ ϕ, ft.ax (ft.imp φ ϕ) ↔ ft.ax (ft.imp ψ ϕ) :=
--   sorry 

-- def temp3 {form : Type} (ft: formula form) : list form -> set form → list form
--   | list.nil _ := list.nil,
--   | (f::fs) Γ  :=

-- lemma ax_consistent_union_top {form : Type} (ft: formula form) (Γ: set form) 
--   (h: ax_consistent ft Γ) : ax_consistent ft (Γ ∪ {ft.top}) :=
-- begin
--   simp[ax_consistent, finite_ax_consistent] at *,
--   intros fs' hψ hf,
--   sorry,
-- end

-- lemma max_ax_top {form : Type} (ft: formula form) (Γ: set (form)) 
--   (h: max_ax_consistent ft Γ):
--   ft.top ∈ Γ :=
-- begin
--   cases h,
--   by_contradiction,
--   apply h_right (Γ ∪ {ft.top}),
--   {
--     rw set.ssubset_iff_of_subset,
--     apply exists.intro ft.top,
--     {
--       apply exists.intro,
--       { simp, },
--       { exact h, },
--     },
--     { exact subset_union_left Γ {ft.top}, },
--   },
--   {
--     exact ax_consistent_union_top ft Γ h_left,
--   }
-- end


lemma max_imp_ax {form : Type} {ft: formula form} {Γ: set form} : 
  max_ax_consistent ft Γ → ax_consistent ft Γ :=
begin
intro h1, exact h1.left
end


-- -- Lemma 5 from class notes
lemma five_helper {form : Type} {ft: formula form} :
 ∀ Γ : set form, ∀ φ : form, ∀ L : list (form), ∀ b : form, 
  (∀ ψ ∈ L, ψ ∈ Γ ∨ ψ = φ) → ft.ax (ft.imp (finite_conjunction ft L) b) → ∃ L',
  (∀ ψ ∈ L', ψ ∈ Γ) ∧ ft.ax (ft.imp (finite_conjunction ft L') (ft.imp φ b)) :=
begin
intros Γ φ L b h1 h2, 
revert b, 
induction L,
{intros b h2, existsi (list.nil : list (form)), split, 
intros ψ h3, exfalso, apply list.not_mem_nil ψ h3, 
apply imp_if_imp_imp,
exact h2,},
{
  intros b h2,
  have h1a : ∀ (ψ : form), ψ ∈ L_tl → ψ ∈ Γ ∨ ψ = φ, 
    {intros ψ h2, apply h1 ψ (list.mem_cons_of_mem L_hd h2)},
  have h1b: L_hd ∈ Γ ∨ L_hd = φ, 
    {apply h1 L_hd, left, refl},
  cases h1b,
  { 
    have h3 := and_right_imp.mp h2,
    cases L_ih h1a (ft.imp L_hd b) h3 with L' ih, existsi (L_hd::L' : list form),
    cases ih, split, intros ψ h4, cases h4,
    {
      subst h4, exact h1b, 
    },
    {
      apply ih_left ψ h4,
    },
    {
      rw imp_shift at ih_right,
      rw ←imp_conj_imp_imp at ih_right,
      exact ih_right,
      have h3 : ft.ax (ft.imp (finite_conjunction ft (L_hd::L_tl))  b), 
      exact h2, exact Γ, exact b,
      intros _ _ _,
      exact and_right_imp,
    },
  },
  {
    have h4 := and_right_imp.mp,
    have h5 : ft.ax (ft.imp (finite_conjunction ft L_tl) (ft.imp φ b)),
      from eq.subst h1b (h4 h2),
    cases L_ih h1a (ft.imp φ b) h5 with L' ih, 
    existsi (L' : list form), split, 
    exact ih.left, exact imp_imp_iff_imp.mp ih.right,
  },
},
end


lemma five {form : Type} {ft: formula form} : 
  ∀ Γ : set form, ∀ φ : form, ¬ ax_consistent ft (Γ ∪ {φ}) → ∃ L': list form,
  (∀ ψ ∈ L', ψ ∈ Γ) ∧ ft.ax (ft.imp (finite_conjunction ft L') (ft.not φ)) :=
begin
intro Γ, intro φ, intro h1, rw ax_consistent at h1, 
push_neg at h1,
cases h1 with L h1,
have h2 : (∀ ψ ∈ L, ψ ∈ Γ ∨ ψ = φ) → ft.ax (ft.imp (finite_conjunction ft L) ft.bot) → ∃ L',
  (∀ ψ ∈ L', ψ ∈ Γ) ∧ ft.ax (ft.imp (finite_conjunction ft L') (ft.imp φ ft.bot)), from five_helper Γ φ L ft.bot,
cases h1,
have h3 : (∀ (ψ : form), ψ ∈ L → ψ ∈ Γ ∨ ψ = φ), 
  {
    intros ψ this,
    have hor: ψ ∈ Γ ∨ ψ = φ, from h1_left ψ this, 
    have hor': ψ = φ ∨ ψ ∈ Γ, from or.swap hor,
    exact or.swap hor',
  },
rw finite_ax_consistent at h1_right, 
rw not_not at h1_right,
rw ft.notdef at *,
apply h2 h3,
exact h1_right,
end


-- Lemma 6 from class notes
lemma max_ax_contains_phi_or_neg  {form : Type} {ft: formula form} (Γ: set form):
max_ax_consistent ft Γ → ∀ φ : form, φ ∈ Γ ∨ (ft.not φ) ∈ Γ :=
begin
intros h1 φ, rw or_iff_not_and_not, by_contradiction h2,
cases h2 with h2l h2r,
cases h1 with h1l h1r, 
have h2 := h1r (Γ ∪ {φ}),
have h3 : ¬ax_consistent ft ({ft.not φ} ∪ Γ), 
  { 
    apply h1r,
    from set.ssubset_insert h2r,
  },
have h5 : ¬ax_consistent ft (Γ ∪ {φ}), 
  {
    apply h2,
    have heq: Γ ∪ {φ} = set.insert φ Γ, from by finish,
    rw heq,
    from set.ssubset_insert h2l,}, 
have h6 := five Γ φ _, have h7 := five Γ (ft.not φ) _, 
cases h6 with L' h6, cases h7 with L h7, cases h6 with h6l h6r,
cases h7 with h7l h7r,
have h8 := imp_and_and_imp (ft.mp _ _ (ft.mp _ _ (ft.p4 _ _) h6r) h7r),
have h12 := cut (ft.mp _ _ (ft.p6 _ _) fin_conj_append') (cut h8 (ft.mp _ _ (ft.p5 _ _) (contra_equiv_false'))),
have h13 : (∀ (ψ : form), ψ ∈ L' ++ L → ψ ∈ Γ), 
intro ψ, intro h13,
rw list.mem_append at h13, cases h13, exact h6l ψ h13, exact h7l ψ h13,
exact absurd h12 (h1l (L' ++ L) h13),
exact {φ},
rw union_comm at h3,
exact h3,
exact h5,
end


lemma max_ax_contains_phi_xor_neg {form : Type} {ft: formula form} (Γ: set form) (h: ax_consistent ft Γ) :
max_ax_consistent ft Γ ↔ ∀ φ, (φ ∈ Γ ∨ (ft.not φ) ∈ Γ) ∧ ¬(φ ∈ Γ ∧ (ft.not φ) ∈ Γ) :=
begin 
simp, split, 
intro h1, intro φ, 
split, exact max_ax_contains_phi_or_neg Γ h1 φ,
{rw ←not_and, by_contradiction h2,
cases h2 with h2 h3,
simp [ax_consistent] at h,

let l := (φ :: (ft.not φ :: list.nil)),
specialize h (l), simp at *,
have h4 : (∀ (ψ : form ), ψ = φ ∨ ψ = ft.not φ → ψ ∈ Γ), 
{intros ψ h4, cases h4, subst h4, exact h2, subst h4, exact h3},
have h5 : ft.ax (ft.not (finite_conjunction ft l)), from fin_conj_simp φ, 
have h6: _, from h h2 h3,
simp [finite_ax_consistent] at h6,
simp [ft.notdef] at h5,
exact h6 h5,
},
intro h1, split, exact h,
intros Γ' h2,
have h3 : Γ ⊆ Γ' ∧ ¬ Γ' ⊆ Γ, from h2,
cases h3,
rw set.not_subset at h3_right,
apply (exists.elim h3_right), simp, intros ψ h4 h5,
specialize h1 ψ, cases h1,
cases h1_left,
apply absurd h1_left h5,
have h6 : (ft.not ψ) ∈ Γ', from set.mem_of_subset_of_mem h3_left h1_left,
rw ax_consistent, 
push_neg,
existsi ((ψ :: (ft.not ψ :: list.nil))),
simp, split, 
{
  split,
  { exact h4, },
  { exact h6, },
}, 
{
  have hfcs: _, from @fin_conj_simp form ft ψ,
  simp[finite_ax_consistent],
  have h: _, from ft.notdef,
  finish,
},
end


-- -- Exercise 1 from class notes
-- lemma ex1help {Γ : ctx agents} {φ : form agents} {L L' : list (form agents)} :
--   (∀ ψ ∈ L, ψ ∈ Γ) → prfS5 ∅ (fin_conj L ⊃ φ) → (∀ ψ ∈ L', ψ ∈ (insert φ Γ)) 
--   → ∃ L'' : list (form agents), (∀ ψ ∈ L'', ψ ∈ Γ) ∧ prfS5 ∅ (fin_conj L'' ⊃ fin_conj L') :=
-- begin
-- intros h1 h2 h3, induction L',
-- existsi ([] : list (form agents)),
-- split,
-- intros ψ h4, exact false.elim h4,
-- exact iden,
-- simp at *, cases h3 with h3 h4,
-- cases L'_ih h4 with L'' L'_ih,
-- cases L'_ih with ih1 ih2,
-- cases h3, 
-- existsi (L''++L : list (form agents)),
-- split,
-- simp at *, intros ψ h2,
-- cases h2 with h2 h5,
-- exact ih1 ψ h2,
-- exact h1 ψ h5,
-- subst h3, 
-- exact (cut (mp pl6 fin_conj_append) (cut (mp pl5 and_switch) (imp_and_and_imp (mp (mp pl4 h2) ih2)))),
-- existsi (L'_hd::L'' : list (form agents)),
-- split, simp at *, split, exact h3, exact ih1,
-- exact imp_and_imp ih2
-- end


-- lemma exercise1 {Γ : ctx agents} {φ : form agents} {L : list (form agents)} :
--   max_ax_consist Γ → (∀ ψ ∈ L, ψ ∈ Γ) → prfS5 ∅ (fin_conj L ⊃ φ) → φ ∈ Γ :=
-- begin
-- intros h1 h2 h3, 
-- by_contradiction h4, 
-- cases h1 with h1 h5, 
-- specialize h5 (Γ ∪ {φ}), 
-- simp at h5,
-- specialize h5 (set.ssubset_insert h4), 
-- rw ax_consist at h5,
-- push_neg at h5,
-- cases h5 with L' h5,
-- cases h5 with h5 h6,
-- rw fin_ax_consist at h6, 
-- rw not_not at h6,
-- have h7 := ex1help h2 h3 h5,
-- cases h7 with L'' h7,
-- cases h7 with h7 h8,
-- apply h1 L'' h7,
-- exact cut h8 h6
-- end


-- lemma max_dn (Γ : ctx agents) (h : max_ax_consist Γ) (φ : form agents) :
--   φ ∈ Γ ↔ (¬¬φ) ∈ Γ :=
-- begin
-- split, intro h1, 
-- have h2 : (∀ ψ ∈ [φ], ψ ∈ Γ) → prfS5 ∅ (fin_conj [φ] ⊃ (¬¬φ)) → (¬¬φ) ∈ Γ, from exercise1 h,
-- simp at *, apply h2, exact h1,
-- exact (cut (mp pl5 phi_and_true) dni), 
-- intro h1,
-- have h2 : (∀ ψ ∈ [¬¬φ], ψ ∈ Γ) → prfS5 ∅ (fin_conj [¬¬φ] ⊃ φ) → φ ∈ Γ, from exercise1 h,
-- simp at *, apply h2, exact h1,
-- exact (cut (mp pl5 phi_and_true) dne), 
-- end


-- lemma max_boxdn (Γ : ctx agents) (h : max_ax_consist Γ) (φ : form agents) (a : agents) :
--   (¬K a φ) ∈ Γ → (¬ (K a (¬¬φ))) ∈ Γ :=
-- begin
-- intro h1,
-- have h2 : ∀ a, (∀ ψ ∈ [¬ K a φ], ψ ∈ Γ) → prfS5 ∅ (fin_conj [¬ K a φ] ⊃ (¬ (K a (¬¬φ)))) → (¬ (K a (¬¬φ))) ∈ Γ,
--   from λ a, exercise1 h,
-- simp at *, 
-- apply h2 a, exact h1, clear h2,
-- exact (cut (mp pl5 phi_and_true) (mp pl5 box_dn)), 
-- end


-- lemma max_notiff {form : Type} (ft: formula form) (Γ: set form) 
-- (h : max_ax_consistent ft Γ) (φ : form) :
--   φ ∉ Γ ↔ (ft.imp φ ft.bot) ∈ Γ :=
-- begin
-- split, intro h1,
-- have h2: ax_consistent ft Γ, from max_imp_ax h, 
-- have h3 := max_forall_ex_or_neg Γ h2 h,
-- specialize h3 φ, cases h3, exact absurd h3 h1, simp[ft.notdef] at h3, exact h3,
-- intro h1,
-- have h2 := max_imp_ax h, 
-- have h3 := six Γ h2,
-- cases h3, specialize h3_mp h (¬φ), simp at *,
-- cases h3_mp with mp1 mp2,
-- have h4 := max_dn Γ h φ,
-- rw ←not_iff_not at h4, apply h4.mpr, exact mp2 h1
-- end


-- lemma max_imp_1 {Γ : ctx agents} {φ ψ : form agents} : 
--   max_ax_consist Γ → (φ ∈ Γ → ψ ∈ Γ) → (φ ⊃ ψ) ∈ Γ :=
-- begin
-- intros h1 h2, rw imp_iff_not_or at h2,
-- cases h2,
-- have h3 : (∀ χ ∈ [¬φ], χ ∈ Γ) → prfS5 ∅ (fin_conj [¬φ] ⊃ (φ ⊃ ψ)) → (φ ⊃ ψ) ∈ Γ, from exercise1 h1,
-- simp at *, apply h3, 
-- exact (max_notiff Γ h1 φ).mp h2,
-- exact cut (mp pl5 phi_and_true) (and_right_imp.mp exfalso),
-- have h3 : (∀ χ ∈ [ψ], χ ∈ Γ) → prfS5 ∅ (fin_conj [ψ] ⊃ (φ ⊃ ψ)) → (φ ⊃ ψ) ∈ Γ, from exercise1 h1,
-- simp at *, 
-- apply h3, exact h2, exact (cut (mp pl5 phi_and_true) pl1),
-- end


-- lemma max_imp_2 {Γ : ctx agents} {φ ψ : form agents} : 
--   max_ax_consist Γ → (φ ⊃ ψ) ∈ Γ → φ ∈ Γ → ψ ∈ Γ :=
-- begin
-- intros h1 h2 h3,
-- have h4 : (∀ χ ∈ [φ, (φ ⊃ ψ)], χ ∈ Γ) → prfS5 ∅ (fin_conj [φ, (φ ⊃ ψ)] ⊃ ψ) → ψ ∈ Γ, from exercise1 h1,
-- simp at *, apply h4, intros χ h5, cases h5, subst h5, exact h3, subst h5, exact h2,
-- exact and_right_imp.mpr (mp pl5 phi_and_true)
-- end


-- lemma max_conj_1 {Γ : ctx agents} {φ ψ : form agents} : 
--   max_ax_consist Γ → (φ ∈ Γ ∧ ψ ∈ Γ) → (φ & ψ) ∈ Γ :=
-- begin
-- intros h1 h2,
-- have h3 : (∀ χ ∈ [φ], χ ∈ Γ) → prfS5 ∅ (fin_conj [φ] ⊃ (ψ ⊃ (φ & ψ))) → (ψ ⊃ (φ & ψ)) ∈ Γ, 
--   from exercise1 h1,
-- simp at *,
-- apply max_imp_2 h1, 
-- exact (h3 h2.left) (cut (mp pl5 phi_and_true) pl4), exact h2.right
-- end


-- lemma max_conj_2 {Γ : ctx agents} {φ ψ : form agents} : 
--   max_ax_consist Γ → (φ & ψ) ∈ Γ → φ ∈ Γ :=
-- begin
-- intros h1 h2,
-- have h3 : (∀ χ ∈ [(φ & ψ)], χ ∈ Γ) → prfS5 ∅ (fin_conj [(φ & ψ)] ⊃ φ) → φ ∈ Γ, 
--   from exercise1 h1,
-- simp at *, apply h3, exact h2,
-- exact (cut (mp pl5 phi_and_true) pl5)
-- end


-- lemma max_conj_3 {Γ : ctx agents} {φ ψ : form agents} : 
--   max_ax_consist Γ → (φ & ψ) ∈ Γ → ψ ∈ Γ :=
-- begin
-- intros h1 h2,
-- have h3 : (∀ χ ∈ [(φ & ψ)], χ ∈ Γ) → prfS5 ∅ (fin_conj [(φ & ψ)] ⊃ ψ) → ψ ∈ Γ, 
--   from exercise1 h1,
-- simp at *, apply h3, exact h2,
-- exact (cut (mp pl5 phi_and_true) pl6)
-- end


-- -- Γ is maximally AX-consistent iff it is AX-consistent and for 
-- -- every AX-consistent set Γ', if Γ ⊆ Γ', then Γ = Γ'
-- lemma max_equiv (Γ : ctx agents) : max_ax_consist Γ ↔ ax_consist Γ ∧ 
--   ∀ Γ', ax_consist Γ' → Γ ⊆ Γ' → Γ = Γ' :=
-- begin
-- split, 
-- {intro h1, split, exact h1.left, 
-- intros Γ' h2 h3, rw set.subset.antisymm_iff, split, exact h3,
-- by_contradiction h4, exact h1.right Γ' (and.intro h3 h4) h2}, 
-- intro h1, split, exact h1.left,
-- intros Γ' h2, by_contradiction h3,
-- rw set.ssubset_def at h2, apply h2.right, 
-- rw (h1.right Γ' h3) h2.left
-- end


/-- Let `c` be a nonempty chain of sets and `s` a finite set, such that each
element of `s` is in some set of `c`. Then there is a `t ∈ c` that contains the
entirety of `s`.

In other words, finitary properties are preserved under unions.

This is useful in combination with Zorn's lemma, if you take `⋃₀ c` as the
upper bound of a chain of sets.
-/
lemma exists_subset_of_finite_of_subset_sUnion_of_chain {α : Type*}
  (c : set (set α)) (hc : is_chain (⊆) c)
  (t : set α) (ht : t ∈ c)
  (s : set α) (hs : s.finite) (hsc : s ⊆ ⋃₀ c) : ∃ t ∈ c, s ⊆ t :=
begin
  revert hsc,
  refine hs.induction_on _ _,
  { exact λ _, ⟨t, ht, set.empty_subset _⟩ },
  rintros x s hxs hs ih hsc,
  obtain ⟨⟨u, huc, hxu⟩, hsc⟩ := set.insert_subset.mp hsc,
  obtain ⟨t, htc, hst⟩ := ih hsc,
  cases hc.total huc htc with h h,
  { exact ⟨t, htc, insert_subset.mpr ⟨h hxu, hst⟩⟩ },
  { exact ⟨u, huc, insert_subset.mpr ⟨hxu, hst.trans h⟩⟩ }
end

/-- The union of a chain of consistent sets is consistent. -/
lemma ax_consistent_sUnion_chain {form : Type} {ft : formula form}
  {c : set (set form)} (c_cons : ∀ Γ ∈ c, ax_consistent ft Γ) (c_chain : is_chain (⊆) c)
  (Γ : set form) (hΓ : Γ ∈ c) :
  ax_consistent ft (⋃₀ c) :=
begin
  -- For consistency, we have to show any finite subset of axioms L does not imply falsum.
  unfold ax_consistent finite_ax_consistent at ⊢ c_cons,
  intros L L_subset,
  -- Since L is finite, it is completely contained in some element of the chain,
  -- and each element of the chain is consistent, therefore L does not imply falsum.
  obtain ⟨Γ, hΓc, hΓ⟩ := exists_subset_of_finite_of_subset_sUnion_of_chain c c_chain
    Γ hΓ
    { x | x ∈ L } _ L_subset,
  { exact c_cons Γ hΓc L hΓ },
  letI := classical.dec_eq form,
  convert set.finite_mem_finset L.to_finset,
  ext; simp
end

lemma lindenbaum {form : Type} (ft: formula form) (Γ : set form) (hax : ax_consistent ft Γ) :
  ∃ Γ', max_ax_consistent ft Γ' ∧ Γ ⊆ Γ' :=
begin
  -- By Zorn's lemma, it suffices to show that the union of a chain of consistent sets of formulas
  -- is itself consistent.
  obtain ⟨Γ', consistent, subset, max⟩ := zorn_nonempty_preorder₀ (ax_consistent ft) _ Γ hax,
  { refine ⟨Γ', ⟨consistent, _⟩, subset⟩,
    intros Δ hΓΔ hconsΔ,
    rw ← set.lt_eq_ssubset at hΓΔ,
    exact hΓΔ.not_le (max Δ hconsΔ hΓΔ.le) },
  { intros c c_cons c_chain Γ hΓ,
    exact ⟨⋃₀ c, ax_consistent_sUnion_chain c_cons c_chain Γ hΓ, λ _, set.subset_sUnion_of_mem⟩, }
end


-- -- Corollary 8 from class notes

lemma max_ax_exists {form : Type} (ft: formula form) (hnprfalseCL: ¬ ft.ax ft.bot) : 
  ∃ Γ : set form, max_ax_consistent ft Γ :=
begin
have h1 : ax_consistent ft ∅,
{intro L, intro h2, rw finite_ax_consistent, 
have h3 := listempty ft h2, have this : ∅ = ∅, refl, 
specialize h3 this, subst h3, by_contradiction h4, 
apply hnprfalseCL, 
apply ft.mp,
exact h4,
exact prtrue,},
have h2 := lindenbaum ft (∅: set form) h1, 
cases h2 with Γ h2, cases h2 with h2 h3, existsi (Γ : set form), apply h2
end

-- lemma max_ax_exists (hax : sem_cons (∅ : ctx agents) equiv_class) : ∃ Γ : ctx agents, max_ax_consist Γ :=
-- begin
-- have h1 : ax_consist ∅,
-- {intro L, intro h2, rw fin_ax_consist, 
-- have h3 := listempty h2, have this : ∅ = ∅, refl, 
-- specialize h3 this, subst h3, by_contradiction h4, 
-- apply nprfalse hax, exact mp dne h4},
-- have h2 := lindenbaum ∅ h1, 
-- cases h2 with Γ h2, cases h2 with h2 h3, existsi (Γ : ctx agents), apply h2
-- end

-- (formula : Type) (Γ: set (formula))
-- (ax: formula → Prop) (imp: formula → formula → formula) (bot: formula) (and: formula → formula → formula) (true: formula):

def set_proves {form : Type} {ft: formula form} (Γ : set (form)) (φ : form) :=
∃ (fs : list (form)), (∀ x ∈ fs, x ∈ Γ) ∧ ft.ax (ft.imp (finite_conjunction ft fs) φ)

lemma not_ax_consistent_of_proves_bot {form : Type} {ft: formula form} (Γ : set form)
  (h : @set_proves form ft Γ ft.bot) : ¬ (ax_consistent ft Γ) :=
begin
  intro hf,
  cases h with l h,
  cases h,
  apply hf,
  intros ψ hψ,
  apply h_left,exact hψ,
  exact h_right,
end


lemma bot_not_mem_of_ax_consistent {form : Type} {ft: formula form} (Γ : set (form))
  (hΓ : ax_consistent ft Γ) : (ft.bot) ∉ Γ :=
begin
  intro hf,
  have hbot_proves_bot: @set_proves form ft Γ ft.bot, from 
  begin
    -- simp [ax_consistent, finite_ax_consistent] at hΓ,
    let l := (ft.bot :: list.nil),
    apply exists.intro l,
    split,
    { simp, exact hf, },
    {
      simp[l, finite_conjunction],
      apply cut,
      { exact ft.p5 _ _, },
      { exact iden},
    },
  end,
  exact (not_ax_consistent_of_proves_bot Γ hbot_proves_bot) hΓ,
end

lemma proves_of_mem {form : Type} {ft: formula form} (Γ : set (form)) (φ : form)
  (h : φ ∈ Γ) : @set_proves form ft Γ φ :=
⟨list.cons φ list.nil,
  by simpa using h,
  have ft.ax (ft.imp (ft.and φ ft.top) φ), from ft.p5 _ _,
  by simpa [finite_conjunction]⟩

lemma mem_max_consistent_iff_proves {form : Type} {ft: formula form} (Γ : set (form)) (φ : form)
   (hΓ : max_ax_consistent ft Γ) : @set_proves form ft Γ φ ↔ φ ∈ Γ :=
⟨begin
  intro h,
  cases max_ax_contains_phi_or_neg Γ hΓ φ,
  { assumption },
  exfalso,
  refine not_ax_consistent_of_proves_bot Γ _ (hΓ.1),
  simp [set_proves, finite_conjunction] at ⊢ h,
  -- exercise in logic
  cases h with fs h,
  cases h,
  apply exists.intro (ft.not φ :: fs),
  split,
  { 
    intros x hx,
    cases hx,
    rw ←hx at h_1, exact h_1,
    apply h_left x hx,
  },
  {
    have hφ: ft.ax (ft.imp (finite_conjunction ft (ft.not φ :: fs)) (φ)), from cut (imp_and_r h_right) (iden),
    have hnφ: ft.ax (ft.imp (finite_conjunction ft (ft.not φ :: fs)) (ft.not φ)), from imp_and_l iden,
    apply cut,
    { exact imp_imp_and hφ hnφ, },
    { exact contra_imp_false, },
  },
 end,
 proves_of_mem Γ φ⟩

lemma always_true_of_true {form : Type} {ft: formula form} (φ : form) (h : ft.ax φ)
  (Γ : set (form)) : @set_proves form ft Γ φ :=
⟨list.nil, by rintro x ⟨⟩, ft.mp _ _ (ft.p1 _ _) h⟩

lemma false_of_always_false {form : Type} {ft: formula form} (φ : form)
  (h : ∀ (Γ : set (form)) (hΓ : max_ax_consistent ft Γ), ¬ @set_proves form ft Γ φ) :
  ft.ax (ft.not φ) :=
begin
  let Γ := {φ},
  by_cases hφ : ax_consistent ft Γ,
  { obtain ⟨Γ', hΓ', sub⟩ := lindenbaum ft Γ hφ,
    have := h Γ' hΓ',
    rw mem_max_consistent_iff_proves Γ' φ hΓ' at this,
    have := sub (set.mem_singleton φ),
    contradiction },
  simp [ax_consistent, finite_ax_consistent] at hφ,
  rcases hφ with ⟨(list.nil | ⟨x, xs⟩), sub, pf⟩,
  { simp [finite_conjunction] at pf,
    -- we have ⊥, so (φ → ⊥) should also follow
    simp [ft.notdef],
    exact ax_bot_imp pf,
    },
  { -- we have (φ ∧ φ ... ∧ φ) → ⊥, so (φ → ⊥) should also follow
    induction xs, 
    {
      simp [finite_conjunction] at *,
      simp [sub] at *,
      simp [ft.notdef],
      exact iff_and_top.mp pf,
    },
    {
      simp [finite_conjunction] at *,
      apply xs_ih,
      { exact sub.left, },
      { exact sub.right.right, },
      {
        simp [sub.right.left, sub.left] at *,
        apply remove_and_imp pf,
      }

    },
  },
end

lemma false_of_always_false' {form : Type} {ft: formula form} (φ : form)
  (h : ∀ (Γ : set (form)) (hΓ : max_ax_consistent ft Γ), φ ∉ Γ) :
  ft.ax (ft.iff φ ft.bot) :=
begin
  rw ft.iffdef,
  have hfoaf: _, from (@false_of_always_false form ft φ) ,
  -- have hmmcip: _, from @mem_max_consistent_iff_proves form ft,
  -- use false_of_always_false
  simp,
  apply ft.mp,
  apply ft.mp,
  apply ft.p4,
  {
    rw ft.notdef at hfoaf,
    apply hfoaf,
    intros Γ hΓ hf,
    apply h,
    { exact hΓ, },
    { 
      apply iff.elim_left (mem_max_consistent_iff_proves Γ φ hΓ),
      exact hf,
    },
  },
  { exact explosion, },
end

lemma max_ax_contains_by_set_proof {form: Type} {ft: formula form} {φ ψ: form} (Γ: set form)
  (h_max: max_ax_consistent ft Γ) (hin: φ ∈ Γ) (hproves: ft.ax (ft.imp φ ψ)) : ψ ∈ Γ :=
begin
  rw ←(mem_max_consistent_iff_proves Γ ψ h_max),
  simp[set_proves],
  apply exists.intro (φ :: list.nil),
  split,
  { intros x hx, simp at *, rw ←hx at hin, assumption, },
  { 
    simp[finite_conjunction],
    rw iff_and_top,
    exact hproves, 
  },
end 

lemma max_ax_contains_by_set_proof_2h {form: Type} {ft: formula form} {φ ψ χ: form} (Γ: set form)
  (h_max: max_ax_consistent ft Γ) (hinφ: φ ∈ Γ) (hinψ: ψ ∈ Γ) (hproves: ft.ax (ft.imp φ (ft.imp ψ χ))) : χ ∈ Γ :=
begin
  rw ←(mem_max_consistent_iff_proves Γ χ h_max),
  simp[set_proves],
  apply exists.intro (ψ :: φ :: list.nil),
  split,
  { intros x hx, simp at *, cases hx, repeat{ rw ←hx at *, assumption, },},
  { 
    simp[finite_conjunction],
    apply cut,
    apply ft.mp _ _ (ft.p6 _ _) and_commute',
    rw iff_and_top,
    rw and_right_imp,
    exact hproves,
  },
end 

-- lemma ex_empty_eff {form: Type} {ft: formula form} {Γ: set form} 
-- (hΓ: max_ax_consistent ft Γ) (hempty : {t : set  | φ ∈ ↑t} = ∅) ∧ ([G]φ) ∈ ↑s

-- {t : states | φ ∈ ↑t} ⊆ ∅ ∧ ([G]φ) ∈ ↑s