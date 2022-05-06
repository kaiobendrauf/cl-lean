import syntax.syntaxCL data.set.basic
-- cl.syntax.syntaxCL data.set.basic
-- import del.semantics.translationfunction
local attribute [instance] classical.prop_decidable

variable {agents : Type}
-- open formPA s
open formCL
open set


---------------------- Semantics ----------------------

structure frame (agents : Type) :=
(states : Type)
(hs : nonempty states)
(ha : nonempty agents)
(E : states → ((set agents) → (set (set (states)))))

structure model (agents : Type) :=
(f : frame agents)
(v : f.states → set ℕ)

-- Definition of semantic entailment
def s_entails : ∀ m : model agents,
  m.f.states → formCL agents → Prop
  | m s bot           := false
  | m s (var n)       := n ∈ m.v s
  | m s (imp φ ψ)     := (s_entails m s φ) → (s_entails m s ψ)
  | m s (and φ ψ)     := (s_entails m s φ) ∧ (s_entails m s ψ)
  | m s ([G] φ)       := (∃ ts, ts ∈ (m.f.E s G) ∧ ∀ t, (t ∈ ts → s_entails m t φ))


-- def s_entails : ∀ f : frame agents, 
--   (nat → f.states → Prop) → f.states → formCL agents → Prop
--   | f v s bot           := false
--   | f v s (var n)       := v n s
--   | f v s (imp φ ψ)     := (s_entails f v s φ) → (s_entails f v s ψ)
--   | f v s (and φ ψ)     := (s_entails f v s φ) ∧ (s_entails f v s ψ)
--   | f v s (E C φ)       := (∃ os, os ∈ (f.e s C) ∧ ∀ s', (s' ∈ os → s_entails f v s' φ))


-- φ is valid in a model M = (f,v)
def m_valid (φ : formCL agents) (m: model agents) := 
  ∀ s, s_entails m s φ

-- -- φ is valid in a frame f
-- def f_valid (φ : formCL agents) (f : frame agents) := 
--   ∀ v s, s_entails f v s φ


-- -- φ is valid in a class of frames F
-- def F_valid (φ : formCL agents) (F : set (frame agents)) := 
--   ∀ f ∈ F, ∀ v s, s_entails f v s φ

-- -- φ is universally valid (valid in all frames)
-- def u_valid (φ : formCL agents) := 
--   ∀ f v s, s_entails f v s φ


-- -- A context is true at a world in a model if each 
-- -- formula of the context is true at that world in that model
-- def s_entails_ctx (f : frame) (v : nat → f.states → Prop) 
--   (Γ : ctx) := ∀ φ, ∀ x, φ ∈ Γ → s_entails f v x φ


-- -- Global semantic consequence
-- def global_sem_csq (Γ : ctx) (φ : form) :=
--   ∀ f v, s_entails_ctx f v Γ → ∀ x, s_entails f v x φ


lemma not_s_entails_imp (m : model agents) : ∀ s φ, 
  (¬(s_entails m s φ)) ↔ (s_entails m s (¬ φ)) :=
begin
intros s φ, split, 
repeat {intros h1 h2, exact h1 h2},
end


-- lemma s_entails_exists {f : frame} {v : nat → f.states → Prop} {x : f.states} {φ : form} :
--   s_entails f v x (◇φ) ↔ ∃ y : f.states, (f.rel x y ∧ s_entails f v y φ) :=
-- begin
-- split, intro h1,
-- repeat {rw s_entails at h1},
-- have h2 := not_or_of_imp h1,
-- cases h2, push_neg at h2,
-- cases h2 with y h2, cases h2 with h2 h3,
-- existsi (y : f.states), split, exact h2,
-- have h4 := (not_s_entails_imp f v y (¬φ)).mp h3,
-- repeat {rw s_entails at h4}, repeat {rw imp_false at h4},
-- rw not_not at h4, exact h4,
-- exact false.elim h2,
-- intro h1, cases h1 with y h1,
-- cases h1 with h1 h2,
-- intro h3,
-- exact absurd h2 (h3 y h1)
-- ends