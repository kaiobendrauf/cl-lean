import syntax.syntaxCL semantics.playability
-- cl.syntax.syntaxCL data.set.basic
-- import del.semantics.translationfunction
local attribute [instance] classical.prop_decidable

variable {agents : Type}

open formCL set

---------------------- Semantics ----------------------

structure frameCL (agents : Type) :=
(states : Type)
(hs : nonempty states)
(ha : nonempty agents)
-- (E : states → ((set agents) → (set (set (states)))))
(E: playable_effectivity_fun states ha)

-- (E: states → (set agents) → Prop)

structure modelCL (agents : Type) :=
(f : frameCL agents)
(v : f.states → set ℕ)

-- Definition of semantic entailmentf
def s_entails : ∀ m : modelCL agents,
  m.f.states → formCL agents → Prop
  | m s bot           := false
  | m s (var n)       := n ∈ m.v s
  | m s (imp φ ψ)     := (s_entails m s φ) → (s_entails m s ψ)
  | m s (and φ ψ)     := (s_entails m s φ) ∧ (s_entails m s ψ)
  | m s ([G] φ)       := {t: m.f.states | s_entails m t φ} ∈ m.f.E.E (s) (G)

-- def tilde (m: modelCL agents) (φ : formCL agents)  :=
-- {t: m.f.states | s_entails m t φ}

-- φ is valid in a model M = (f,v)
def valid_m (m: modelCL agents) (φ : formCL agents) := 
  ∀ s, s_entails m s φ

def global_valid (φ : formCL agents) :=
  ∀ m, valid_m m φ

-- -- φ is valid in a frame f
-- def f_valid (φ : formCL agents) (f : frame agents) := 
--   ∀ v s, s_entails f v s φ


-- -- φ is valid in a class of frames F
-- def F_valid (φ : formCL agents) (F : set (frame agents)) := 
--   ∀ f ∈ F, ∀ v s, s_entails f v s φ

-- -- φ is universally valid (valid in all frames)
-- def u_valid (φ : formCL agents) := 
--   ∀ f v s, s_entails f v s φ


-- A context is true at a world in a model if each 
-- formula of the context is true at that world in that model
-- def s_entails_ctx (m : modelCL agents) 
--   := ∀ φ, ∀ s, s_entails m s φ


-- Global semantic consequence
-- def global_sem_csq (φ : formCL agents) :=
--   ∀ m s, s_entails m s φ


lemma not_s_entails_imp (m : modelCL agents) : ∀ s φ, 
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

