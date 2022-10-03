import syntax.syntaxCLC 
import semantics.playability 
import semantics.model
import data.fintype.basic
-- cl.syntax.syntaxCL data.set.basic
-- import del.semantics.translationfunction
local attribute [instance] classical.prop_decidable

open formCLC set

---------------------- Semantics ----------------------

-- structure frameCL (agents : Type) :=
-- (states : Type)
-- (hs : nonempty states)
-- (ha : nonempty agents)
-- (E  : playable_effectivity_struct states ha)


-- structure frameCLC (agents : Type) extends frameCL agents :=
-- (rel   : agents → states → set states)
-- (rfl   : ∀ i s, s ∈ (rel i s))
-- (sym   : ∀ i s t, t ∈ (rel i s) → s ∈ (rel i t))
-- (trans : ∀ i s t u, t ∈ (rel i s) → u ∈ (rel i t) → u ∈ (rel i s))


-- structure modelCLC (agents : Type) :=
-- (f : frameCLC agents)
-- (v : ℕ → set f.states)

def C_path {agents : Type} [hN : fintype agents] {m : modelCLK agents}: 
  list agents → list m.f.states →  m.f.states →  m.f.states → Prop
  | _         list.nil s t := s = t
  | list.nil  _        s t := s = t
  | (i :: is)(u :: us) s t := (s = t) ∨ (u ∈ (m.f.rel i s) ∧ (C_path is us u t))

-- Definition of semantic entailmentf
def s_entails_CLC {agents : Type} [hN : fintype agents] (m : modelCLK agents) (s : m.f.states) :
  formCLC agents → Prop
  | bot       := false
  | (var n)   := s ∈ m.v n
  | (imp φ ψ) := (s_entails_CLC m s φ) → (s_entails_CLC m s ψ)
  | (and φ ψ) := (s_entails_CLC m s φ) ∧ (s_entails_CLC m s ψ)
  | ([G] φ)   := {t: m.f.states | s_entails_CLC m t φ} ∈ m.f.E.E (s) (G)
  | (k i φ)  := ∀ t: m.f.states, t ∈ (m.f.rel i s) → s_entails_CLC m t φ
  | (e G φ)  := ∀ i ∈ G, s_entails_CLK m s (k i φ)
  | (c G φ)  := ∀ t: m.f.states, (∃ la ls, (∀ a ∈ la, a ∈ G) ∧ C_path la ls s t)
                  s_entails_CLC m t φ
  
-- def tilde (m: modelCLC agents) (φ : formCLC agents)  :=
-- {t: m.f.states | s_entails m t φ}

-- φ is valid in a model M = (f,v)
def valid_m (m: modelCLK agents) (φ : formCLC agents) := 
  ∀ s, s_entails_CLC m s φ

def global_valid (φ : formCLC agents) :=
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


lemma not_s_entails_imp (m : modelCLK agents) : ∀ s φ, 
  (¬ (s_entails_CLC m s φ)) ↔ (s_entails_CLC m s (¬ φ)) :=
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

