import syntax.syntaxCLC 
import semantics.playability 
import semantics.model
import data.fintype.basic
import logic.relation

local attribute [instance] classical.prop_decidable

open formCLC set

---------------------- Semantics ----------------------

-- def disjunct_rel {agents : Type} {m : modelCLK agents} (G : set agents) :
--   m.f.states →  m.f.states → Prop :=
-- λ s t, ∃ i ∈ G, t ∈ (m.f.rel i s)

def C_path {agents : Type}  {m : modelCLK agents} : 
  list agents → list m.f.states →  m.f.states →  m.f.states → Prop
  | list.nil  _        s t := false
  | (i :: is) list.nil s t := t ∈ (m.f.rel i s)
  | (i :: is)(u :: us) s t := (u ∈ (m.f.rel i s) ∧ (C_path is us u t)) 

def C_path_nil {agents : Type} {m : modelCLK agents} {ss : list m.f.states} {s t : m.f.states} : 
  C_path list.nil ss s t → false :=
begin
  intro hC,
  induction ss,
  repeat 
  { simp[C_path] at hC,
    exact hC, },
end

-- @[simp]
-- protected def formCLC.sizeof' (agents : Type) [agents_inst : has_sizeof agents] : formCLC agents → ℕ
-- | bot := 1
-- | (var n) := 1 + sizeof n
-- | (imp φ ψ) := 1 + formCLC.sizeof' φ + formCLC.sizeof' ψ
-- | (and φ ψ) := 1 + formCLC.sizeof' φ + formCLC.sizeof' ψ
-- | ([G] φ) := 1 + sizeof G + formCLC.sizeof' φ
-- | (k i φ) := 1 + sizeof i + formCLC.sizeof' φ
-- | (e i φ) := 1 + sizeof i + formCLC.sizeof' φ + 1 -- Make recursion from E' to K' possible
-- | (c i φ) := 1 + sizeof i + formCLC.sizeof' φ

-- def formCLC.has_sizeof' {agents} : has_sizeof (formCLC agents) := ⟨formCLC.sizeof' _⟩
-- local attribute [instance] formCLC.has_sizeof'

-- Definition of semantic entailment
-- Order of arguments is swapped to help the equation compiler find the recursive parameter
def s_entails_CLC {agents : Type}  : Π (m : modelCLK agents), m.f.states → formCLC agents → Prop
  | m s bot       := false
  | m s (var n)   := s ∈ m.v n
  | m s (imp φ ψ) := (s_entails_CLC m s φ) → (s_entails_CLC m s ψ)
  | m s (and φ ψ) := (s_entails_CLC m s φ) ∧ (s_entails_CLC m s ψ)
  | m s ([G] φ)   := {t : m.f.states | s_entails_CLC m t φ} ∈ m.f.E.E (s) (G)
  | m s (k i φ)   := ∀ t : m.f.states, t ∈ (m.f.rel i s) → s_entails_CLC m t φ
  -- | m (e G φ)   s := ∀ i ∈ G, (s_entails_CLC.aux m (k i φ) s)
  | m s (c G φ)   := ∀ t : m.f.states, (∃ la, (∀ a ∈ la, a ∈ G) ∧ ∃ ls, C_path la ls s t) → 
                        s_entails_CLC m t φ
  -- | m (c G φ)   s := ∀ t : m.f.states, (relation.trans_gen (disjunct_rel G) s t) → s_entails_CLC.aux m φ t

-- -- Definition of semantic entailment
-- def s_entails_CLC {agents : Type} (m : modelCLK agents) (s : m.f.states) (φ : formCLC agents) : Prop :=
-- s_entails_CLC.aux m φ s

-- def tilde (m: modelCLC agents) (φ : formCLC agents)  :=
-- {t: m.f.states | s_entails m t φ}
lemma s_entails_CLC_conjunction {agents : Type} {m : modelCLK agents} {s : m.f.states} 
  {φs : list (formCLC agents)} : 
  s_entails_CLC m s (finite_conjunction φs) ↔ ∀ φ ∈ φs, s_entails_CLC m s φ :=
begin
  induction φs with φ φs ih,
  { simp [finite_conjunction],
    show s_entails_CLC m s ⊤,
    simp [s_entails_CLC], },
  { unfold finite_conjunction,
    show s_entails_CLC m s (φ & finite_conjunction φs) ↔ _,
    simp [s_entails_CLC],
    intros h,
    exact ih, },
end

variables {agents : Type}

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
  intros s φ,
  unfold s_entails_CLC,
  refl
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

