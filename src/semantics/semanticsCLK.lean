import semantics.model 
import syntax.syntaxCLK 
import semantics.playability 
-- cl.syntax.syntaxCL data.set.basic
-- import del.semantics.translationfunction
local attribute [instance] classical.prop_decidable

variable {agents : Type}

open formCLK set

---------------------- Semantics ----------------------

-- structure frameCL (agents : Type) :=
-- (states : Type)
-- (hs : nonempty states)
-- (ha : nonempty agents)
-- (E  : playable_effectivity_struct states ha)


structure frameCLK (agents : Type) extends frameCL agents :=
(rel   : agents → states → set states)
(rfl   : ∀ i s, s ∈ (rel i s))
(sym   : ∀ i s t, t ∈ (rel i s) → s ∈ (rel i t))
(trans : ∀ i s t u, t ∈ (rel i s) → u ∈ (rel i t) → u ∈ (rel i s))


structure modelCLK (agents : Type) :=
(f : frameCLK agents)
(v : ℕ → set f.states)

-- Definition of semantic entailment
def s_entails : ∀ m : modelCLK agents,
  m.f.states → formCLK agents → Prop
  | m s bot           := false
  | m s (var n)       := s ∈ m.v n
  | m s (imp φ ψ)     := (s_entails m s φ) → (s_entails m s ψ)
  | m s (and φ ψ)     := (s_entails m s φ) ∧ (s_entails m s ψ)
  | m s ([G] φ)       := {t: m.f.states | s_entails m t φ} ∈ m.f.E.E (s) (G)
  | m s (K' i φ)      := ∀ t: m.f.states, t ∈ (m.f.rel i s) → s_entails m t φ

-- φ is valid in a model M = (f,v)
def valid_m (m: modelCLK agents) (φ : formCLK agents) := 
  ∀ s, s_entails m s φ

def global_valid (φ : formCLK agents) :=
  ∀ m, valid_m m φ

lemma not_s_entails_imp (m : modelCLK agents) : ∀ s φ, 
  (¬(s_entails m s φ)) ↔ (s_entails m s (¬ φ)) :=
begin
intros s φ, split, 
repeat {intros h1 h2, exact h1 h2},
end
