import semantics.model 
import syntax.syntaxCLK 
import semantics.playability 
import data.fintype.basic
-- cl.syntax.syntaxCL data.set.basic
-- import del.semantics.translationfunction
local attribute [instance] classical.prop_decidable

open formCLK set

---------------------- Semantics ----------------------

-- structure frameCL (agents : Type) :=
-- (states : Type)
-- (hs : nonempty states)
-- (ha : nonempty agents)
-- (E  : playable_effectivity_struct states ha)


-- structure frameCLK (agents : Type) extends frameCL agents :=
-- (rel   : agents → states → set states)
-- (rfl   : ∀ i s, s ∈ (rel i s))
-- (sym   : ∀ i s t, t ∈ (rel i s) → s ∈ (rel i t))
-- (trans : ∀ i s t u, t ∈ (rel i s) → u ∈ (rel i t) → u ∈ (rel i s))


-- structure modelCLK (agents : Type) :=
-- (f : frameCLK agents)
-- (v : ℕ → set f.states)

@[simp]
protected def formCLK.sizeof' (agents : Type) [agents_inst : has_sizeof agents] : formCLK agents → ℕ
| bot := 1
| (var n) := 1 + sizeof n
| (imp φ ψ) := 1 + formCLK.sizeof' φ + formCLK.sizeof' ψ
| (and φ ψ) := 1 + formCLK.sizeof' φ + formCLK.sizeof' ψ
| ([G] φ) := 1 + sizeof G + formCLK.sizeof' φ
| (K' i φ) := 1 + sizeof i + formCLK.sizeof' φ
| (E' i φ) := 1 + sizeof i + formCLK.sizeof' φ + 1 -- Make recursion from E' to K' possible

def formCLK.has_sizeof' {agents} : has_sizeof (formCLK agents) := ⟨formCLK.sizeof' _⟩
local attribute [instance] formCLK.has_sizeof'

-- Definition of semantic entailment
-- Order of arguments is swapped to help the equation compiler find the recursive parameter
def s_entails_CLK.aux {agents : Type} : ∀ m : modelCLK agents,
  formCLK agents → m.f.states → Prop
| m bot       s  := false
| m (var n)   s  := s ∈ m.v n
| m (imp φ ψ) s  := (s_entails_CLK.aux m φ s) → (s_entails_CLK.aux m ψ s)
| m (and φ ψ) s  := (s_entails_CLK.aux m φ s) ∧ (s_entails_CLK.aux m ψ s)
| m ([G] φ)   s  := {t: m.f.states | s_entails_CLK.aux m φ t} ∈ m.f.E.E (s) (G)
| m (K' i φ)  s  := ∀ t: m.f.states, t ∈ (m.f.rel i s) → s_entails_CLK.aux m φ t
| m (E' G φ)  s  := ∀ i ∈ G, s_entails_CLK.aux m (K' i φ) s

-- Definition of semantic entailment
def s_entails_CLK {agents : Type} (m : modelCLK agents) (s : m.f.states) (φ : formCLK agents) : Prop :=
s_entails_CLK.aux m φ s

variables {agents : Type}

-- φ is valid in a model M = (f,v)
def valid_m (m: modelCLK agents) (φ : formCLK agents) := 
  ∀ s, s_entails_CLK m s φ

def global_valid (φ : formCLK agents) :=
  ∀ m, valid_m m φ

lemma not_s_entails_imp (m : modelCLK agents) : ∀ s φ, 
  (¬(s_entails_CLK m s φ)) ↔ (s_entails_CLK m s (¬ φ)) :=
begin
  intros s φ,
  unfold s_entails_CLK s_entails_CLK.aux,
  refl,
end
