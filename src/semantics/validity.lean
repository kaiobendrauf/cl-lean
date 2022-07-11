import semantics.playability syntax.formula
local attribute [instance] classical.prop_decidable

variable {agents : Type}

open set

-- φ is valid in a model M = (f,v), if it is entailed by every state of the model
def valid_m_formula {form: Type} (ft: formula form) (m: model) (φ : form) := 
  ∀ s, ft.s_entails m s φ

-- φ is globally valid, if it is valid in all models
def global_valid {form: Type} (ft: formula form) (φ : form):=
  ∀ m, valid_m_formula ft m φ

-- lemma not_s_entails_imp {form: Type} (ft: formula form) (m: model) : 
--   ∀ s φ, (¬(ft.s_entails m s φ)) ↔ (ft.s_entails m s (ft.not φ)) :=
-- begin

-- end

