import semantics.playability 
local attribute [instance] classical.prop_decidable

variable {agents : Type}

open set

----------------------------------------------------------
-- Frames & Models
----------------------------------------------------------

structure frame :=
(states: Type)
(hs : nonempty states)

structure frameCL (agents : Type) extends frame :=
(ha : nonempty agents)
(E: playable_effectivity_struct states ha)

structure model :=
(f : frame)
(v : ℕ → set f.states)

structure modelCL (agents : Type) :=
(f : frameCL agents)
(v : ℕ → set f.states)

