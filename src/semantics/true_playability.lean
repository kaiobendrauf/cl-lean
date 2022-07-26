-- import semantics.playability
import data.fintype.basic

open set

def regular {agents : Type} {states : Type} 
  (E : ((set agents) → (set (set (states))))) :=
∀ G : set agents, ∀ X : set states, (X ∈ E (G)) → (Xᶜ ∉ E (Gᶜ))

def N_max {agents : Type} {states : Type}
  (E : ((set agents) → (set (set (states))))) :=
∀ X : set states, (Xᶜ ∉ E (∅)) → (X ∈ E (univ))

structure playable_effectivity_func {agents : Type} {states : Type}
  (s : states) (ha : nonempty agents) :=
(E : (set agents) → (set (set (states))))
(liveness   : ∀ G : set agents,
                ∅ ∉ E (G))
(safety     : ∀ G : set agents,
                univ ∈ E (G))
(N_max      : N_max E)
(monoticity : ∀ G : set agents, ∀ X Y : set states,
                X ⊆ Y → X ∈ E (G) → Y ∈ E (G))
(superadd   : ∀ G F : set agents, ∀ X Y : set states,
                X ∈ E (G) → Y ∈ E (F) → G ∩ F = ∅ →
                X ∩ Y ∈ E (G ∪ F))


def nonmonotonic_core {agents : Type} {states : Type} 
  (E: (set agents) → (set (set (states)))) (G: set agents) :=
{ X ∈ E (G) | ¬ ∃ Y, (Y ∈ E (G) ∧ Y ⊂ X) }

structure truly_playable_effectivity_func {agents : Type} {states : Type}
  (s : states) (ha : nonempty agents) extends playable_effectivity_func s ha :=
(complete_nmc: ∀ G, ∀ X ∈ E (G), ∃ Y, (Y ∈ (nonmonotonic_core E G) ∧ Y ⊆ X))

def playable_effectivity_struct {agents : Type} (states : Type) (ha : nonempty agents) :=
∀ s: states, playable_effectivity_func s ha

def truly_playable_effectivity_struct {agents : Type} (states : Type) (ha : nonempty agents) :=
∀ s: states, truly_playable_effectivity_func s ha

def truly_from_playable_finite {agents : Type} {states : Type}
  (s : states) (ha : nonempty agents)
  (playable : playable_effectivity_func s ha) [hfin : fintype states]: 
  truly_playable_effectivity_func s ha := 
{ non_monotonic_core :=
  begin
    intros G X hX,
    sorry,
  end,
  .. playable }