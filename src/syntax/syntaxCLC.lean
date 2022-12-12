import data.fintype.basic
import data.finset.basic
import syntax.formula

open set

inductive formCLC (agents  : Type) /- [fintype agents] -/ : Type
-- φ := ⊥ | p | φ → φ| φ ∧ φ | [G]φ
  | bot                                 : formCLC
  | var  (n : nat)                      : formCLC
  | and  (φ ψ : formCLC)                : formCLC
  | imp  (φ ψ : formCLC)                : formCLC
  | eff  (G: set agents) (φ : formCLC)  : formCLC
  | K    (a: agents)     (φ : formCLC)  : formCLC
  -- | E    (G: set agents) (φ : formCLC)  : formCLC
  | C    (G: set agents) (φ : formCLC)  : formCLC


-- form notation
notation `⊥`:80         := formCLC.bot
infix `&`:80            := formCLC.and
infix `~>`:25           := formCLC.imp
notation `¬`:80 φ       :=  φ ~> formCLC.bot
notation `[` G `]`:90 φ := formCLC.eff G φ
notation `⊤`:80         := ¬ (formCLC.bot)
notation φ `∨` ψ        := ¬ (( ¬ φ) & (¬ ψ))
notation φ `<~>` ψ        := (φ ~> ψ) & (ψ ~> φ)

instance formulaCLC {agents : Type} : formula (formCLC agents) :=
{ bot := ⊥,
  and := formCLC.and,
  imp := formCLC.imp,
  not := λ φ, ¬ φ,
  iff := λ φ ψ, φ <~> ψ,
  top := ⊤,
  notdef := by simp,
  iffdef := by simp,
  topdef := by simp
}

notation `k` := formCLC.K
notation `e` := λ G φ, (finite_conjunction (list.map (λ i, k i φ) 
                       (finset.to_list (finite.to_finset (finite.of_fintype G)))))
notation `c` := formCLC.C 

