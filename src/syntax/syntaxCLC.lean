import data.fintype.basic
import data.finset.basic

inductive formCLC (agents  : Type) [fintype agents] : Type
-- φ := ⊥ | p | φ → φ| φ ∧ φ | [G]φ
  | bot                                 : formCLC
  | var  (n : nat)                      : formCLC
  | and  (φ ψ : formCLC)                : formCLC
  | imp  (φ ψ : formCLC)                : formCLC
  | eff  (G: set agents) (φ : formCLC)  : formCLC
  | K    (a: agents)     (φ : formCLC)  : formCLC
  | E    (G: set agents) (φ : formCLC)  : formCLC
  | C    (G: set agents) (φ : formCLC)  : formCLC


-- form notation
notation `⊥`:80         := formCLC.bot
infix `&`:80            := formCLC.and
infix `~>`:25           := formCLC.imp
notation `¬`:80 φ       :=  φ ~> formCLC.bot
notation `[` G `]`:90 φ := formCLC.eff G φ
notation `⊤`:80         := ¬ (formCLC.bot)
notation φ `∨` ψ        := ¬ (( ¬ φ) & (¬ ψ))
notation φ `↔` ψ        := (φ ~> ψ) & (ψ ~> φ)
notation `k`           := formCLC.K
notation `e`           := formCLC.E
notation `c`           := formCLC.C 


-- def everyone_knows {agents: Type}: 
-- list agents → formCLC agents → formCLC agents
-- | list.nil  _ := (⊤)
-- | (i :: is) φ := (K' i φ) & everyone_knows is φ


-- notation `E'`        := everyone_knows
