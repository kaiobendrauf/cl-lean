import data.finset.basic
import data.fintype.basic

inductive formCLK (agents  : Type) /- [fintype agents] -/ : Type
-- φ := ⊥ | p | φ → φ| φ ∧ φ | [G]φ
  | bot                                   : formCLK
  | var  (n : nat)                        : formCLK
  | and  (φ ψ : formCLK)                  : formCLK
  | imp  (φ ψ : formCLK)                  : formCLK
  | eff  (G: set agents)    (φ : formCLK) : formCLK
  | K    (a: agents)        (φ : formCLK) : formCLK
  | E    (G: finset agents) (φ : formCLK) : formCLK



-- form notation
notation `⊥`:80         := formCLK.bot
infix `&`:80            := formCLK.and
infix `~>`:25           := formCLK.imp
notation `¬`:80 φ       :=  φ ~> formCLK.bot
notation `[` G `]`:90 φ := formCLK.eff G φ
notation `⊤`:80         := ¬ (formCLK.bot)
notation φ `∨` ψ        := ¬ (( ¬ φ) & (¬ ψ))
notation φ `↔` ψ        := (φ ~> ψ) & (ψ ~> φ)
notation `K'`           := formCLK.K
notation `E'`           := formCLK.E 


-- def everyone_knows {agents: Type}: 
-- list agents → formCLK agents → formCLK agents
-- | list.nil  _ := (⊤)
-- | (i :: is) φ := (K' i φ) & everyone_knows is φ


-- notation `E'`        := everyone_knows
