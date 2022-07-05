import data.finset

inductive formCLK (agents  : Type) : Type
-- φ := ⊥ | p | φ → φ| φ ∧ φ | [G]φ
  | bot                                 : formCLK
  | var  (n : nat)                      : formCLK
  | and  (φ ψ : formCLK)                : formCLK
  | imp  (φ ψ : formCLK)                : formCLK
  | eff  (G: set agents) (φ : formCLK)  : formCLK
  | K    (a: agents)     (φ : formCLK)  : formCLK



-- form notation
notation `⊥`:80         := formCLK.bot
infix `&`:80            := formCLK.and
infix `~>`:25           := formCLK.imp
notation `¬'`:80 φ      :=  φ ~> ⊥
notation `[` G `]`:90 φ := formCLK.eff G φ
notation `⊤'`:80        := ¬' (formCLK.bot)
notation φ `∨` ψ        := ¬' (( ¬' φ) & (¬' ψ))
notation φ `↔` ψ        := (φ ~> ψ) & (ψ ~> φ)
notation `K'`           := formCLK.K
notation `C'`           := formCLK.C 


def everyone_knows_l {agents: Type}: 
list agents → formCLK agents → formCLK agents
| list.nil  _ := (⊤')
| (i :: is) φ := (K' i φ) & everyone_knows_l is φ


notation `E'`        := everyone_knows_l