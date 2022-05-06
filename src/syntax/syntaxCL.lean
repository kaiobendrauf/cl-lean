inductive formCL (agents  : Type) : Type
  | bot                         : formCL
  | var  (n : nat)              : formCL
  | and  (φ ψ : formCL)         : formCL
  | imp  (φ ψ : formCL)         : formCL
  | eff  (G: set agents) 
         (φ : formCL)            : formCL


-- form notation
notation `⊥`:80       := formCL.bot
prefix `p`:80         := formCL.var
infix `&`:80          := formCL.and
infix `~>`:25         := formCL.imp
notation `¬`:80 φ     :=  φ ~> ⊥
notation `[` G `]` φ  := formCL.eff G φ
notation `⊤`:80       := ¬ (⊥)
notation φ `∨` ψ      := ¬ (( ¬ φ) & (¬ ψ))
notation φ `↔` ψ      := (φ ~> ψ) & (ψ ~> φ)


variable {agents : Type}
