import syntax.propLemmas

open set

def ax {agents: Type} {form: Type} {clf: CLformula agents form}:= clf.propf.ax

def ef_and_switch {agents: Type} {form: Type} {clf: CLformula agents form} {φ ψ: form} {G: set agents}:
-- ⊢ clf.eff G (φ ∧ ψ) → clf.eff G (ψ ∧ φ)
   ax (clf.propf.imp (clf.eff G (clf.propf.and φ ψ)) (clf.eff G (clf.propf.and ψ φ))) :=
   begin
    have hiff: ax (clf.propf.iff (clf.propf.and φ ψ) (clf.propf.and ψ φ)), from and_switch,
    have hGiff: ax (clf.propf.iff (clf.eff G (clf.propf.and φ ψ)) (clf.eff G (clf.propf.and ψ φ))), from (clf.Eq _ _ _) hiff,
   exact iff_l hGiff,
   end

def ax_M' {agents: Type} {form: Type} {clf: CLformula agents form} (φ ψ: form) (G: set agents):
-- ⊢ clf.eff G (φ ∧ ψ) → clf.eff G ψ
   ax (clf.propf.imp (clf.eff G (clf.propf.and φ ψ)) (clf.eff G ψ)) :=
begin
   have hab: ax (clf.propf.imp (clf.eff G (clf.propf.and φ ψ)) (clf.eff G (clf.propf.and ψ φ))), from ef_and_switch,
   have hbc: ax (clf.propf.imp (clf.eff G (clf.propf.and ψ φ)) (clf.eff G ψ)), from (clf.M _ _ _),
   apply cut, exact hab, exact hbc,
end


def derived_monoticity_rule {agents: Type} {form: Type} {clf: CLformula agents form} {φ ψ: form} {G: set agents}:
-- ⊢ φ → ψ ⇒ ⊢ clf.eff Gφ → clf.eff Gψ
   ax (clf.propf.imp φ ψ) → ax (clf.propf.imp (clf.eff G φ) (clf.eff G ψ)) :=
begin
   -- Let ⊢ φ → ψ
   intro h,
   -- ⊢ φ → (φ ∧ ψ), from h, by propositional logic
   have h2: ax (clf.propf.imp φ (clf.propf.and φ ψ)), from 
      imp_and_iden h,
   -- ⊢ ((φ ∧ ψ) → φ), from ⊤ by propositional logic
   have hp5: ax (clf.propf.imp (clf.propf.and φ ψ) φ), from 
      (clf.propf.p5 _  _),
   -- ⊢ (φ ∧ ψ) ↔ φ, from h2 & hp5, by propositional logic
   have hiff: ax (clf.propf.iff (clf.propf.and φ ψ) φ), from
      begin
         rw clf.propf.iffdef,
         exact MP' h2 (MP' hp5 (clf.propf.p4 _  _)),
      end,
   -- ⊢ [G](φ ∧ ψ) ↔ [G]φ, from hiff, by axiom (Eq)
   have heq: ax (clf.propf.iff (clf.eff G(clf.propf.and φ ψ)) (clf.eff G φ)), from 
      (clf.Eq _ _ _) hiff,
   -- ⊢ [G]φ → [G](φ ∧ ψ), from heq, by propositional logic
   have hif: ax (clf.propf.imp (clf.eff G φ) (clf.eff G (clf.propf.and φ ψ))), from 
      iff_r heq,
   -- ⊢ [G](φ ∧ ψ) → [G](ψ), by axiom (M)
   have hM:  ax (clf.propf.imp (clf.eff G(clf.propf.and φ ψ)) (clf.eff G ψ)), from 
      ax_M' φ ψ G,
   -- ⊢ [G]φ → [G]ψ, from hif & hM, by propositional logic
   exact cut hif hM, 
end


def univ_iff_empty {agents: Type} {form: Type} {clf: CLformula agents form} {φ: form}: 
   -- ⊢ clf.eff Nφ ↔ ⊢ ¬ clf.eff ∅¬φ
   ax (clf.propf.iff (clf.eff univ φ) (clf.propf.not (clf.eff ∅ (clf.propf.not φ)))) :=
   -- ⇒
   have hl: ax (clf.propf.imp (clf.eff univ φ) (clf.propf.not (clf.eff ∅ (clf.propf.not φ)))), from
      begin
         -- Assume clf.eff Nφ
         -- Assume by contradiction clf.eff ∅¬φ
         apply by_contra_ax,
         rw ←and_right_imp,
         apply cut,
         exact clf.propf.mp _ _  (clf.propf.p5 _  _) (and_switch'),
         apply cut,
         --  clf.eff N(φ ∧ ¬φ), from above by axiom (S): (clf.eff Nφ ∧ clf.eff ∅¬φ) → clf.eff N ∪ ∅(φ ∧ ¬φ)
         exact (clf.S _ _ _ _) (by simp),
         apply cut,
         simp at *,
         --  clf.eff N(⊥), from above by axiom (Eq)
         have hGiff: ax (clf.propf.iff (clf.eff univ(clf.propf.and φ (clf.propf.not φ))) (clf.eff univ clf.propf.bot)), 

             { apply clf.Eq,
               exact contra_equiv_false, },
         exact iff_l hGiff,
         apply clf.propf.mp,
         --Contradiction from axiom (⊥): ¬clf.eff N⊥ and above.
         exact contra_imp_imp_false,
         exact clf.Bot _,
      end,
      -- ⇐ by the N axiom
   have hr: ax (clf.propf.imp (clf.propf.not (clf.eff ∅(clf.propf.not φ))) (clf.eff univ φ)), from clf.N _,

   begin
      rw clf.propf.iffdef,
      exact MP' hr (MP' hl (clf.propf.p4 _ _)),
   end

