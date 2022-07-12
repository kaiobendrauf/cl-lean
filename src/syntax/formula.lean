import data.set.basic 
import semantics.playability 
import semantics.model
open set

class formula (form: Type) :=
(bot: form)
-- (var: ℕ → form)
(and: form → form → form)
(imp: form → form → form)
(top: form)
(not: form → form)
(iff: form → form → form)

(notdef: not = λ f, imp f bot)
(iffdef: iff = λ f g, and (imp f g) (imp g f))
(topdef: top = imp bot bot)

(ax : form → Prop)
(p1 : ∀ φ ψ : form, ax (imp φ ( imp ψ φ)))
(p2 : ∀ φ ψ χ : form, ax (imp (imp φ (imp ψ χ)) (imp (imp φ ψ) (imp φ χ))))
(p3 : ∀ φ ψ : form, ax (imp (imp (not φ) (not ψ)) (imp (imp (not φ) ψ) φ)))
(p4 : ∀ φ ψ : form, ax (imp φ (imp ψ (and φ ψ))))
(p5 : ∀ φ ψ : form, ax (imp (and φ ψ) φ))
(p6 : ∀ φ ψ : form, ax (imp (and φ ψ) ψ))
(p7 : ∀ φ ψ : form, ax (imp (imp (not φ) (not ψ)) (imp ψ φ)))
(mp : ∀ φ ψ : form, ax (imp φ ψ) → ax φ → ax ψ)

-- (s_entails: ∀ m: model, m.f.states → form → Prop)
-- (s_entails_bot: ∀ m s, false = (s_entails m s bot))
-- (s_entails_var: ∀ m: model, ∀ s n, (s ∈ m.v n) ↔ (s_entails m s (var n)))
-- (s_entails_imp: ∀ m s φ ψ, (s_entails m s φ → s_entails m s ψ) ↔ (s_entails m s (imp φ ψ)))
-- (s_entails_and: ∀ m s φ ψ, (s_entails m s φ ∧ s_entails m s ψ) ↔ s_entails m s (and φ ψ))



class CLformula (agents: Type) (form: Type) [formula form] :=
(eff : set agents → form → form)
(Bot : ∀ G, formula.ax (formula.not (eff G formula.bot)))
(Top : ∀ G, formula.ax (eff G formula.top))
(N   : ∀ φ: form, formula.ax (formula.imp (formula.not (eff ∅ (formula.not φ))) (eff univ φ)))
(M   : ∀ φ ψ G, formula.ax (formula.imp (eff G (formula.and φ ψ)) (eff G φ)))
(S   : ∀ φ ψ G F, G ∩ F = ∅ → formula.ax (formula.imp (formula.and (eff G φ) (eff F ψ)) (eff (G ∪ F) (formula.and φ ψ))))
(Eq  : ∀ φ ψ G, formula.ax (formula.iff φ ψ) → formula.ax (formula.iff (eff G φ) (eff G ψ)))

-- (s_entails: ∀ m: modelCL agents, m.f.states → form → Prop)
-- (s_entails_bot: ∀ m s, (s_entails m s formula.bot) = false)
-- (s_entails_var: ∀ m: modelCL agents, ∀ s n, (s ∈ m.v n) ↔ (s_entails m s (formula.var n)))
-- (s_entails_imp: ∀ m s φ ψ, (s_entails m s φ → s_entails m s ψ) ↔ (s_entails m s (formula.imp φ ψ)))
-- (s_entails_and: ∀ m s φ ψ, (s_entails m s φ ∧ s_entails m s ψ) ↔ s_entails m s (formula.and φ ψ))
-- (s_entails_eff: ∀ m: modelCL agents, ∀ s φ G, ({t: m.f.states | s_entails m t φ} ∈ (m.f.E.E s G)) ↔ s_entails m s (eff G φ))

def ax {form : Type} [ft: formula form] := ft.ax
def p1 {form : Type} [ft: formula form] := ft.p1
def p2 {form : Type} [ft: formula form] := ft.p2
def p3 {form : Type} [ft: formula form] := ft.p3
def p4 {form : Type} [ft: formula form] := ft.p4
def p5 {form : Type} [ft: formula form] := ft.p5
def p6 {form : Type} [ft: formula form] := ft.p6
def p7 {form : Type} [ft: formula form] := ft.p7
def mp {form : Type} [ft: formula form] := ft.mp
def Bot{agents: Type} {form : Type} [ft: formula form] [clf: CLformula agents form]:= clf.Bot
def Top{agents: Type} {form : Type} [ft: formula form] [clf: CLformula agents form]:= clf.Top
def N  {agents: Type} {form : Type} [ft: formula form] [clf: CLformula agents form]:= clf.N
def M  {agents: Type} {form : Type} [ft: formula form] [clf: CLformula agents form]:= clf.M
def S  {agents: Type} {form : Type} [ft: formula form] [clf: CLformula agents form]:= clf.S
def Eq {agents: Type} {form : Type} [ft: formula form] [clf: CLformula agents form]:= clf.Eq

-- @[simp] def notdef {form : Type} [ft: formula form] := ft.notdef
-- @[simp] def topdef {form : Type} [ft: formula form] := ft.topdef
-- @[simp] def iffdef {form : Type} [ft: formula form] := ft.iffdef
-- def mp {form : Type} [ft: formula form] := ft.mp

infix `→'`:80             := formula.imp
infix `∧'`:80             := formula.and
infix `↔'`:80             := formula.iff
notation `¬'`:80          := formula.not
notation `⊤'`:80          := formula.top
notation `[` G `]'`:80 φ  := CLformula.eff G φ

-- @[simp] def imp_notation {form : Type} [ft: formula form] : 
--   (λ a b: form, a ~> b) = (λ a b: form, formula.imp a b) :=
-- begin
--   simpa,
-- end