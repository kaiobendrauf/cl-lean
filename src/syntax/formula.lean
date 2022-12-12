import data.set.basic 
import data.fintype.basic
import semantics.playability 
import semantics.model
import data.set.finite
open set

class formula (form : Type) :=
(bot : form)
-- (var : ℕ → form)
(and : form → form → form)
(imp : form → form → form)
(top : form)
(not : form → form)
(iff : form → form → form)
(notdef : not = λ f, imp f bot)
(iffdef : iff = λ f g, and (imp f g) (imp g f))
(topdef : top = imp bot bot)

infixr   `→'` : 80         := formula.imp
infix    `∧'` : 80         := formula.and
infix    `↔'` : 80         := formula.iff
notation `¬'` : 80         := formula.not
notation `⊤'` : 80         := formula.top
notation `⊥'` : 80         := formula.bot -- ¬' ⊤'
infix    `∨'` : 80         := λ φ ψ, (¬' φ) →' ψ

-- finite conjunction of formulas
def finite_conjunction {form : Type} [ft : formula form] : (list form) → form
  | list.nil   := ⊤'
  | (f :: fs)  := f ∧' (finite_conjunction fs) 

-- finite disjunction of formulas
def finite_disjunction {form : Type} [ft : formula form] : (list form) → form
  | list.nil   := ⊥'
  | (f :: fs)  := f ∨' (finite_disjunction fs)

class formula_ax (form : Type) [ft : formula form] :=
(ax : form → Prop)
(p1 : ∀ φ ψ : form, ax (φ →' (ψ →' φ)))
(p2 : ∀ φ ψ χ : form, ax ((φ →' (ψ →' χ)) →' ((φ →' ψ) →' (φ →' χ))))
(p3 : ∀ φ ψ : form, ax (((¬' φ) →' (¬' ψ)) →' (((¬' φ) →' ψ) →' φ)))
(p4 : ∀ φ ψ : form, ax (φ →' (ψ →' (φ ∧' ψ))))
(p5 : ∀ φ ψ : form, ax ((φ ∧' ψ) →' φ))
(p6 : ∀ φ ψ : form, ax ((φ ∧' ψ) →' ψ))
(p7 : ∀ φ ψ : form, ax (((¬' φ) →' (¬' ψ)) →' (ψ →' φ)))
(mp : ∀ φ ψ : form, ax (φ →' ψ) → ax φ → ax ψ)

def ax  {form : Type} [ft : formula form] [fax : formula_ax form] := fax.ax
def p1  {form : Type} [ft : formula form] [fax : formula_ax form] := fax.p1
def p2  {form : Type} [ft : formula form] [fax : formula_ax form] := fax.p2
def p3  {form : Type} [ft : formula form] [fax : formula_ax form] := fax.p3
def p4  {form : Type} [ft : formula form] [fax : formula_ax form] := fax.p4
def p5  {form : Type} [ft : formula form] [fax : formula_ax form] := fax.p5
def p6  {form : Type} [ft : formula form] [fax : formula_ax form] := fax.p6
def p7  {form : Type} [ft : formula form] [fax : formula_ax form] := fax.p7
def mp  {form : Type} [ft : formula form] [fax : formula_ax form] := fax.mp


class CLformula (agents : out_param Type) (form : Type) [formula form] [formula_ax form] :=
(eff : set agents → form → form)
(Bot : ∀ G, ax (¬' (eff G formula.bot)))
(Top : ∀ G, ax (eff G formula.top))
(N : ∀ φ : form, ax ((¬' (eff ∅ (¬' φ))) →' (eff univ φ)))
(M : ∀ φ ψ G, ax ((eff G (φ ∧' ψ)) →' (eff G φ)))
(S : ∀ φ ψ G F, G ∩ F = ∅ → ax (((eff G φ) ∧' (eff F ψ)) →' (eff (G ∪ F) (φ ∧' ψ))))
(Eq : ∀ φ ψ G, ax (φ ↔' ψ) → ax ((eff G φ) ↔' (eff G ψ)))

def Bot {agents : Type} {form : Type} [ft : formula form] [fax : formula_ax form] [clf : CLformula agents form] := clf.Bot
def Top {agents : Type} {form : Type} [ft : formula form] [fax : formula_ax form] [clf : CLformula agents form] := clf.Top
def N   {agents : Type} {form : Type} [ft : formula form] [fax : formula_ax form] [clf : CLformula agents form] := clf.N
def M   {agents : Type} {form : Type} [ft : formula form] [fax : formula_ax form] [clf : CLformula agents form] := clf.M
def S   {agents : Type} {form : Type} [ft : formula form] [fax : formula_ax form] [clf : CLformula agents form] := clf.S
def Eq  {agents : Type} {form : Type} [ft : formula form] [fax : formula_ax form] [clf : CLformula agents form] := clf.Eq

notation `[` G `]'` : 80 φ := CLformula.eff G φ


class Kformula (agents : out_param Type) [hN : fintype agents] (form : Type) [formula form] [formula_ax form] :=
(knows : agents → form → form)
(everyone_knows : set (agents) → form → form)
(K : ∀ φ ψ i, ax ((knows i (φ →' ψ)) →' ((knows i φ) →' (knows i ψ))))
(T : ∀ φ i, ax ((knows i φ) →' φ))
(Four : ∀ φ i, ax ((knows i φ) →' (knows i (knows i φ))))
(Five : ∀ φ i, ax ((¬' (knows i (φ))) →' (knows i (¬' (knows i φ)))))
(RN : ∀ φ i, ax φ → ax (knows i φ))
(edef : everyone_knows = λ G φ, (finite_conjunction (list.map (λ i, knows i φ) (finset.to_list (finite.to_finset (finite.of_fintype G))))))

def K    {agents : Type} {form : Type} [hN : fintype agents] [ft : formula form] [fax : formula_ax form] [kf : Kformula agents form] := kf.K
def T    {agents : Type} {form : Type} [hN : fintype agents] [ft : formula form] [fax : formula_ax form] [kf : Kformula agents form] := kf.T
def Four {agents : Type} {form : Type} [hN : fintype agents] [ft : formula form] [fax : formula_ax form] [kf : Kformula agents form] := kf.Four
def Five {agents : Type} {form : Type} [hN : fintype agents] [ft : formula form] [fax : formula_ax form] [kf : Kformula agents form] := kf.Five
def RN   {agents : Type} {form : Type} [hN : fintype agents] [ft : formula form] [fax : formula_ax form] [kf : Kformula agents form] := kf.RN
-- def E    {agents : Type} {form : Type} [hN : fintype agents] [ft : formula form] [fax : formula_ax form] [kf : Kformula agents form] := kf.E

notation `K'` : 80         := Kformula.knows
notation `E'` : 80         := Kformula.everyone_knows

class Cformula (agents : out_param Type) [hN : fintype agents] (form : Type) [formula form] [formula_ax form] [Kformula agents form]:=
(common_know : (set (agents)) → form → form)
(C : ∀ φ: form, ∀ G: set (agents), ax ((common_know G φ) →' (E' G (φ ∧' (common_know G φ)))))
(RC : ∀ φ ψ : form, ∀ G : set (agents), ax (ψ →' (E' G (φ ∧' ψ))) → ax (ψ →' (common_know G φ)))

def C  {agents : Type} {form : Type} [hN : fintype agents] [formula form] [formula_ax form] [Kformula agents form] [cf : Cformula agents form] := cf.C
def RC {agents : Type} {form : Type} [hN : fintype agents] [formula form] [formula_ax form] [Kformula agents form] [cf : Cformula agents form] := cf.RC

notation `C'` : 80 := Cformula.common_know

