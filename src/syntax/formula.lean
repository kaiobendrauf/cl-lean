import data.set.basic 
import data.fintype.basic
import semantics.playability 
import semantics.model
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

(ax : form → Prop)
(p1 : ∀ φ ψ : form, ax (imp φ ( imp ψ φ)))
(p2 : ∀ φ ψ χ : form, ax (imp (imp φ (imp ψ χ)) (imp (imp φ ψ) (imp φ χ))))
(p3 : ∀ φ ψ : form, ax (imp (imp (not φ) (not ψ)) (imp (imp (not φ) ψ) φ)))
(p4 : ∀ φ ψ : form, ax (imp φ (imp ψ (and φ ψ))))
(p5 : ∀ φ ψ : form, ax (imp (and φ ψ) φ))
(p6 : ∀ φ ψ : form, ax (imp (and φ ψ) ψ))
(p7 : ∀ φ ψ : form, ax (imp (imp (not φ) (not ψ)) (imp ψ φ)))
(mp : ∀ φ ψ : form, ax (imp φ ψ) → ax φ → ax ψ)

def ax  {form : Type} [ft : formula form] := ft.ax
def p1  {form : Type} [ft : formula form] := ft.p1
def p2  {form : Type} [ft : formula form] := ft.p2
def p3  {form : Type} [ft : formula form] := ft.p3
def p4  {form : Type} [ft : formula form] := ft.p4
def p5  {form : Type} [ft : formula form] := ft.p5
def p6  {form : Type} [ft : formula form] := ft.p6
def p7  {form : Type} [ft : formula form] := ft.p7
def mp  {form : Type} [ft : formula form] := ft.mp

infixr   `→'` : 80         := formula.imp
infix    `∧'` : 80         := formula.and
infix    `↔'` : 80         := formula.iff
notation `¬'` : 80         := formula.not
notation `⊤'` : 80         := formula.top
notation `⊥'` : 80         := formula.bot -- ¬' ⊤'
infix    `∨'` : 80         := λ φ ψ, (¬' φ) →' ψ


class CLformula (agents : out_param Type) (form : Type) [formula form] :=
(eff : set agents → form → form)
(Bot : ∀ G, ax (¬' (eff G formula.bot)))
(Top : ∀ G, ax (eff G formula.top))
(N : ∀ φ : form, ax ((¬' (eff ∅ (¬' φ))) →' (eff univ φ)))
(M : ∀ φ ψ G, ax ((eff G (φ ∧' ψ)) →' (eff G φ)))
(S : ∀ φ ψ G F, G ∩ F = ∅ → ax (((eff G φ) ∧' (eff F ψ)) →' (eff (G ∪ F) (φ ∧' ψ))))
(Eq : ∀ φ ψ G, ax (φ ↔' ψ) → ax ((eff G φ) ↔' (eff G ψ)))

def Bot {agents : Type} {form : Type} [ft : formula form] [clf : CLformula agents form] := clf.Bot
def Top {agents : Type} {form : Type} [ft : formula form] [clf : CLformula agents form] := clf.Top
def N   {agents : Type} {form : Type} [ft : formula form] [clf : CLformula agents form] := clf.N
def M   {agents : Type} {form : Type} [ft : formula form] [clf : CLformula agents form] := clf.M
def S   {agents : Type} {form : Type} [ft : formula form] [clf : CLformula agents form] := clf.S
def Eq  {agents : Type} {form : Type} [ft : formula form] [clf : CLformula agents form] := clf.Eq

notation `[` G `]'` : 80 φ := CLformula.eff G φ


class Kformula (agents : out_param Type) (form : Type) [formula form] :=
(knows : agents → form → form)
(everyone_knows : set (agents) → form → form)
(K : ∀ φ ψ i, ax ((knows i (φ →' ψ)) →' ((knows i φ) →' (knows i ψ))))
(T : ∀ φ i, ax ((knows i φ) →' φ))
(Four : ∀ φ i, ax ((knows i φ) →' (knows i (knows i φ))))
(Five : ∀ φ i, ax ((¬' (knows i (φ))) →' ((knows i (¬' (knows i φ))))))
(RN: ∀ φ i, ax φ → ax (knows i φ))

def K    {agents : Type} {form : Type} [ft : formula form] [kf : Kformula agents form] := kf.K
def T    {agents : Type} {form : Type} [ft : formula form] [kf : Kformula agents form] := kf.T
def Four {agents : Type} {form : Type} [ft : formula form] [kf : Kformula agents form] := kf.Four
def Five {agents : Type} {form : Type} [ft : formula form] [kf : Kformula agents form] := kf.Five
def RN   {agents : Type} {form : Type} [ft : formula form] [kf : Kformula agents form] := kf.RN

notation `K'` : 80         := Kformula.knows
notation `E'` : 80         := Kformula.everyone_knows

class Cformula (agents : out_param Type) (form : Type) [formula form] [Kformula agents form]:=
(common_know : (set (agents)) → form → form)
(C : ∀ φ: form, ∀ G: set (agents), ax ((common_know G φ) →' (E' G (φ ∧' (common_know G φ)))))
(RC : ∀ φ ψ : form, ∀ G : set (agents), ax (ψ →' (E' G (φ ∧' ψ))) → ax (ψ →' (common_know G φ)))

def C  {agents : Type} {form : Type} [ft : formula form] [kf : Kformula agents form] [cf : Cformula agents form] := cf.C
def RC {agents : Type} {form : Type} [ft : formula form] [kf : Kformula agents form] [cf : Cformula agents form] := cf.RC

notation `C'` : 80 := Cformula.common_know
