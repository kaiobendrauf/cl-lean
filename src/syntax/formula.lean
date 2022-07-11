import data.set.basic 
import semantics.playability 
import semantics.model
open set

structure formula (form: Type) :=
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



structure CLformula (agents: Type) (form: Type) :=
(propf: formula form)
(eff : set agents → form → form)
(Bot : ∀ G, propf.ax (propf.not (eff G propf.bot)))
(Top : ∀ G, propf.ax (eff G propf.top))
(N   : ∀ φ: form, propf.ax (propf.imp (propf.not (eff ∅ (propf.not φ))) (eff univ φ)))
(M   : ∀ φ ψ G, propf.ax (propf.imp (eff G (propf.and φ ψ)) (eff G φ)))
(S   : ∀ φ ψ G F, G ∩ F = ∅ → propf.ax (propf.imp (propf.and (eff G φ) (eff F ψ)) (eff (G ∪ F) (propf.and φ ψ))))
(Eq  : ∀ φ ψ G, propf.ax (propf.iff φ ψ) → propf.ax (propf.iff (eff G φ) (eff G ψ)))

-- (s_entails: ∀ m: modelCL agents, m.f.states → form → Prop)
-- (s_entails_bot: ∀ m s, (s_entails m s propf.bot) = false)
-- (s_entails_var: ∀ m: modelCL agents, ∀ s n, (s ∈ m.v n) ↔ (s_entails m s (propf.var n)))
-- (s_entails_imp: ∀ m s φ ψ, (s_entails m s φ → s_entails m s ψ) ↔ (s_entails m s (propf.imp φ ψ)))
-- (s_entails_and: ∀ m s φ ψ, (s_entails m s φ ∧ s_entails m s ψ) ↔ s_entails m s (propf.and φ ψ))
-- (s_entails_eff: ∀ m: modelCL agents, ∀ s φ G, ({t: m.f.states | s_entails m t φ} ∈ (m.f.E.E s G)) ↔ s_entails m s (eff G φ))

