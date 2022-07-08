import data.set.basic semantics.playability semantics.model
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
-- (s_entails_bot: ∀ m s φ, φ = bot → (s_entails m s φ = false))
-- (s_entails_var: ∀ m s φ n, φ = (var n) → s_entails m s φ = (s ∈ m.v n))
-- (s_entails_imp: ∀ m s φ ψ χ, φ = (imp ψ χ) → s_entails m s φ = s_entails m s ψ → s_entails m s χ)
-- (s_entails_and: ∀ m s φ ψ χ, φ = (and ψ χ) → s_entails m s φ = s_entails m s ψ ∧ s_entails m s χ)



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
-- (s_entails_bot: ∀ m s φ, φ = propf.bot → s_entails m s φ = false)
-- (s_entails_var: ∀ m s φ n, φ = (propf.var n) → s_entails m s φ = (s ∈ m.v n))
-- (s_entails_imp: ∀ m s φ ψ χ, φ = (propf.imp ψ χ) → s_entails m s φ = s_entails m s ψ → s_entails m s χ)
-- (s_entails_and: ∀ m s φ ψ χ, φ = (propf.and ψ χ) → s_entails m s φ = s_entails m s ψ ∧ s_entails m s χ)
-- (s_entails_eff: ∀ m s φ G ψ, φ = (eff G ψ) → s_entails m s φ = ({t: m.f.states | s_entails m t φ} ∈ (m.f.E.E s G)))

