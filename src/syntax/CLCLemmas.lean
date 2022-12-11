import syntax.CLKLemmas

def c_imp_kc {agents : Type} [hN : fintype agents] {form : Type} [ft : formula form] [fax : formula_ax form] 
  [kf : Kformula agents form] [cf : Cformula agents form]
  {φ : form} {G : set (agents)} {i : agents} (hi : i ∈ G): 
  ax ((C' G φ) →' (K' i (C' G φ))) :=
begin
  apply cut, apply C,
  apply cut, apply iff_l, apply E,
  apply cut, apply @finite_conj_forall_imp _ _ _ _ (K' i (φ ∧' (C' G φ))),
  simp,
  apply exists.intro i,
  simp [hi],
  apply mp,
  apply K,
  apply RN,
  exact p6 _ _,
end

def c_imp_k {agents : Type} [hN : fintype agents] {form : Type} [ft : formula form] [fax : formula_ax form] 
  [kf : Kformula agents form] [cf : Cformula agents form]
  {φ : form} {G : set (agents)} {i : agents} (hi : i ∈ G): 
  ax ((C' G φ) →' (K' i φ)) :=
begin
  apply cut, apply C,
  apply cut, apply iff_l, apply E,
  apply cut, apply @finite_conj_forall_imp _ _ _ _ (K' i (φ ∧' (C' G φ))),
  simp,
  apply exists.intro i,
  simp [hi],
  apply mp,
  apply K,
  apply RN,
  exact p5 _ _,
end

def c_imp {agents : Type} [hN : fintype agents] {form : Type} [ft : formula form] [fax : formula_ax form] 
  [kf : Kformula agents form] [cf : Cformula agents form]
  {φ : form} {G : set (agents)} {i : agents} (hi : i ∈ G) : 
  ax ((C' G φ) →' φ) := cut (c_imp_k hi) (T φ i)