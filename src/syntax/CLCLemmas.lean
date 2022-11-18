import syntax.CLLemmas

open set

-- ⊢ ((¬ φ) → (¬ (K i φ)))
def n_imp_nk {agents : Type} {form : Type} [ft : formula form] [clf : CLformula agents form] [kf : Kformula agents form] [cf : Cformula agents form]
  {φ : form} {i : agents} : 
  ax ((¬' φ) →' (¬' (K' i φ))) :=
begin
  apply by_contra_ax,
  apply imp_switch,
  apply cut,
  apply kf.T,
  rw ft.notdef,
  exact likemp,
end

-- ⊢ 
def n_inp_nk {agents : Type} {form : Type} [ft : formula form] [clf : CLformula agents form] [kf : Kformula agents form] [cf : Cformula agents form]
  {φ : form} {G : set (agents)} {i : agents} (hi : i ∈ G): 
  -- ax (¬' K' i (C' G φ)  →' ¬' C' G φ
  ax ((¬' (K' i (C' G φ))) →' (¬' (C' G φ))) :=
begin
  rw contrapos, 
  
end