-- import syntax.CLLemmas
import syntax.consistency

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
-- def n_inp_nk {agents : Type} {form : Type} [ft : formula form] [clf : CLformula agents form] [kf : Kformula agents form] [cf : Cformula agents form]
--   {φ : form} {G : set (agents)} {i : agents} (hi : i ∈ G): 
--   -- ax (¬' K' i (C' G φ)  →' ¬' C' G φ
--   ax ((¬' (K' i (C' G φ))) →' (¬' (C' G φ))) :=
-- begin
--   rw contrapos, 
  
-- end

def c_imp_kc {agents : Type} {form : Type} [ft : formula form] [clf : CLformula agents form] [kf : Kformula agents form] [cf : Cformula agents form]
  {φ : form} {G : set (agents)} {i : agents} (hi : i ∈ G): 
  ax ((C' G φ) →' (K' i (C' G φ))) :=
begin
  sorry,
  
end

def c_imp_k {agents : Type} {form : Type} [ft : formula form] [clf : CLformula agents form] [kf : Kformula agents form] [cf : Cformula agents form]
  {φ : form} {G : set (agents)} {i : agents} (hi : i ∈ G): 
  ax ((C' G φ) →' (K' i φ)) :=
begin
  sorry,
  
end

def c_imp {agents : Type} {form : Type} [ft : formula form] [clf : CLformula agents form] [kf : Kformula agents form] [cf : Cformula agents form]
  {φ : form} {G : set (agents)} {i : agents} (hi : i ∈ G) : 
  ax ((C' G φ) →' φ) := cut (c_imp_k hi) (T φ i)

lemma knows_conjunction {agents : Type} {form : Type} [ft : formula form] [kf : Kformula agents form] 
  {i : agents} {φs : list (form)} :
  ax ((finite_conjunction (list.map (K' i) φs)) →' (K' i (finite_conjunction φs))) :=
begin
induction φs,
{ apply mp,
  exact p1 _ _,
  apply RN,
  exact prtrue, },
{ apply cut,
  { apply imp_and_imp,
    exact φs_ih, },
  { exact (mp _ _ double_imp (cut2 (p6 _ _) (cut (p5 _ _) 
    (cut (mp _ _ (K _ _ _) ((RN _ _ )(p4 _ _))) (K _ _ _))))), },
},
end