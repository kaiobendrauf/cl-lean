/-
Authors : Kai Obendrauf
Following the papers:
  - "A Modal Logic for Coalitional Power in Games" by Mark Pauly
  - "Coalition Logic with Individual, Distributed and Common Knowledge" by Thomas Ågotnes and Natasha Alechina
  - "Strategic Games and Truly Playable Effectivity Functions", by Valentin Groanko, Wojciech Jamroga and Paolo Turrini

This file contains definitions for effectivity structures, N-maximality, regularity.
We define structures for truly, semi- and playable effectivity structure.
A playable effectivity structure can be created from from a semi-playable one which is regular and N-maximal.
A truly playable effectivity structure can be created from from a playable one with a finite domain.
-/

import order.filter.basic

open set

----------------------------------------------------------
-- Effectivity Structures Type
----------------------------------------------------------
@[simp] def effectivity_struct (agents states : Type) := 
  states → (set agents) → (set (set (states)))

----------------------------------------------------------
-- Definitions N maximality, regularity and principal
----------------------------------------------------------

def N_max {agents states : Type} (E : (effectivity_struct agents states)) :=
∀ s : states, ∀ X : set states, (Xᶜ ∉ E (s) (∅)) → (X ∈ E (s) (univ))

def regular {agents states : Type} (E : (effectivity_struct agents states)) :=
∀ s : states, ∀ G : (set agents), ∀ X : (set states), (X ∈ E (s) (G)) → (Xᶜ ∉ E (s) (Gᶜ))

----------------------------------------------------------
-- Playability Structures
----------------------------------------------------------
structure playable_effectivity_struct (agents states : Type) :=
(E          : effectivity_struct agents states)
(liveness   : ∀ s : states, ∀ G : set agents, ∅ ∉ E (s) (G))
(safety     : ∀ s : states, ∀ G : set agents, univ ∈ E (s) (G))
(N_max      : N_max E)
(mono       : ∀ s : states, ∀ G : set agents, ∀ X Y : set states,
                X ⊆ Y → X ∈ E (s) (G) → Y ∈ E (s) (G))
(superadd   : ∀ s : states, ∀ G F : set agents, ∀ X Y : set states,
                X ∈ E (s) (G) → Y ∈ E (s) (F) → G ∩ F = ∅ →
                X ∩ Y ∈ E (s) (G ∪ F))

structure semi_playable_effectivity_struct (agents states : Type) :=
(E                : effectivity_struct agents states)
(semi_liveness    : ∀ s : states, ∀ G : set agents,
                      G ⊂ univ → ∅ ∉ E (s) (G))
(semi_safety      : ∀ s : states, ∀ G : set agents,
                      G ⊂ univ → univ ∈ E (s) (G))
(semi_mono        : ∀ s : states, ∀ G : set agents, ∀ X Y : set states,
                      G ⊂ univ → X ⊆ Y → X ∈ E (s) (G) → Y ∈ E (s) (G))
(semi_superadd    : ∀ s : states, ∀ G F : set agents, ∀ X Y : set states,
                      G ∪ F ⊂ univ → X ∈ E (s) (G) → Y ∈ E (s) (F) → G ∩ F = ∅ →
                      X ∩ Y ∈ E (s) (G ∪ F))

structure truly_playable_effectivity_struct (agents states : Type) 
  extends playable_effectivity_struct agents states :=
(principal_E_s_empty : ∀ s, ∃ X, X ∈ E s ∅ ∧ ∀ Y, Y ∈ E s ∅ → X ⊆ Y)


----------------------------------------------------------
-- Set Helper Functions
----------------------------------------------------------
def empty_subset_univ {α : Type} (h : nonempty α) : 
  ∅ ⊂ @univ (α) := 
by simp[empty_ssubset, (nonempty_iff_univ_nonempty.mp h)]
  
def empty_union_subset_univ {α : Type} (h : nonempty α) : 
  ∅ ∪ ∅ ⊂ @univ (α) := 
by simp[union_self, empty_ssubset, (nonempty_iff_univ_nonempty.mp h)]

def intersect_complement {α : Type} (A B : set α) : 
  (A ∩ B)ᶜ ∩ B = Aᶜ ∩ B := 
by simp[compl_inter, inter_distrib_right, compl_inter_self]

def show_complement {α : Type} (A B : set α) (hint : A ∩ B = ∅) (hunion : A ∪ B  = univ) : 
  A = Bᶜ := 
begin
  ext,
  have huniv : x ∈ univ, from mem_univ x,
  rw ←hunion at huniv, -- exact hx huniv,
  apply iff.intro,

  { intro hx,
    by_contradiction hfalse,
    simp at hfalse,
    have hint' : x ∈ B ∩ A, from mem_inter hfalse hx,
      rw inter_comm at hint', -- x ∈ A ∩ B
    exact eq_empty_iff_forall_not_mem.mp hint x hint', },

  { intro hx,
    by_contradiction hfalse,
    cases huniv,
    { exact hfalse huniv, },
    {exact hx huniv, }, },
end

----------------------------------------------------------
-- Playable from Semi
----------------------------------------------------------
def playable_from_semi_Nmax_reg {agents : Type} (states : Type) [ha : nonempty agents]
  (semi : semi_playable_effectivity_struct agents states) 
  (hNmax : N_max semi.E) (hReg : regular semi.E) : 
  playable_effectivity_struct agents states := 

-- E(s) is live : ∅ ∉ E(s)(N)
  have hLiveness : ∀ s : states, ∀ G : set agents, ∅ ∉ semi.E (s) (G), from
  begin
    -- asume s and G
    intros s G,
    -- either G ⊂ N, or G = N
    cases (ssubset_or_eq_of_subset (subset_univ G)),
    -- if G ⊂ N, liveness follows from semi-playability liveness
    {exact semi.semi_liveness s G h,},
    -- if G = N, liveness follows from semi-playable : S ∈ E(s)(∅) 
    -- and regularity : S ∈ E(s)(∅) ⇒ ∅ ∉ E(s)(N).
    { rw h,
      have hS : univ ∈ semi.E (s) (∅), from semi.semi_safety s ∅ (empty_subset_univ ha),
      have hif : univ ∈ semi.E (s) (∅) → univᶜ ∉ semi.E (s) (∅ᶜ), from hReg s ∅ univ,
      simp[compl_univ, compl_empty] at hif,
      exact hif hS, },
  end,

  -- E(s) is safe : S ∈ E(s)(N) 
  have hSafety : ∀ s : states, ∀ G : set agents, univ ∈ semi.E (s) (G), from 
  begin 
    -- asume s and G
    intros s G,
    -- either G ⊂ N, or G = N
    cases (ssubset_or_eq_of_subset (subset_univ G)),
    -- if G ⊂ N, safeness follows from semi-playability safeness
    {exact semi.semi_safety s G h,},
    -- if G = N, safety follows from semi-playable : ∅ ∉ E(s)(∅) 
    -- and N-maximality : ∅ ∈/ E(s)(∅) ⇒ S ∈ E(s)(N).

    { rw h,
      have h0 : ∅ ∉ semi.E (s) (∅), from semi.semi_liveness s ∅ (empty_subset_univ ha),
      have hif : univᶜ ∉ semi.E (s) (∅) → univ ∈ semi.E (s) (univ), from hNmax s univ,
      simp[compl_univ] at hif,
      exact hif h0, }
  end,

-- E(s) is outcome monotonic : ∀X ⊆ Y ⊆ S : X ∈ E(s)(N) ⇒ Y ∈ E(s)(N)
  have hMonoticity : ∀ s : states, ∀ G : set agents, 
        ∀ X Y : set states, X ⊆ Y → X ∈ semi.E (s) (G) → Y ∈ semi.E (s) (G), 
  begin
  -- Assume some X and some Y such that X ⊆ Y ⊆ S and X ∈ E(s)(N)
    intros s G X Y hXY hX,
    cases (ssubset_or_eq_of_subset (subset_univ G)),
    {exact semi.semi_mono s G X Y h hXY hX,},

    { rw h at *,
      -- Xᶜ ∉ E(s)(∅), from regularity : X ∈ E(s)(N) ⇒ Xᶜ ∉ E(s)(∅), and hX : Xᶜ ∈ E(s)(N)
      have hXc : Xᶜ ∉ semi.E s univᶜ, from hReg s univ X hX,
      simp[compl_univ] at hXc,
      --  Yᶜ ⊆ Xᶜ, from hXY : X ⊆ Y
      have hXYc : Yᶜ ⊆ Xᶜ, from compl_subset_compl.mpr hXY,
      -- Yᶜ ∈ E(s)(∅) ⇒ Xᶜ ∈ E(s)(∅), from semi-playable (monotonicity) and hXYc
      have hmono : Yᶜ ∈ semi.E s ∅ → Xᶜ ∈ semi.E s ∅, 
        from semi.semi_mono s ∅ Yᶜ Xᶜ (empty_subset_univ ha) hXYc,
      -- Xᶜ ∉ E(s)(∅) ⇒ Yᶜ ∉ E(s)(∅), from the contrapositive of hmono
      have hmono' : Xᶜ ∉ semi.E s ∅ → Yᶜ ∉ semi.E s ∅, from mt hmono,
      --  Yᶜ ∉ E(s)(∅), from hXc and hmono'
      have hYc, from hmono' hXc,
      -- Y ∈ E(s)(N), from N-maximality : Yᶜ ∉(s)(∅) ⇒ Y ∈ E(s)(N) and hYc
      exact (hNmax s Y) hYc, }
  end,

-- E(s) is superadditive : ∀G, F ⊆ N (where G ∩ F = ∅ and G ∪ F = N), 
-- ∀X, Y ⊆ S : X ∈ E(s)(G) and Y ∈ E(s)(F) ⇒ X ∩Y ∈ E(s)(G∪F)
  have hSuperadd : ∀ s : states, ∀ G F : set agents, ∀ X Y : set states, 
        X ∈ semi.E (s) (G) → Y ∈ semi.E (s) (F) → G ∩ F = ∅ → X ∩ Y ∈ semi.E (s) (G ∪ F), from 
  
    -- Either F ⊂ N or G ⊂ N (or both). Let F be either F or G,
    -- such that F ⊂ N , and let G be the other set
    have hSuperadd' : ∀ s : states, ∀ G F : set agents, ∀ X Y : set states,
      G ∩ F = ∅ → G ∪ F = univ → F ⊂ univ → X ∈ semi.E (s) (G) → Y ∈ semi.E (s) (F) → 
      X ∩ Y ∈ semi.E (s) (G ∪ F), from 
    begin
      -- Assume some G, F ⊆ N, where G ∩ F = ∅ and G ∪ F = N). Note that G = F. 
      -- Assume X ∈ E(s)(G) and Y ∈ E(s)(F).
      intros s G F X Y hint hunion hF hX hY,

      -- Assume by contradiction that X ∩ Y ∉ E(s)(G ∪ F = N).
      by_contradiction hfalse,
      rw hunion at hfalse, 

    	-- (X ∩ Y) ∉ E(s)(N) ⇒ (X ∩ Y)ᶜ ∈ E(s)(∅),  
      -- from the contrapositive of N-maximality : (X ∩ Y)ᶜ ∉ E(s)(∅) ⇒ (X ∩ Y) ∈ E(s)(N)
      -- (X ∩ Y)ᶜ ∈ E(s)(∅), hfalse and above
      have hIntc : ¬(X ∩ Y)ᶜ ∉ semi.E s ∅, 
        from (mt (hNmax s (X ∩ Y))) hfalse,
      simp at hIntc, 

      -- ((X ∩ Y)ᶜ ∩ Y ) ∈ E(s)(F), from semi-playability : (X ∩ Y)ᶜ ∈ E(s)(∅) 
      -- and Y ∈ E(s)(F) ⇒ ((X ∩ Y)ᶜ ∩ Y ) ∈ E(s)(∅ ∪ F), hIntc and hY
      -- (Xᶜ ∩ Y) ∈ E(s)(F), from above
      have hIntXc : (X ∩ Y)ᶜ ∩ Y ∈ semi.E s (∅ ∪ F),
        from semi.semi_superadd s ∅ F (X ∩ Y)ᶜ Y (by simp [hF]) hIntc hY (empty_inter F),
      simp [intersect_complement] at hIntXc,

      --  Xᶜ ∈ E(s)(F), from semi-playability : (Xᶜ ∩ Y) ∈ E(s)(F) ⇒ Xᶜ ∈ E(s)(F), and hIntXc
      have hXc : Xᶜ ∈ semi.E s F, 
        from semi.semi_mono s F (Xᶜ ∩ Y) Xᶜ hF (by simp) hIntXc,

      -- X ∉ E(s)(G), from regularity : Xᶜ ∈ E(s)(F) ⇒ X ∉ E(s)(G), 
      -- and hXc, given Fᶜ = G, from hint and hunion
      have hX' : Xᶜᶜ ∉ semi.E s Fᶜ, 
        from hReg s F Xᶜ hXc,
      simp [(compl_compl X), ←(show_complement G F hint hunion)] at hX', -- hX' : X ∉ semi.E s G

      -- Contradiction from hX' and hX
      exact hX' hX,
    end,

  begin
    intros s G F X Y hX hY hint,
    cases (ssubset_or_eq_of_subset (subset_univ (G ∪ F))),
    -- Case : G ∪ F ⊂ N
    {exact semi.semi_superadd s G F X Y h hX hY hint,},

    { cases (ssubset_or_eq_of_subset (subset_univ (G))),

      -- Case : G ⊂ N
      { simp[inter_comm X Y, inter_comm G F, union_comm G F] at *,
        exact hSuperadd' s F G Y X hint h h_1 hY hX, },

      -- Case : F ⊂ N
      { cases (ssubset_or_eq_of_subset (subset_univ (F))),

        -- Case : G = N, F ⊂ N
        { exact hSuperadd' s G F X Y hint h h_2 hX hY, },
        
        -- Case : G = N, F = N (impossible)
        { by_contradiction,
          simp [h_1, h_2, inter_self (@univ agents)] at *,
          exact hReg s univ X hX (false.rec (Xᶜ ∈ semi.E s univᶜ) hint), }, }, },
  end,

  playable_effectivity_struct.mk semi.E hLiveness hSafety hNmax hMonoticity hSuperadd


----------------------------------------------------------
-- True Playability
----------------------------------------------------------

@[simp] def truly_playable_from_finite {agents states : Type} [hS : fintype states]
  (play : playable_effectivity_struct agents states) : 
  truly_playable_effectivity_struct agents states := 
{ principal_E_s_empty :=
  begin
    intro s,
    -- E (s) (∅) is nonempty by safety
    have hnempty : (finite.to_finset (finite.of_fintype (play.E s ∅))).nonempty, from 
    begin
      rw finite.to_finset.nonempty,
      apply nonempty_def.mpr,
      apply exists.intro univ,
      exact play.safety s ∅, 
    end,
    -- E (s) (∅) has some minimal element because it it finite
    have hminimal := 
      finset.exists_minimal (finite.to_finset (finite.of_fintype (play.E s ∅))) hnempty,
    cases hminimal with X hminimal,
    cases hminimal with hX hminimal,
    simp only [finite.mem_to_finset, lt_eq_ssubset] at hX hminimal,
    apply exists.intro X,
    split,
    -- That element is in E (s) (∅)
    { exact hX, },
    -- There is only one minimum element
    { -- If there were two minimal elements X and Y
      intros Y hY,
      -- by superadditivity (X ∩ Y) ∈ E (s)(∅), and thus X = Y.
      cases em (X = Y),
      { exact eq.subset h, },
      { have hun := play.superadd s _ _ _ _ hX hY (empty_inter ∅),
        rw empty_union at hun,
        by_contradiction hf,
        cases ssubset_or_eq_of_subset (inter_subset_left X Y),
        { exact hminimal (X ∩ Y) hun h_1, },
        { rw inter_eq_left_iff_subset at h_1,
          exact hf h_1, }, }, },
    end,
  .. play }