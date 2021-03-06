import syntax.syntaxCL data.set.basic

variable {agents : Type}
variable {N : set agents}

open formCL 
open set classical


def regular (agents: Type) (states: Type) (E : states → ((set agents) → (set (set (states))))) :=
  ∀ s: states, ∀ G: set agents, ∀ X: set states, 
    (X ∈ E (s) (G)) → (Xᶜ ∉ E (s) (Gᶜ))

def N_max (agents: Type) (states: Type) (E : states → ((set agents) → (set (set (states))))) := 
  ∀ s: states, ∀ X: set states, 
    (Xᶜ ∉ E (s) (∅)) → (X ∈ E (s) (univ))

----------------------------------------------------------
-- Structures
----------------------------------------------------------
structure playable_effectivity_fun {agents: Type} (states: Type) (ha: nonempty agents) :=
(E : states → (set agents) → (set (set (states))))
(liveness:  ∀ s: states, ∀ G: set agents,
              ∅ ∉ E (s) (G))
(safety:    ∀ s: states, ∀ G: set agents,
              univ ∈ E (s) (G))
(N_max     : N_max agents states E)
(monoticity:∀ s: states, ∀ G: set agents, ∀ X Y: set states,
              X ⊆ Y → X ∈ E (s) (G) → Y ∈ E (s) (G))
(superadd:  ∀ s: states, ∀ G F: set agents, ∀ X Y: set states,
              X ∈ E (s) (G) → Y ∈ E (s) (F) → G ∩ F = ∅ →
                X ∩ Y ∈ E (s) (G ∪ F))

structure semi_playable_effectivity_fun {agents: Type} (states: Type) (ha: nonempty agents) :=
(E : states → ((set agents) → (set (set (states)))))
(semi_liveness:  ∀ s: states, ∀ G: set agents,
                    G ⊂ univ → ∅ ∉ E (s) (G))
(semi_safety:    ∀ s: states, ∀ G: set agents,
                    G ⊂ univ → univ ∈ E (s) (G))
(semi_monoticity:∀ s: states, ∀ G: set agents, ∀ X Y: set states,
                    G ⊂ univ → X ⊆ Y → X ∈ E (s) (G) → Y ∈ E (s) (G))
(semi_superadd:  ∀ s: states, ∀ G F: set agents, ∀ X Y: set states,
                    G ∪ F ⊂ univ → X ∈ E (s) (G) → Y ∈ E (s) (F) → G ∩ F = ∅ →
                      X ∩ Y ∈ E (s) (G ∪ F))

----------------------------------------------------------
-- Set Helper Functions
----------------------------------------------------------
def empty_subset_univ {α: Type} (h: nonempty α): 
  ∅ ⊂ @univ (α) :=
by simp[empty_ssubset, (nonempty_iff_univ_nonempty.mp h)]
  
def empty_union_subset_univ {α: Type} (h: nonempty α): 
  ∅ ∪ ∅ ⊂ @univ (α) :=
by simp[union_self, empty_ssubset, (nonempty_iff_univ_nonempty.mp h)]

def intersect_complement {α: Type} (A B: set α): 
  (A ∩ B)ᶜ ∩ B = Aᶜ ∩ B :=
by simp[compl_inter, inter_distrib_right, compl_inter_self]

def show_complement {α: Type} (A B: set α) (hint: A ∩ B = ∅) (hunion: A ∪ B  = univ): 
  A = Bᶜ :=
begin
  ext,
  have huniv: x ∈ univ, from mem_univ x,
  rw ←hunion at huniv, -- exact hx huniv,
  apply iff.intro,
  {
    intro hx,
    by_contradiction hfalse,
    simp at hfalse,
    have hint': x ∈ B ∩ A, from mem_inter hfalse hx,
      rw inter_comm at hint', -- x ∈ A ∩ B
    exact eq_empty_iff_forall_not_mem.mp hint x hint',
  },
  {
    intro hx,
    by_contradiction hfalse,
    cases huniv,
    { exact hfalse huniv, },
    {exact hx huniv, },
  },
end

----------------------------------------------------------
-- Playable from Semi
----------------------------------------------------------
def playable_from_semi_Nmax_reg (states: Type) (ha: nonempty agents) (semi: semi_playable_effectivity_fun states ha) 
  (hNmax: N_max agents states semi.E) (hReg: regular agents states semi.E): 
  playable_effectivity_fun states ha :=

-- E(s) is live: ∅ ∉ E(s)(N)
-- From semi-playable: S ∈ E(s)(∅) and regularity: S ∈ E(s)(∅) ⇒ ∅ ∉ E(s)(N).
  have hLiveness: ∀ s: states, ∀ G: set agents, ∅ ∉ semi.E (s) (G), from
  begin
    intros s G,
    cases (ssubset_or_eq_of_subset (subset_univ G)),
    {exact semi.semi_liveness s G h,},
    {
      rw h,
      have hS: univ ∈ semi.E (s) (∅), from semi.semi_safety s ∅ (empty_subset_univ ha),
      have hif: univ ∈ semi.E (s) (∅) → univᶜ ∉ semi.E (s) (∅ᶜ), from hReg s ∅ univ,
      simp[compl_univ, compl_empty] at hif,
      exact hif hS,
    },
  end,

  -- E(s) is safe: S ∈ E(s)(N) 
  -- From semi-playable: ∅ ∉ E(s)(∅) and N-maximality: ∅ ∈/ E(s)(∅) ⇒ S ∈ E(s)(N).
  have hSafety: ∀ s: states, ∀ G: set agents, univ ∈ semi.E (s) (G), from 
  begin
    intros s G,
    cases (ssubset_or_eq_of_subset (subset_univ G)),
    {exact semi.semi_safety s G h,},
    {
      rw h,
      have h0: ∅ ∉ semi.E (s) (∅), from semi.semi_liveness s ∅ (empty_subset_univ ha),
      have hif: univᶜ ∉ semi.E (s) (∅) → univ ∈ semi.E (s) (univ), from hNmax s univ,
      simp[compl_univ] at hif,
      exact hif h0,
    }
  end,

-- E(s) is outcome monotonic: ∀X ⊆ Y ⊆ S : X ∈ E(s)(N) ⇒ Y ∈ E(s)(N)
  have hMonoticity: ∀ s: states, ∀ G: set agents, ∀ X Y: set states, X ⊆ Y → X ∈ semi.E (s) (G) → Y ∈ semi.E (s) (G), 
  begin
  -- Assume some X and some Y such that X ⊆ Y ⊆ S and X ∈ E(s)(N)
    intros s G X Y hXY hX,
    cases (ssubset_or_eq_of_subset (subset_univ G)),
    {exact semi.semi_monoticity s G X Y h hXY hX,},
    {
      rw h at *,
      -- Xᶜ ∉ E(s)(∅), from regularity: X ∈ E(s)(N) ⇒ Xᶜ ∉ E(s)(∅), and hX: Xᶜ ∈ E(s)(N)
      have hXc: Xᶜ ∉ semi.E s univᶜ, from hReg s univ X hX,
      simp[compl_univ] at hXc,
      --  Yᶜ ⊆ Xᶜ, from hXY: X ⊆ Y
      have hXYc: Yᶜ ⊆ Xᶜ, from compl_subset_compl.mpr hXY,
      -- Yᶜ ∈ E(s)(∅) ⇒ Xᶜ ∈ E(s)(∅), from semi-playable (monoticity) and hXYc
      have hmono: Yᶜ ∈ semi.E s ∅ → Xᶜ ∈ semi.E s ∅, from semi.semi_monoticity s ∅ Yᶜ Xᶜ (empty_subset_univ ha) hXYc,
      -- Xᶜ ∉ E(s)(∅) ⇒ Yᶜ ∉ E(s)(∅), from the contrapositive of hmono
      have hmono': Xᶜ ∉ semi.E s ∅ → Yᶜ ∉ semi.E s ∅, from mt hmono,
      --  Yᶜ ∉ E(s)(∅), from hXc and hmono'
      have hYc, from hmono' hXc,
      -- Y ∈ E(s)(N), from N-maximality: Yᶜ ∉(s)(∅) ⇒ Y ∈ E(s)(N) and hYc
      exact (hNmax s Y) hYc,
    }
  end,

-- E(s) is superadditive: ∀G, F ⊆ N (where G ∩ F = ∅ and G ∪ F = N), ∀X, Y ⊆ S : X ∈ E(s)(G) and Y ∈ E(s)(F) ⇒ X ∩Y ∈ E(s)(G∪F)
  have hSuperadd: ∀ s: states, ∀ G F: set agents, ∀ X Y: set states, X ∈ semi.E (s) (G) → Y ∈ semi.E (s) (F) → G ∩ F = ∅ → X ∩ Y ∈ semi.E (s) (G ∪ F), from 
  
    have hSuperadd': ∀ s: states, ∀ G F: set agents, ∀ X Y: set states,
      G ∩ F = ∅ → G ∪ F = univ → F ⊂ univ  → X ∈ semi.E (s) (G) → Y ∈ semi.E (s) (F) → 
      X ∩ Y ∈ semi.E (s) (G ∪ F), from 
    begin
      --  Assume some G, F ⊆ N, where G ∩ F = ∅ and G ∪ F = N). Note that G = F. Assume X ∈ E(s)(G) and Y ∈ E(s)(F).
      intros s G F X Y hint hunion hF hX hY,

      -- Assume by contradiction that X ∩ Y ∉ E(s)(G ∪ F = N).
      by_contradiction hfalse,
      rw hunion at hfalse, 

    	-- (X ∩ Y) ∉ E(s)(N) ⇒ (X ∩ Y)ᶜ ∈ E(s)(∅), from the contrapositive of N-maximality: (X ∩ Y)ᶜ ∉ E(s)(∅) ⇒ (X ∩ Y) ∈ E(s)(N)
      -- (X ∩ Y)ᶜ ∈ E(s)(∅), hfalse and above
      have hIntc: ¬(X ∩ Y)ᶜ ∉ semi.E s ∅, 
        from (mt (hNmax s (X ∩ Y))) hfalse,
      simp at hIntc, 

      -- ((X ∩ Y)ᶜ ∩ Y ) ∈ E(s)(F), from semi-playability: (X ∩ Y)ᶜ ∈ E(s)(∅) and Y ∈ E(s)(F) ⇒ (X ∩ Y ∩ Y ) ∈ E(s)(∅ ∪ F), hIntc and hY
      -- (X ∩ Y) ∈ E(s)(F), from above
      have hIntXc: (X ∩ Y)ᶜ ∩ Y ∈ semi.E s (∅ ∪ F),
        from semi.semi_superadd s ∅ F (X ∩ Y)ᶜ Y (by simp [hF]) hIntc hY (empty_inter F),
      simp [intersect_complement] at hIntXc,

      --  Xᶜ ∈ E(s)(F), from semi-playability: (Xᶜ ∩ Y) ∈ E(s)(F) ⇒ Xᶜ ∈ E(s)(F), and hIntXc
      have hXc: Xᶜ ∈ semi.E s F, 
        from semi.semi_monoticity s F (Xᶜ ∩ Y) Xᶜ hF (by simp) hIntXc,

      -- X ∉ E(s)(G), from regularity: Xᶜ ∈ E(s)(F) ⇒ X ∉ E(s)(G), and 1.5.9, given Fᶜ = G, from hint and hunion
      have hX': Xᶜᶜ ∉ semi.E s Fᶜ, 
        from hReg s F Xᶜ hXc,
      simp [(compl_compl X), ←(show_complement G F hint hunion)] at hX', -- hX': X ∉ semi.E s G

      -- Contradiction from hX' and hX
      exact hX' hX,
    end,

  begin
    intros s G F X Y hX hY hint,
    cases (ssubset_or_eq_of_subset (subset_univ (G ∪ F))),
    -- Case: G ∪ F ⊂ N
    {exact semi.semi_superadd s G F X Y h hX hY hint,},
    {
      cases (ssubset_or_eq_of_subset (subset_univ (G))),

      -- Case: G ⊂ N
      {
        simp[inter_comm X Y, inter_comm G F, union_comm G F] at *,
        exact hSuperadd' s F G Y X hint h h_1 hY hX,
      },
      {
        cases (ssubset_or_eq_of_subset (subset_univ (F))),

        -- Case: G = N, F ⊂ N
        { exact hSuperadd' s G F X Y hint h h_2 hX hY, },
        
        -- Case:G = N, F = N (impossible)
        {
          by_contradiction,
          simp [h_1, h_2, inter_self (@univ agents)] at *,
          exact hReg s univ X hX (false.rec (Xᶜ ∈ semi.E s univᶜ) hint),
        },
      },
    },
  end,

  playable_effectivity_fun.mk semi.E hLiveness hSafety hNmax hMonoticity hSuperadd

