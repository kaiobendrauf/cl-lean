import syntax.syntaxCL semantics.semanticsCL

variable {agents : Type}
variable {N : set agents}

open formCL
open set
open frame model
open classical

def regular (f : frame agents) :=
  ∀ s: f.states, ∀ G: set agents, ∀ X: set f.states, 
    X ∈ f.E (s) (G) → Xᶜ ∉ f.E (s) (Gᶜ)

def N_max (f : frame agents):= 
  ∀ s: f.states, ∀ X: set f.states, 
    Xᶜ ∉ f.E (s) (∅) → X ∈ f.E (s) (univ)


structure playable_effectivity_fun (agents: Type) :=
(f : frame agents)
(liveness:  ∀ s: f.states, ∀ G: set agents,
              ∅ ∉ f.E (s) (G))
(safety:    ∀ s: f.states, ∀ G: set agents,
              univ ∈ f.E (s) (G))
(N_max     : N_max f)
(monoticity:∀ s: f.states, ∀ G: set agents, ∀ X Y: set f.states,
              X ⊆ Y → X ∈ f.E (s) (G) → Y ∈ f.E (s) (G))
(superadd:  ∀ s: f.states, ∀ G F: set agents, ∀ X Y: set f.states,
              X ∈ f.E (s) (G) → Y ∈ f.E (s) (F) → G ∩ F = ∅ →
                X ∩ Y ∈ f.E (s) (G ∪ F))

structure semi_playable_effectivity_fun (agents: Type) :=
(f : frame agents)
(semi_liveness:  ∀ s: f.states, ∀ G: set agents,
                    G ⊂ univ → ∅ ∉ f.E (s) (G))
(semi_safety:    ∀ s: f.states, ∀ G: set agents,
                    G ⊂ univ → univ ∈ f.E (s) (G))
(semi_monoticity:∀ s: f.states, ∀ G: set agents, ∀ X Y: set f.states,
                    G ⊂ univ → X ⊆ Y → X ∈ f.E (s) (G) → Y ∈ f.E (s) (G))
(semi_superadd:  ∀ s: f.states, ∀ G F: set agents, ∀ X Y: set f.states,
                    G ∪ F ⊂ univ → X ∈ f.E (s) (G) → Y ∈ f.E (s) (F) → G ∩ F = ∅ →
                      X ∩ Y ∈ f.E (s) (G ∪ F))

def empty_subset_univ {α: Type} (h: nonempty α): ∅ ⊂ @univ (α) :=
  by simp[empty_ssubset, (nonempty_iff_univ_nonempty.mp h)]
-- begin
--   rw empty_ssubset,
--   exact nonempty_iff_univ_nonempty.mp h,
-- end
  
def empty_union_subset_univ {α: Type} (h: nonempty α): ∅ ∪ ∅ ⊂ @univ (α) :=
  by simp[union_self, empty_ssubset, (nonempty_iff_univ_nonempty.mp h)]

def intersect_complement {α: Type} (X Y: set α): (X ∩ Y)ᶜ ∩ Y = Xᶜ ∩ Y :=
  by simp[compl_inter, inter_distrib_right, compl_inter_self]
--   calc (X ∩ Y)ᶜ ∩ X 
--     = (Xᶜ ∪ Yᶜ) ∩ X:
--       by rw compl_inter
-- ... = (Xᶜ ∩ X) ∪ (Yᶜ ∩ X):
--       by rw inter_distrib_right
-- ... = (∅) ∪ (Yᶜ ∩ X):  
--       by rw compl_inter_self
-- ... = Yᶜ ∩ X:
--       by simp

def show_complement {α: Type} (X Y: set α) (hint: X ∩ Y = ∅) (hunion: X ∪ Y  = univ): Xᶜ = Y :=
begin
  ext,
  have huniv: x ∈ univ, from mem_univ x,
  rw ←hunion at huniv,
  apply iff.intro,
  {
    intro hx,
    cases huniv,
  {
    by_contradiction,
    exact hx huniv,
  },
    exact huniv,
  },
  {
    intro hx,
    cases huniv,
    {
      by_contradiction,
      have hint': x ∈ X ∩ Y, from mem_inter huniv hx,
      exact eq_empty_iff_forall_not_mem.mp hint x hint'
    },
    {
      by_contradiction,
      simp at *,
      have hint': x ∈ X ∩ Y, from mem_inter h hx,
      exact eq_empty_iff_forall_not_mem.mp hint x hint',
    }
  }
  
end


def playable_from_semi_Nmax_reg (semi: semi_playable_effectivity_fun agents) (hNmax: N_max semi.f) (hReg: regular semi.f): playable_effectivity_fun agents :=
  have hLiveness: ∀ s: semi.f.states, ∀ G: set agents, ∅ ∉ semi.f.E (s) (G), from
  begin
    intros s G,
    cases (ssubset_or_eq_of_subset (subset_univ G)),
    {exact semi.semi_liveness s G h,},
    {
      rw h,
      have hS: univ ∈ semi.f.E (s) (∅), from semi.semi_safety s ∅ (empty_subset_univ semi.f.ha),
      have hif: univ ∈ semi.f.E (s) (∅) → univᶜ ∉ semi.f.E (s) (∅ᶜ), from hReg s ∅ univ,
      simp[compl_univ, compl_empty] at hif,
      exact hif hS,
    },
  end,

  have hSafety: ∀ s: semi.f.states, ∀ G: set agents, univ ∈ semi.f.E (s) (G), from 
  begin
    intros s G,
    cases (ssubset_or_eq_of_subset (subset_univ G)),
    {exact semi.semi_safety s G h,},
    {
      rw h,
      have h0: ∅ ∉ semi.f.E (s) (∅), from semi.semi_liveness s ∅ (empty_subset_univ semi.f.ha),
      have hif: univᶜ ∉ semi.f.E (s) (∅) → univ ∈ semi.f.E (s) (univ), from hNmax s univ,
      simp[compl_univ] at hif,
      exact hif h0,
    }
  end,

  have hMonoticity: ∀ s: semi.f.states, ∀ G: set agents, ∀ X Y: set semi.f.states, X ⊆ Y → X ∈ semi.f.E (s) (G) → Y ∈ semi.f.E (s) (G), 
  begin
    intros s G X Y hXY hX,
    cases (ssubset_or_eq_of_subset (subset_univ G)),
    {exact semi.semi_monoticity s G X Y h hXY hX,},
    {
      rw h at *,
      have hXc: Xᶜ ∉ semi.f.E s univᶜ, from hReg s univ X hX,
      simp[compl_univ] at hXc,
      have hXYc: Yᶜ ⊆ Xᶜ, from compl_subset_compl.mpr hXY,
      have hmono: Yᶜ ∈ semi.f.E s ∅ → Xᶜ ∈ semi.f.E s ∅, from semi.semi_monoticity s ∅ Yᶜ Xᶜ (empty_subset_univ semi.f.ha) hXYc,
      have hmono': Xᶜ ∉ semi.f.E s ∅ → Yᶜ ∉ semi.f.E s ∅, from mt hmono,
      have hYc, from hmono' hXc,
      have hif: Yᶜ ∉ semi.f.E s ∅ → Y ∈ semi.f.E s univ, from hNmax s Y,
      exact hif hYc,
    }
  end,

  have hSuperadd: ∀ s: semi.f.states, ∀ G F: set agents, ∀ X Y: set semi.f.states, X ∈ semi.f.E (s) (G) → Y ∈ semi.f.E (s) (F) → G ∩ F = ∅ → X ∩ Y ∈ semi.f.E (s) (G ∪ F), from 
  
  have hcaseN: ∀ s: semi.f.states, ∀ X Y: set semi.f.states, X ∈ semi.f.E (s) (univ) → Y ∈ semi.f.E (s) (∅) → X ∩ Y ∈ semi.f.E (s) (univ ∪ ∅), from 
  begin
    intros s X Y hX hY,
    by_contradiction hf,
    simp at *,
    have hifIntc: (X ∩ Y)ᶜ ∉ semi.f.E s ∅ → X ∩ Y ∈ semi.f.E s univ, from hNmax s (X ∩ Y),
    have hifInt: X ∩ Y ∉ semi.f.E s univ → ¬(X ∩ Y)ᶜ ∉ semi.f.E s ∅, from mt hifIntc,
    have hIntc: ¬(X ∩ Y)ᶜ ∉ semi.f.E s ∅, from hifInt hf,
    simp at *,
    
    have hIntc': (X ∩ Y)ᶜ ∩ Y ∈ semi.f.E s (∅ ∪ ∅), from semi.semi_superadd s ∅ ∅ (X ∩ Y)ᶜ Y (empty_union_subset_univ semi.f.ha) hIntc hY (inter_self ∅),
    simp [intersect_complement, union_self] at hIntc',
    have hXc: _, from semi.semi_monoticity s ∅ (Xᶜ ∩ Y) Xᶜ (empty_subset_univ semi.f.ha) (by simp) hIntc',
    have hX': Xᶜᶜ ∉ semi.f.E s ∅ᶜ, from hReg s ∅ Xᶜ hXc,
    simp[compl_compl, compl_empty] at hX',
    exact hX' hX,
  end,


  begin
    intros s G F X Y hX hY hInt,
    cases (ssubset_or_eq_of_subset (subset_univ (G ∪ F))),
    {exact semi.semi_superadd s G F X Y h hX hY hInt,},
    {
      -- by_contradiction hf,
      cases (ssubset_or_eq_of_subset (subset_univ (G))), 
      {
        cases (ssubset_or_eq_of_subset (subset_univ (F))),
        {
          -- Case: G & F both not N
          by_contradiction hf,
          simp at *,
          have hifIntc: _, from hNmax s (X ∩ Y),
          rw hInt at *,
          have hifInt: X ∩ Y ∉ semi.f.E s univ → ¬(X ∩ Y)ᶜ ∉ semi.f.E s ∅, from mt hifIntc,
          rw h at *,
          have hIntc: _, from hifInt hf,
          simp at hIntc,
          have hIntc': _, from semi.semi_superadd s ∅ F (X ∩ Y)ᶜ Y (by simp [h_2]) hIntc hY (by simp),
          rw intersect_complement at hIntc',
          rw union_comm at hIntc',
          rw union_empty at hIntc',
          have hXc: _, from semi.semi_monoticity s F (Xᶜ ∩ Y) Xᶜ h_2 (by simp) hIntc',
          have hX': _, from hReg s F Xᶜ hXc,
          rw compl_compl X at hX',
          rw inter_comm at hInt,
          rw union_comm at h,
          have hcompl: Fᶜ = G, from show_complement F G hInt h,
          rw hcompl at hX',
          exact hX' hX,
        },
        {
          -- Case: F = N
          simp [h_2] at *,
          simp [hInt, inter_comm X Y] at *,
          exact hcaseN s Y X hY hX,
        },
      },
      {
        cases (ssubset_or_eq_of_subset (subset_univ (F))),
        {
          -- Case: G = N
          simp [h_1] at *,
          simp [hInt] at *,
          exact hcaseN s X Y hX hY,
        },
        {
          by_contradiction,
          simp [h_1, h_2, inter_self (@univ agents)] at *,
          exact not_is_empty_iff.mpr semi.f.ha hInt,
        },
      },
    },
  end,

  playable_effectivity_fun.mk semi.f hLiveness hSafety hNmax hMonoticity hSuperadd

