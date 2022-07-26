import data.set.basic
import data.list.basic
-- import data.finite.basic
import semantics.true_playability

open set

structure action_pair {agents : Type} {actions : Type} (actionf : agents → set (actions)) :=
(i : agents)
(a : actions)
(h : a ∈ actionf i)

structure strategy_set {agents : Type} {actions : Type} 
  (G : set agents) (actionf : agents → set (actions)) :=
(strat : set (action_pair actionf))
(hG : ∀ i : agents, (i ∈ G) ↔ (∃ a: action_pair actionf, a ∈ strat ∧ a.i = i))
(hunique : ∀ a a' : action_pair actionf, a ∈ strat → a' ∈ strat → a.i = a'.i → a = a')

structure strategic_game_form {agents : Type} {actions: Type} {states: Type} :=
(actionf : agents → set (actions))
(ha : ∀ i : agents, ∅ ≠ (actionf i))
(outcome : strategy_set univ actionf → states)

def effectivity {agents : Type} {actions : Type} {states : Type} 
  (game : @strategic_game_form agents actions states) :
  set (agents) → set (set (states)) :=
λ G, {X : set states | ∃ stratG: strategy_set G game.actionf, 
        ∀ stratU: strategy_set univ game.actionf,
        stratG.strat ⊆ stratU.strat → game.outcome stratU ∈ X}

  -- for every playable effectivity function E 
  -- there exists a strategic game that assigns to coalitions 
  -- exactly the same power as E, and vice versa.

  lemma strategic_games_playability {agents : Type} {states: Type} {actions: Type}
    [hN: nonempty agents] [ha: nonempty actions] (s: states) :
  (∀ E : truly_playable_effectivity_func hN, 
 ∃ game : @strategic_game_form agents actions states, ∀ G : set agents, 
    E.E G = effectivity game G) ∧ 
    (∀ game : @strategic_game_form agents actions states, 
    ∃ E : truly_playable_effectivity_func s hN, ∀ G : set agents, 
    E.E G = effectivity game G) :=
  begin
    split,
    { intro E,
      let game : @strategic_game_form agents actions states:=
        { actionf := λ _, univ,
          ha := λ _, set.empty_ne_univ,
          outcome :=
          begin
            intro strat,
            sorry,
          end,
        },
      sorry, },
    { intro game,
      let E : truly_playable_effectivity_func s hN :=
      { E := λ G: set agents,
        { X | ∃ hG  : (strategy_set G game.actionf), 
              (∀ hGc : (strategy_set (univ: set agents) game.actionf),
                      hG.strat ⊆ hGc.strat → (game.outcome hGc) ∈ X )},
        liveness   := sorry,
        safety     := sorry,
        N_max      := sorry,
        monoticity := sorry,
        superadd   := sorry,
        complete_n := sorry, },
        apply exists.intro E,
        intro G,
        simp[E, effectivity],
    }
  end