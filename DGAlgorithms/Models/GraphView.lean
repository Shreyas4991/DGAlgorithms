import Mathlib

/--
The `View` of a node `v` after `r` rounds.
Currently restricted to topology. Should include all the details of this node.
-/

class Node (V : Type) where
  state : V → α
  active : V → Bool

def View {V : Type} [Node V]
  (G : SimpleGraph V) (v : V) (r : ℕ) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ (G.dist v x < r ∨ G.dist v y < r)
  symm := by
    unfold Symmetric
    intro x y hxy
    constructor
    · apply G.symm hxy.left
      done
    · tauto
      done
  loopless := by
    unfold Irreflexive
    intro x hx
    apply G.loopless x hx.left
    done
