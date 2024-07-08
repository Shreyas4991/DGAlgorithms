import DGAlgorithms.Models.Fingraph
import DGAlgorithms.Models.GraphBasics
import Mathlib

set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace DG

variable (V : Type)
variable [iFin : FinEnum V] [iDec : DecidableEq V] [iRepr: Repr V]


structure PNNet where
  P : Finset (V × ℕ)
  p : V × ℕ → V × ℕ -- Port Map.
  p_inv : ∀ x : V × ℕ, p (p x) = p x


structure SimplePNNet where
  N : PNNet V
  loopless : ∀ v : V, ∀ i j : ℕ, ¬ N.p (v,i) = (v,j)
  no_multi_conn : ∀ v w : V, ∀ i₁ j₁ i₂ j₂ : ℕ,
    N.p (v, i₁) = (w,j₁) → N.p (v, i₂) = (w, j₂) → i₁ = i₂ ∧ j₁ = j₂


-- it got more complicated to just extract indices or use set notation.
-- Had to construct a fintype instance. This was simpler.
abbrev pSet (N : PNNet V) (v : V) : Finset (V × ℕ) := 
  Finset.filter (fun (w,i) => w = v) N.P


abbrev degN (N : PNNet V) (v : V) := (pSet V N v).card

def underlyingFinG (SN : SimplePNNet V) : SimpleFinGraph V := {
  adj := fun v => {w | ∃ i : ℕ, (w, i) ∈ (pSet V SN.N v)}.toFinset,
  symm := by
    sorry
  loopless := by
    sorry
}

end DG
