import Mathlib
import DGAlgorithms.Models.PortNumbering

namespace DGAlgorithms

#print Computability.FinEncoding -- encoding typeclass to use
#print Computability.Encoding

variable (V : Type u) [iFinV : Fintype V] [iDecEqV : DecidableEq V]


structure LOCAL_Network extends PNNetwork V where
  id_fun : V → ℕ

structure DLOCAL_Network  extends LOCAL_Network V where
  unique_id : Function.Injective id_fun

structure DLOCAL_PolyBounded (P : Polynomial ℕ) extends LOCAL_Network V where
  poly_id_bound : ∀ v, id_fun v ≤ P.eval (Fintype.card V)

structure RLOCAL_Network (bound : ℕ) extends PNNetwork V where
  id_fun : V → PMF ℕ

abbrev RLOCAL_Network_Poly (p : Polynomial ℕ) := RLOCAL_Network V (p.eval <| Fintype.card V)

abbrev DLOCAL.Adj (N : LOCAL_Network V) [SimplePN N.toPNNetwork] (v w : V) := N.toPNNetwork.Adj v w

abbrev DLOCAL.Adj_ID (N : LOCAL_Network V) (id₁ id₂ : ℕ) :=
  ∃ v w : V, N.id_fun v = id₁ ∧ N.id_fun w = id₂ ∧ N.Adj v w

abbrev SimpleGraph.VBall (G : SimpleGraph V) (v : V) (r : ℕ) := {w : V | G.edist v w ≤ r}

abbrev SimpleGraph.EBall (G : SimpleGraph V) (v : V) (r : ℕ)
  : V → V → Prop :=
  fun x y => G.edist v x ≤ r ∧ G.edist v y ≤ r ∧ G.Adj x y

open SimpleGraph

omit iFinV iDecEqV in
lemma EBall_symm (G : SimpleGraph V) (v : V) (r : ℕ)
  : Symmetric (EBall V G v r) := by
  simp [Symmetric, EBall]
  intro x y distx disty adj
  all_goals try tauto

#print SimpleGraph.Subgraph
#print SimpleGraph.IsSubgraph

abbrev GBall (G : SimpleGraph V) (v : V) (r : ℕ) : SimpleGraph.Subgraph G where
  symm := by
    intro x y h
    apply EBall_symm
    assumption

  verts := VBall V G v r
  Adj x y := EBall V G v r x y
  edge_vert := by
    intro x y
    simp
    tauto

  adj_sub := by
    intro x y
    simp




end DGAlgorithms
