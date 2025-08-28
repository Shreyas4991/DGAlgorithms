import Mathlib
import DGAlgorithms.Models.PortNumbering

namespace DGAlgorithms



variable {V : Type u} [iFinV : Fintype V] [iDecEqV : DecidableEq V]
variable {ID : Type u} [iFinD : Fintype ID] [iDecEqID : DecidableEq ID]


structure LOCAL_Network extends SimpleGraph V where
  id_fun : V → ID

structure DLOCAL_Network extends @LOCAL_Network V ID where
  unique_id : @Function.Injective V ID id_fun

abbrev DLOCAL_Adj (N : LOCAL_Network) (id₁ id₂ : α) :=
  ∃ v w : V, N.id_fun v = id₁ ∧ N.id_fun w = id₂ ∧ N.Adj v w

abbrev VBall (G : SimpleGraph V) (v : V) (r : ℕ) := {w : V | G.edist v w ≤ r}

abbrev EBall (G : SimpleGraph V) (v : V) (r : ℕ) : V → V → Prop :=
  fun x y => G.edist v x ≤ r ∧ G.edist v y ≤ r ∧ G.Adj x y

open SimpleGraph

omit iFinV iDecEqV in
lemma EBall_symm (G : SimpleGraph V) (v : V) (r : ℕ) : Symmetric (EBall G v r) := by
  simp [Symmetric, EBall]
  intro x y distx disty adj
  all_goals try tauto

#print Subgraph 
#print IsSubgraph

abbrev GBall (G : SimpleGraph V) (v : V) (r : ℕ) : SimpleGraph.Subgraph G where
  symm := by
    intro x y h
    apply EBall_symm
    assumption

  verts := VBall G v r
  Adj x y := EBall G v r x y
  edge_vert := by
    intro x y
    simp
    tauto

  adj_sub := by
    intro x y
    simp


#print edist_le_ediam

open Computability
#print FinEncoding
#print Encoding
end DGAlgorithms
