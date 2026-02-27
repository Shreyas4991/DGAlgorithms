import DGAlgorithms.Models.PortNumbering
import DGAlgorithms.Network.PNNetwork
import Mathlib

namespace DGAlgorithms


structure GraphLabelling (V : Type u) (Γ : V → Type v) where -- here Γ is the type of output labels
  network : SimpleGraph V
  output : (v : V) → Γ v -- the output type can in general be dependent on the vertex. We use this for edge labellings

variable (V : Type u) (Γ : V → Type v)

abbrev NodeSubset_Labelling := GraphLabelling V (fun _ => Prop)


structure EdgeLabelling (N : PNNetwork V) (L : Type) extends GraphLabelling V (fun (v : V)  => (Fin (N.deg v)) → L) where
  consistency :
      ∀ v w : V, ∀ i : Fin (N.deg v), ∀ j : Fin (N.deg w), (N.pmap ⟨v,i⟩) = ⟨w,j⟩
        → output v i = output w j
-- the edge labelling must also be consistent


abbrev EdgeSubsetLabelling (N : PNNetwork V) :=
  EdgeLabelling V N Prop


-- edge orientation labellings are anti-consistent
structure EdgeOrientationLabelling (N : PNNetwork V) extends GraphLabelling V (fun (v : V)  => (Set <| Fin (N.deg v))) where
  anti_consistency :
      ∀ v w : V, ∀ i : Fin (N.deg v), ∀ j : Fin (N.deg w), (N.pmap ⟨v,i⟩) = ⟨w,j⟩
        → i ∈ output v ↔  j ∉ output w


abbrev AllowedLabellings := Set (GraphLabelling V Γ)


namespace ExampleProblems

variable {V : Type u} {Γ : V → Type v}

-- trivially label all vertices true
def ex1 (N : PNNetwork V) [SimplePN N] : NodeSubset_Labelling V where
  network := N.to_SimpleGraph
  output := Set.univ

-- trivially label all edges true
def ex2 (N : PNNetwork V) [SimplePN N]: EdgeSubsetLabelling V N where
  network := N.to_SimpleGraph
  output := fun _ => Set.univ
  consistency := by
    intro v w i j h
    simp
    tauto

def is_ProperColouring (N : PNNetwork V) : AllowedLabellings V (fun _ => ColourType) := { L | ∀ v w : V, N.Adj v w → L.output v ≠ L.output  w}

def is_VC (N : PNNetwork V) : AllowedLabellings V (fun _ => Prop) :=
  { L | ∀ v w : V, N.Adj v w → L.output v ∨ (L.output w)}


def isIndepVertexSet (N : PNNetwork V) : AllowedLabellings V (fun _ => Prop) :=
  { L | ∀ v w : V, L.output v ∧ L.output w →  ¬ N.Adj v w}


def isEdgeCover (N : PNNetwork V) :=
  { L : EdgeSubsetLabelling V N | ∀ v w : V, N.Adj v w
      → (∃ i : Fin (N.deg v), L.output v i) ∨ (∃ j : Fin (N.deg w), L.output w j) }

end ExampleProblems

end DGAlgorithms
