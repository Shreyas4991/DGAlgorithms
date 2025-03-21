import Mathlib

namespace DGAlgorithms

/-- A Port-Numbered Network.

Each node `v` of the network has some `deg v` ports attached to it. Each port
is attached to another port, given by `pmap`. Function `pmap` is involutive,
that is if `p₁` is connected to `p₂`, then `p₂` is also connected to `p₁`.
 -/
structure PNNetwork (V : Type u) where
  /-- Degree of a node. -/
  deg : V → ℕ
  /-- Map from a given port of a node to the other end of the edge. -/
  pmap : ((v : V) × Fin (deg v)) → ((w : V) × (Fin (deg w)))
  /-- Ensure that ports are properly connected. -/
  pmap_involutive : Function.Involutive pmap

/-- A Simple Port-Numbered Network.

A PN network is simple if it is both loopless and simple, i.e. there are no
duplicate edges.
-/
structure SimplePN (V : Type u) extends PNNetwork V where
  /-- There are no edges from a node to itself. -/
  loopless : ∀ v : V, ∀ i j : Fin (deg v), pmap ⟨v,i⟩ ≠ ⟨v, j⟩
  /-- There is at most one edge between any pair of nodes. -/
  simple : ∀ v : V, ∀ i j : Fin (deg v), (pmap ⟨v, i⟩).fst = (pmap ⟨v, j⟩).fst → i = j

/-- Adjacency relation for a network.

See [Mathlib.SimpleGraph.Adj] for comparison.
-/
def SimplePN.Adj (N : SimplePN V) (u v : V) : Prop :=
  ∃ i, ∃ j, N.pmap ⟨u,i⟩ = ⟨v,j⟩

/-- The induced adjacency relation is symmetric. -/
lemma SimplePN.Adj.symm (N : SimplePN V) : Symmetric N.Adj := by
  intro u v h
  simp_all[SimplePN.Adj]
  cases' h with p₁ h
  cases' h with p₂ h
  use p₂, p₁
  rw [←h, N.pmap_involutive ⟨u, p₁⟩]

/-- The induced adjacency relation is irreflexive.

This essentially says that induced graph is loopless.
-/
lemma SimplePN.Adj.irrefl (N : SimplePN V) : Irreflexive N.Adj := by
  intro u h
  simp[SimplePN.Adj, N.loopless] at h

/-- The natural interpretation of a network as a [Mathlib.SimpleGraph]. -/
def SimplePN.to_SimpleGraph {V : Type*} (N : SimplePN V) : SimpleGraph V where
  Adj := N.Adj
  symm := SimplePN.Adj.symm N
  loopless := SimplePN.Adj.irrefl N

/-- Coersion from [SimplePN] to [SimpleGraph]. -/
instance (V : Type*) : CoeOut (SimplePN V) (SimpleGraph V) where
  coe := SimplePN.to_SimpleGraph

/-- Adjacency in the induced [Mathlib.SimpleGraph] is the same as in the
original network
-/
@[simp] lemma SimplePN.to_SimpleGraph_Adj_iff_Adj (N : SimplePN V) :
    ∀ v w : V, N.to_SimpleGraph.Adj v w ↔ N.Adj v w := by
    intro v w
    constructor
    case mp =>
      intro hconn
      exact hconn
    case mpr =>
      intro hconn
      simp [to_SimpleGraph, hconn]
