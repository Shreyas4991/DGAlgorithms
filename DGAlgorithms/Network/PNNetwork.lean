import Mathlib

/-!
# Port-Numbered Networks

In this file, we define PN Networks and what it means for a network to be
simple. We then provide the natural coersion from the simple network into a
[Mathlib.SimpleGraph]. Finally, we prove some simplification lemmas.
-/

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

/-- Another way to define adjacency using only one exists. -/
def SimplePN.Adj' (N : SimplePN V) (u v : V) : Prop :=
  ∃ i, (N.pmap ⟨u, i⟩).fst = v

/-- Both definitions of adjacency are equal. -/
lemma SimplePN.Adj_eq_Adj' (N : SimplePN V) : N.Adj = N.Adj' := by
  ext u v
  constructor
  case mp =>
    intro h
    obtain ⟨i, j, h⟩ := h
    use i
    simp_all
  case mpr =>
    intro h
    obtain ⟨i, h⟩ := h
    subst h
    use i, (N.pmap ⟨u, i⟩).snd

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
lemma SimplePN.Adj.irrefl (N : SimplePN V) : Std.Irrefl N.Adj := by
  sorry


/-- The natural interpretation of a network as a [Mathlib.SimpleGraph]. -/
def SimplePN.to_SimpleGraph {V : Type*} (N : SimplePN V) : SimpleGraph V where
  Adj := N.Adj
  symm := SimplePN.Adj.symm N
  loopless := SimplePN.Adj.irrefl N

/-- Coersion from [SimplePN] to [SimpleGraph]. -/
instance (V : Type*) : CoeOut (SimplePN V) (SimpleGraph V) where
  coe := SimplePN.to_SimpleGraph

/-- Adjacency in the induced [Mathlib.SimpleGraph] is the same as in the
original network.
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

/-- Networks always induce a locally finite graph. -/
noncomputable instance SimplePN.to_SimpleGraph_LocallyFinite (N : SimplePN V) : N.to_SimpleGraph.LocallyFinite := by
  intro v
  unfold SimpleGraph.neighborSet to_SimpleGraph
  conv =>
    enter [1, 1, 1, w, 1, 1]
    rw [Adj_eq_Adj']
  unfold Adj'
  apply Set.Finite.fintype
  exact Set.toFinite {w | ∃ i, (N.pmap ⟨v, i⟩).fst = w}

/-- Degree in the induced [Mathlib.SimpleGraph] is the same as in the original
network.
-/
@[simp] lemma SimplePN.to_SimpleGraph_degree_eq_deg (N : SimplePN V) :
    ∀ v : V, N.to_SimpleGraph.degree v = N.deg v := by
  intro v

  -- Unfold the definition of degree
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset, Set.toFinset_card]

  -- We provide a bijection from Fin (N.deg v) to neighbors of v
  let f : Fin (N.deg v) → { w : V // N.Adj v w } := fun i ↦ ⟨(N.pmap ⟨v, i⟩).fst, by
    unfold Adj
    use i
    use ⟨(N.pmap ⟨v, i⟩).snd, by simp⟩
  ⟩

  have f_bij : Function.Bijective f := by
    constructor
    · intro i j h
      exact N.simple v i j (Subtype.ext_iff.mp h)
    · intro u
      use u.property.choose
      have ⟨j, hj⟩ := u.property.choose_spec
      simp [f, hj]

  -- Write n as #(Fin n)
  rw [←Finset.card_fin (N.deg v)]

  -- Now the result is immediate
  symm
  apply Finset.card_bijective f f_bij
  simp_all
