import Mathlib

namespace DGAlgorithms

section PNNetwork

section Port

def Port (PortValid : V × P → Prop) := Subtype PortValid

variable {V P : Type*} {PortValid : V × P → Prop} (vp : Port PortValid)

abbrev Port.node : V := vp.val.1
abbrev Port.index : P := vp.val.2
abbrev Port.is_valid : PortValid vp.val := vp.prop

-- @[simp]
-- lemma Port.port'_node : vp.port'.node = vp.node := by rfl
-- @[simp]
-- lemma Port.port'_index : vp.port'.index = vp.index := by rfl

end Port

/-- A PNNetwork.
 -/
@[ext, grind]
structure PNNetwork (V P : Type*) where
  PortValid : V × P → Prop
  pmap : Port PortValid → Port PortValid
  pmap_involutive : Function.Involutive pmap


abbrev PNNetwork.Port (N : PNNetwork V P) := DGAlgorithms.Port N.PortValid

def PNNetwork.Port.connNode {N : PNNetwork V P} : N.Port → V := Port.node ∘ N.pmap

variable {V P : Type*} (N : PNNetwork V P)

@[simp]
lemma PNNetwork.pmap_pmap : ∀ vp : N.Port, N.pmap (N.pmap vp) = vp := N.pmap_involutive

@[simp]
lemma PNNetwork.pmap_injective : ∀ vp₁ vp₂ : N.Port, N.pmap vp₁ = N.pmap vp₂ → vp₁ = vp₂ := N.pmap_involutive.injective

section Neighbors


/-- Adjacency relation for a network.
-/
def PNNetwork.Adj (u v : V) : Prop :=
  ∃ vp : N.Port, vp.node = u ∧ (N.pmap vp).node = v

/-- The induced adjacency relation is symmetric. -/
@[simp, symm]
lemma PNNetwork.Adj.symm : ∀ u v, N.Adj u v ↔ N.Adj v u := by
  intro u v
  constructor
  all_goals intro h; use (N.pmap h.choose); simp_all [h.choose_spec]

lemma PNNetwork.Adj.symmetric : Symmetric (Adj N) := by
  intro u v h
  simp_all


@[simp]
lemma PNNetwork.Adj_of_pmap : ∀ vp : N.Port, N.Adj vp.node (N.pmap vp).node := by
  intro vp
  use vp


lemma PNNetwork.Adj_def : N.Adj u v ↔ ∃ vp : N.Port, vp.node = u ∧ (N.pmap vp).node = v := by rfl

variable (v : V)

def PNNetwork.neighborSet : Set V := { u : V | N.Adj v u }

@[simp]
lemma PNNetwork.mem_neighborSet : ∀ u, u ∈ N.neighborSet v ↔ N.Adj v u := by intro u; rfl

@[grind, symm]
lemma PNNetwork.mem_neighborSet_symm : ∀ v u : V, u ∈ N.neighborSet v ↔ v ∈ N.neighborSet u := by simp

variable {N v u} in
noncomputable
abbrev PNNetwork.mem_neighborSet_toPort (h : u ∈ N.neighborSet v) : N.Port := h.out.choose

def PNNetwork.neighborPortSet : Set N.Port := { vp : N.Port | vp.node = v }

@[simp]
lemma PNNetwork.mem_neighborPortSet : ∀ up, up ∈ N.neighborPortSet v ↔ up.node = v := by intro up; rfl

@[simp]
lemma PNNetwork.neighborPortSet_image_connNode_eq_neighborSet : PNNetwork.Port.connNode '' (N.neighborPortSet v) = N.neighborSet v := by rfl

@[simp]
lemma PNNetwork.mem_neighborSet_toPort_mem_neighborPortSet : ∀ u, (h : u ∈ N.neighborSet v) → (mem_neighborSet_toPort h) ∈ N.neighborPortSet v := by
  intro u hu
  simp [hu.out.choose_spec]

@[simp]
lemma PNNetwork.pmap_of_mem_neighborSet_toPort : ∀ u, (h : u ∈ N.neighborSet v) → (N.pmap (mem_neighborSet_toPort h)).node = u := by
  intro u hu
  simp [hu.out.choose_spec]

def PNNetwork.neighborIndexSet : Set P := { p : P | N.PortValid (v, p) }

@[simp]
lemma PNNetwork.mem_neighborIndexSet : ∀ p, p ∈ N.neighborIndexSet v ↔ N.PortValid (v, p) := by intro up; rfl

@[simp]
lemma PNNetwork.port_index_mem_neighborIndexSet : ∀ vp : N.Port, vp.index ∈ N.neighborIndexSet vp.node := by
  intro vp
  simpa using vp.is_valid

@[simp]
lemma PNNetwork.mem_neighborSet_index_mem_neigbhorIndexSet : ∀ up, up ∈ N.neighborPortSet v → up.index ∈ N.neighborIndexSet v := by
  intro up hup
  subst hup
  exact port_index_mem_neighborIndexSet N up

@[simp]
lemma PNNetwork.neighborPortSet_image_index_eq_neighborIndexSet : Port.index '' N.neighborPortSet v = N.neighborIndexSet v := by
  ext p
  constructor
  · intro h
    obtain ⟨⟨vp, hvp⟩, h⟩ := h
    rw [←h.left, ←h.right]
    exact port_index_mem_neighborIndexSet _ _
  · intro h
    rw [Set.mem_image]
    use ⟨(v, p), h⟩
    simp

open Finset

def PNNetwork.neighborFinset [Fintype (N.neighborSet v)] : Finset V := (N.neighborSet v).toFinset

@[simp]
lemma PNNetwork.mem_neighborFinset [Fintype (N.neighborSet v)] : ∀ u, u ∈ N.neighborFinset v ↔ N.Adj v u := by
  simp [neighborFinset]

variable [vFinite : Fintype (N.neighborPortSet v)]

def PNNetwork.neighborPortFinset : Finset N.Port := (N.neighborPortSet v).toFinset

@[simp]
lemma PNNetwork.mem_neighborPortFinset : ∀ up, up ∈ N.neighborPortFinset v ↔ up.node = v := by
  simp [neighborPortFinset]

open Classical in
noncomputable
instance : Fintype (N.neighborSet v) := by
  let f : ↑(N.neighborPortSet v) → ↑(N.neighborSet v) := fun up ↦
    ⟨(N.pmap up.val).node, by
      have h := up.prop
      have h' := (N.mem_neighborPortSet _ up).eq ▸ h
      simp [←h']
    ⟩
  have f_surj : Function.Surjective f := by
    intro u
    obtain ⟨u, hu⟩ := u
    rw [PNNetwork.mem_neighborSet] at hu
    obtain ⟨vp, h⟩ := hu
    use ⟨vp, h.left⟩
    simp_all [f]
  exact Fintype.ofSurjective f f_surj


def PNNetwork.degree : ℕ := #(N.neighborPortFinset v)

end Neighbors

section SimplePN

/-- A Simple Port-Numbered Network.

A PN network is simple if it is both loopless and simple, i.e. there are no
duplicate edges.
-/
class SimplePN {V : Type u} (N : PNNetwork V P) : Prop where
  /-- There are no edges from a node to itself. -/
  loopless : ∀ vp : N.Port, (N.pmap vp).node ≠ vp.node
  /-- There is at most one edge between any pair of nodes. -/
  simple : ∀ vp₁ vp₂ : N.Port, vp₁.node = vp₂.node → (N.pmap vp₁).node = (N.pmap vp₂).node → vp₁ = vp₂


variable [s : SimplePN N]

/-- The induced adjacency relation is irreflexive.

This essentially says that induced graph is loopless.
-/
lemma PNNetwork.Adj.irrefl : Std.Irrefl (Adj N) := by
  constructor
  intro u h
  obtain ⟨vp, h, h'⟩ := h
  apply s.loopless vp
  simp_all

/-- The natural interpretation of a network as a [Mathlib.SimpleGraph]. -/
def PNNetwork.to_SimpleGraph : SimpleGraph V where
  Adj := Adj N
  symm := PNNetwork.Adj.symmetric N
  loopless := PNNetwork.Adj.irrefl N

/-- Adjacency in the induced [Mathlib.SimpleGraph] is the same as in the
original network.
-/
@[simp] lemma PNNetwork.to_SimpleGraph_Adj_iff_Adj :
    ∀ v w : V, N.to_SimpleGraph.Adj v w ↔ Adj N v w := by
    intro v w
    constructor
    case mp =>
      intro hconn
      exact hconn
    case mpr =>
      intro hconn
      simp [to_SimpleGraph, hconn]

instance PNNetwork.to_SimpleGraph_LocallyFinite [inst : ∀ v : V, Fintype (N.neighborSet v)] : N.to_SimpleGraph.LocallyFinite := inst

instance {v : V} [inst : Fintype (N.neighborSet v)] : Fintype (N.to_SimpleGraph.neighborSet v) := inst

@[simp]
lemma PNNetwork.card_neighborSet_eq_card_neighborPortSet [Fintype (N.neighborPortSet v)] :
    (N.neighborFinset v).card = (N.neighborPortFinset v).card := by
  classical
  symm
  apply Finset.card_bij (fun vp h ↦ vp.connNode)
  · simp [Port.connNode, Adj_def]
    intro vp hvp; use vp
  · intro _ _ _ _ _
    apply s.simple
    simp_all
    assumption
  · simp_all [Adj_def, Port.connNode]

@[simp]
lemma PNNetwork.to_SimpleGraph_neighborSet_eq_neighborSet :
    N.to_SimpleGraph.neighborSet = N.neighborSet := by rfl
@[simp]
lemma PNNetwork.to_SimpleGraph_neighborFinset_eq_neighborSet :
    N.to_SimpleGraph.neighborFinset = N.neighborFinset := by rfl

-- variable [locallyFinite : ∀ v : V, Fintype (N.neighborPortSet v)]
/-- Degree in the induced [Mathlib.SimpleGraph] is the same as in the original
network.
-/
@[simp]
lemma PNNetwork.to_SimpleGraph_degree_eq_deg {v : V} [Fintype (N.neighborPortSet v)] :
    N.to_SimpleGraph.degree v = N.degree v := by
  simp [degree, SimpleGraph.degree]


end SimplePN
