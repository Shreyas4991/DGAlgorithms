import Mathlib

namespace DGAlgorithms

section PNNetwork

section Port
/-- A simple port type: a pair of a vertex and ℕ. -/
def Port' (V P : Type*) := V × P

abbrev Port'.node (V P : Type*) (vp : Port' V P) : V := vp.fst
abbrev Port'.index (V P : Type*) (vp : Port' V P) : P := vp.snd

def Port (PortValid : Port' V P → Prop) := Subtype PortValid

variable {V P : Type*} {PortValid : Port' V P → Prop} (vp : Port PortValid)

abbrev Port.port' : Port' V P := vp.val
abbrev Port.node : V := vp.port'.1
abbrev Port.index : P := vp.port'.2
abbrev Port.is_valid : PortValid vp.port' := vp.prop

@[simp]
lemma Port.port'_node : vp.port'.node = vp.node := by rfl
@[simp]
lemma Port.port'_index : vp.port'.index = vp.index := by rfl

end Port

/-- A PNNetwork.
 -/
@[ext, grind]
structure PNNetwork (V P : Type*) where
  PortValid : Port' V P → Prop
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
@[symm]
lemma PNNetwork.Adj.symm : Symmetric (Adj N) := by
  intro u v h
  obtain ⟨vp, h, h'⟩ := h
  use (N.pmap vp)
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

def PNNetwork.neighborPortSet : Set N.Port := { vp : N.Port | vp.node = v }

@[simp]
lemma PNNetwork.mem_neighborPortSet : ∀ up, up ∈ N.neighborPortSet v ↔ up.node = v := by intro up; rfl

@[simp]
lemma PNNetwork.neighborPortSet_image_connNode_eq_neighborSet : PNNetwork.Port.connNode '' (N.neighborPortSet v) = N.neighborSet v := by rfl

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
  symm := PNNetwork.Adj.symm N
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

noncomputable instance PNNetwork.to_SimpleGraph_LocallyFinite [inst : ∀ v : V, Fintype (N.neighborSet v)] : N.to_SimpleGraph.LocallyFinite := inst

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

section BoxProd

def PNNetwork.boxProd (N₁ : PNNetwork V₁ P₁) (N₂ : PNNetwork V₂ P₂) : PNNetwork (V₁ × V₂) (P₁ × P₂) where
  PortValid := fun ((v₁, v₂), (p₁, p₂)) ↦ N₁.PortValid (v₁, p₁) ∧ N₂.PortValid (v₂, p₂)
  pmap := fun vp ↦
    let uq₁ := N₁.pmap ⟨(vp.val.1.1, vp.val.2.1), vp.prop.left⟩
    let uq₂ := N₂.pmap ⟨(vp.val.1.2, vp.val.2.2), vp.prop.right⟩
    ⟨((uq₁.node, uq₂.node), (uq₁.index, uq₂.index)), And.intro uq₁.is_valid uq₂.is_valid⟩
  pmap_involutive := by
    intro vp
    simp_all
    eta_struct
    rfl

/-- Box product of PNNetworks. -/
infixl:70 " □ " => PNNetwork.boxProd

lemma PNNetwork.boxProd.pmap_def (N₁ : PNNetwork V₁ P₁) (N₂ : PNNetwork V₂ P₂) :
    ∀ vp, (N₁ □ N₂).pmap vp = ⟨(
      ((N₁.pmap ⟨(vp.node.1, vp.index.1), vp.is_valid.1⟩).node, (N₂.pmap ⟨(vp.node.2, vp.index.2), vp.is_valid.2⟩).node),
      ((N₁.pmap ⟨(vp.node.1, vp.index.1), vp.is_valid.1⟩).index, (N₂.pmap ⟨(vp.node.2, vp.index.2), vp.is_valid.2⟩).index)),
      And.intro (N₁.pmap ⟨(vp.node.1, vp.index.1), vp.is_valid.1⟩).is_valid (N₂.pmap ⟨(vp.node.2, vp.index.2), vp.is_valid.2⟩).is_valid⟩ := by
    intro vp; rfl

lemma PNNetwork.boxProd.pmap_eq_iff (N₁ : PNNetwork V₁ P₁) (N₂ : PNNetwork V₂ P₂) :
    ∀ vp up, (N₁ □ N₂).pmap vp = up ↔
    N₁.pmap ⟨(vp.node.1, vp.index.1), vp.is_valid.1⟩ = ⟨(up.node.1, up.index.1), up.is_valid.1⟩ ∧
    N₂.pmap ⟨(vp.node.2, vp.index.2), vp.is_valid.2⟩ = ⟨(up.node.2, up.index.2), up.is_valid.2⟩ := by
  intro vp up
  constructor
  · intro h
    obtain ⟨hl, hr⟩ := h
    constructor
    all_goals rfl
  · intro h
    obtain ⟨hl, hr⟩ := h
    rw [boxProd.pmap_def]
    congr
    simp [hl]
    simp [hr]
    simp [hl]
    simp [hr]

instance [SimplePN N₁] [SimplePN N₂] : SimplePN (N₁ □ N₂) where
  loopless := by
    intro vp hcontra
    obtain ⟨⟨⟨v₁, v₂⟩, ⟨p₁, p₂⟩⟩, ⟨h₁, h₂⟩⟩ := vp
    reduce at hcontra
    apply SimplePN.loopless (N := N₁) ⟨(v₁, p₁), h₁⟩
    simp_all
  simple := by
    intro vp₁ vp₂ heq hpeq
    rw [PNNetwork.boxProd.pmap_def, PNNetwork.boxProd.pmap_def] at hpeq
    apply Prod.ext_iff.mp at hpeq
    have h₁ := SimplePN.simple (N := N₁) ⟨(vp₁.node.1, vp₁.index.1), vp₁.is_valid.1⟩ ⟨(vp₂.node.1, vp₂.index.1), vp₂.is_valid.1⟩ (by simp [heq]) (by simp_all)
    have h₂ := SimplePN.simple (N := N₂) ⟨(vp₁.node.2, vp₁.index.2), vp₁.is_valid.2⟩ ⟨(vp₂.node.2, vp₂.index.2), vp₂.is_valid.2⟩ (by simp [heq]) (by simp_all)
    apply Prod.ext_iff.mp ∘ Subtype.ext_iff.mp at h₁
    apply Prod.ext_iff.mp ∘ Subtype.ext_iff.mp at h₂

    apply Subtype.ext
    apply Prod.ext
    · simp_all
    · apply Prod.ext
      all_goals simp_all


end BoxProd



-- Algorithm ≃ I → O
@[ext, grind]
structure PNAlgorithm (I O : Type*) where
  Msg : Type*
  State : Type*
  stopStates : Set State
  init : Type v → I → State
  send : (P : Type v) → State → P → Msg
  recv : (P : Type v) → State → (P → Msg) → State
  stopping_condition : ∀ P : Type v, ∀ y : P → Msg, ∀ s : State, s ∈ stopStates → recv P s y = s
  output : (state : State) → state ∈ stopStates → O -- TODO: State → O

section Examples

@[simps]
def PNalgorithm.id {A : Type*} : PNAlgorithm A A where
  Msg := Unit
  State := A
  stopStates := Set.univ
  init := fun d v ↦ v
  send := fun _ _ _ ↦ ()
  recv := fun _ v _ ↦ v
  stopping_condition := by simp
  output := fun v _ ↦ v

@[simps, grind]
def PNalgorithm.local_map (f : S → S'): PNAlgorithm S S' where
  Msg := Unit
  State := S'
  stopStates := Set.univ
  init := fun d v ↦ f v
  send := fun _ _ _ ↦ ()
  recv := fun _ v _ ↦ v
  stopping_condition := by simp
  output := fun v _ ↦ v

end Examples
