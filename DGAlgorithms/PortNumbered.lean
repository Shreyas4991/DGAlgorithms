import DGAlgorithms.ForMathlib.SimpleGraph
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Fintype.Perm

set_option autoImplicit false

/-- Given a bijective function, computably produce an equivalence. -/
@[simps]
def bijToEquiv {α β : Type*} [Fintype α] [DecidableEq β] (f : α → β) (h : Function.Bijective f) :
    α ≃ β where
  toFun := f
  invFun := fun b => Finset.univ.choose _ <| by simpa using h.existsUnique b
  left_inv := by
    intro a
    exact h.injective (Finset.choose_property (fun b => f b = f a) _ _)
  right_inv := fun b => Finset.choose_property (fun a => f a = b) Finset.univ _

variable {V : Type*}

/-- Port numbered networks -/
structure NonSimplePortNumbered (V : Type*) where
/-- The degree of a node, here corresponds to the number of outgoing ports. -/
(degree : V → ℕ)
/-- The endpoint of a given port. -/
(ofPort : (v : V) → Fin (degree v) → V)
/-- The return port from a given port. -/
(reversePort : (v : V) → (j : Fin (degree v)) → Fin (degree (ofPort v j)))
(ofPort_reversePort : ∀ (v : V) (j : Fin (degree v)), ofPort _ (reversePort v j) = v)
(coe_reversePort_reversePort (v : V) (j) : (reversePort _ (reversePort v j) : ℕ) = j)

namespace NonSimplePortNumbered

attribute [simp] ofPort_reversePort

variable {N : NonSimplePortNumbered V}

@[simp] lemma reversePort_reversePort {v : V} {j : Fin (N.degree v)} :
    N.reversePort _ (N.reversePort v j) = Fin.cast (by simp) j := by
  ext
  simp [coe_reversePort_reversePort]

lemma ofPort_cast (v w : V) (h : v = w) (i : Fin (N.degree v)) :
    N.ofPort w (Fin.cast (by rw [h]) i) = N.ofPort v i := by
  cases h
  rfl

lemma reversePort_cast (v w : V) (h : v = w) (i : Fin (N.degree v)) :
    N.reversePort w (Fin.cast (by rw [h]) i) =
      Fin.cast (by rw [ofPort_cast _ _ h]) (N.reversePort v i) := by
  cases h
  rfl

lemma coe_reversePort_cast (v w : V) (h : v = w) (i : Fin (N.degree v)) :
    (N.reversePort w (Fin.cast (by rw [h]) i) : ℕ) =
      (N.reversePort v i : ℕ) := by
  cases h
  rfl

lemma ofPort_of_reversePort {u v : V} {i : Fin (N.degree u)} {j : Fin (N.degree v)}
    (h : N.ofPort u i = v) (h' : (N.reversePort u i : ℕ) = j) :
    N.ofPort v j = u := by
  cases h
  rw [←Fin.ext_iff] at h'
  cases h'
  rw [N.ofPort_reversePort]

lemma reversePort_inj (v w : V) (i j : Fin _) (h : N.ofPort v i = N.ofPort w j) :
    (N.reversePort v i : ℕ) = (N.reversePort w j : ℕ) → v = w := by
  intro h'
  rw [←ofPort_of_reversePort h h', ofPort_reversePort]

lemma ext (N N' : NonSimplePortNumbered V)
    (degree : ∀ v, N.degree v = N'.degree v)
    (ofPort : ∀ (v : V) (i : Fin (N.degree v)), N.ofPort v i = N'.ofPort v (Fin.cast (degree v) i))
    (reversePort : ∀ (v : V) (j : Fin (N.degree v)),
      (N.reversePort v j : ℕ) = N'.reversePort v (Fin.cast (degree v) j)) :
    N = N' := by
  rcases N with ⟨d₁, o₁, r₁, _, _⟩
  rcases N' with ⟨d₂, o₂, r₂, _, _⟩
  dsimp at degree ofPort reversePort -- BUG: dsimp at * doesn't work here
  have : d₁ = d₂ := funext degree
  cases this
  simp only [Fin.cast_eq_self] at ofPort reversePort
  have : o₁ = o₂ := funext fun v => funext fun i => ofPort v i
  cases this
  have : r₁ = r₂ := by ext; exact reversePort _ _
  cases this
  rfl

/-- The network in which every node has a single port connected to itself. -/
@[simps]
def loopSelf (V : Type*) : NonSimplePortNumbered V where
  degree _ := 1
  ofPort v _ := v
  reversePort v _ := 0
  ofPort_reversePort := by simp
  coe_reversePort_reversePort := by simp

/-- The network in which every node has two ports connected to each other. -/
@[simps]
def loopOther (V : Type*) : NonSimplePortNumbered V where
  degree _ := 2
  ofPort v _ := v
  reversePort v := Equiv.swap 0 1
  ofPort_reversePort := by simp
  coe_reversePort_reversePort := by simp

@[simps]
def discrete (V : Type*) : NonSimplePortNumbered V where
  degree := 0
  ofPort _ := Fin.elim0
  reversePort _ i := Fin.elim0 i
  ofPort_reversePort _ i := Fin.elim0 i
  coe_reversePort_reversePort _ i := Fin.elim0 i

/-- The adjacency relation on a not-necessarily-simple port numbered network. -/
def adj (N : NonSimplePortNumbered V) (v : V) : V → Prop := (∃ i, N.ofPort v i = ·)

lemma ofPort_adj (v : V) (i : Fin (N.degree v)) : N.adj v (N.ofPort v i) := ⟨i, rfl⟩

/-- A network is loopless if there is no node with a port which goes to itself. -/
def loopless (N : NonSimplePortNumbered V) : Prop := ∀ v i, N.ofPort v i ≠ v

instance [Fintype V] [DecidableEq V] : Decidable N.loopless :=
  inferInstanceAs (Decidable (∀ _, _))

lemma loopless_iff (N : NonSimplePortNumbered V) : N.loopless ↔ Irreflexive N.adj := by
  simp only [loopless, Irreflexive, adj]
  aesop

lemma symm : Symmetric N.adj | v, _, ⟨i, rfl⟩ => ⟨N.reversePort v i, N.ofPort_reversePort _ _⟩

/-- A network has no multi edges if, fixing a node `v`, no two ports go to the same node `w`. -/
def noMultiEdges (N : NonSimplePortNumbered V) : Prop := ∀ v, Function.Injective (N.ofPort v)

instance [Fintype V] [DecidableEq V] : Decidable N.noMultiEdges :=
  inferInstanceAs (Decidable (∀ _, _))

/--
In the case that N does not have multiedges, extensionality is easier to prove.
Note that the extra assumption is necessary, since we have `N` as
`p(1, 1) = (2, 2); p(1, 2) = (2, 1)` being equal to `p(1, 1) = (2, 1); p(1, 2) = (2, 2)`.
-/
lemma ext_noMultiEdges (N N' : NonSimplePortNumbered V) (degree : ∀ v, N.degree v = N'.degree v)
    (ofPort : ∀ v i, N.ofPort v i = N'.ofPort v (Fin.cast (degree v) i))
    (hN : N.noMultiEdges) :
    N = N' := by
  rcases N with ⟨d₁, o₁, r₁, h₁, h'₁⟩
  rcases N' with ⟨d₂, o₂, r₂, h₂, h'₂⟩
  dsimp [NonSimplePortNumbered.noMultiEdges] at degree ofPort hN ⊢
  have : d₁ = d₂ := funext degree
  cases this
  simp only [Fin.cast_eq_self] at ofPort
  have : o₁ = o₂ := funext fun v => funext fun i => ofPort v i
  cases this
  congr 1
  ext v j
  rw [←Fin.ext_iff]
  refine hN (o₁ v j) ?_
  rw [h₁, h₂]

/-- If there are no multi edges from v, we have a bijection between ports on v and nodes adjacent to
it. -/
def FinEquivAdjSet (v : V) [DecidableEq V] (h : Function.Injective (N.ofPort v)) :
    Fin (N.degree v) ≃ {w | N.adj v w} :=
  bijToEquiv (fun i => ⟨N.ofPort v i, ofPort_adj _ _⟩) <|
    ⟨ fun _ _ h' => h (Subtype.ext_iff.1 h'),
      fun ⟨_, j, hj⟩ => ⟨j, Subtype.ext_iff.2 hj⟩⟩

/-- The type of ports in the network N. -/
def ports (N : NonSimplePortNumbered V) := (v : V) × Fin (N.degree v)
/-- The involution on ports defined in the textbook. -/
def p (z : N.ports) : N.ports := ⟨N.ofPort z.1 z.2, N.reversePort z.1 z.2⟩

@[ext]
lemma ports_eq {u v : N.ports}
    (nodes_eq : u.1 = v.1) (cast_ports_eq : (u.2 : ℕ) = v.2) : u = v := by
  cases' u with u i
  cases' v with v j
  cases nodes_eq
  simp only [Fin.val_eq_val] at cast_ports_eq
  aesop

lemma ports_eq' {u v : N.ports}
    (nodes_eq : u.1 = v.1) (cast_ports_eq : u.1 = v.1 → (u.2 : ℕ) = v.2) : u = v :=
  ports_eq nodes_eq (cast_ports_eq nodes_eq)

lemma p_invol : Function.Involutive N.p := by
  rintro ⟨u, i⟩
  simp only [p]
  apply ports_eq
  case nodes_eq => exact N.ofPort_reversePort _ _
  case cast_ports_eq => exact N.coe_reversePort_reversePort _ _

/-- Produce a network from an involution on ports. -/
def mk' (V : Type*) (degree : V → ℕ)
    (p : (v : V) × Fin (degree v) → (v : V) × Fin (degree v)) (hp : p.Involutive) :
    NonSimplePortNumbered V where
  degree := degree
  ofPort v i := (p ⟨v, i⟩).1
  reversePort v i := (p ⟨v, i⟩).2
  ofPort_reversePort := by
    intro v i
    simp only [Sigma.eta, hp ⟨v, i⟩]
  coe_reversePort_reversePort := by
    intro v i
    dsimp only
    rw [Sigma.eta, hp ⟨v, i⟩]

end NonSimplePortNumbered

/-- A simple port numbered network. -/
structure PortNumbered (V : Type*) extends NonSimplePortNumbered V, SimpleGraph V where
(adj_eq : toNonSimplePortNumbered.adj = Adj)
(no_multi_edges : toNonSimplePortNumbered.noMultiEdges)

attribute [simp] PortNumbered.adj_eq

namespace PortNumbered

/--
Produce a port numbered network from a not-necessarily-simple one provided it has no loops and no
multi-edges.
Note there is another way of constructing this by removing loops, but this would require changing
the degree function as multi-edges would need to be destroyed.
-/
@[simps Adj toNonSimplePortNumbered]
def fromNonSimple {V : Type*} (N : NonSimplePortNumbered V)
    (loopless : N.loopless) (no_multi_edges : N.noMultiEdges) :
    PortNumbered V :=
  { Adj := N.adj
    symm := N.symm
    adj_eq := rfl
    loopless := N.loopless_iff.1 loopless
    no_multi_edges := no_multi_edges
    .. }

lemma fromNonSimple_inj {V : Type*} {N₁ N₂ : PortNumbered V}
    (h : N₁.toNonSimplePortNumbered = N₂.toNonSimplePortNumbered) :
    N₁ = N₂ := by
  rcases N₁ with ⟨n₁, g₁, h₁, h'₁⟩
  rcases N₂ with ⟨n₂, g₂, h₂, h'₂⟩
  cases h
  congr 1
  ext : 1
  rw [←h₁, h₂]

/--
Produce a port numbered network from a locally finite simple graph given an explicit bijection
between the degree of each node and its neighbour set.
The `degree` field can be specified since it is often useful to have a good defeq for it.
-/
@[simps toSimpleGraph degree ofPort]
def fromSimpleGraph {V : Type*} (G : SimpleGraph V) (degree : V → ℕ)
    (numbering : ∀ v, Fin (degree v) ≃ G.neighborSet v) :
    PortNumbered V where
  toSimpleGraph := G
  degree v := degree v
  ofPort v i := (numbering v i).1
  reversePort v i := (numbering (numbering v i).1).symm ⟨v, (numbering v i).2.symm⟩
  adj_eq := funext fun v => funext fun w => propext <|
      (Equiv.exists_congr_left (numbering v)).trans <| by simp
  ofPort_reversePort := by simp
  coe_reversePort_reversePort := by
    intro v i
    dsimp
    rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  no_multi_edges := by
    intro v i j h
    dsimp at i j h
    rwa [←Subtype.ext_iff, Equiv.apply_eq_iff_eq] at h

@[simps! toSimpleGraph degree]
def fromSimpleGraph' {V : Type*} [DecidableEq V] (G : SimpleGraph V) (degree : V → ℕ)
    [G.LocallyFinite] (numbering : ∀ v, Fin (degree v) → G.neighborSet v)
    (hnumbering : ∀ v, (numbering v).Injective) (hdegree : ∀ v, degree v = G.degree v) :
    PortNumbered V :=
  fromSimpleGraph G degree fun v => bijToEquiv (numbering v) <|
    (Fintype.bijective_iff_injective_and_card _).2 ⟨hnumbering v, by simp [hdegree]⟩

lemma fromSimpleGraph_inj {V : Type*} (G : SimpleGraph V) (degree : V → ℕ) :
    Function.Injective (fromSimpleGraph G degree) := by
  intro n₁ n₂ h
  ext v i : 3
  let _ : Fintype (G.neighborSet v) := Fintype.ofEquiv _ (n₁ v)
  have : (fromSimpleGraph G degree n₁).ofPort v i = (fromSimpleGraph G degree n₂).ofPort v i := by
    congr 1
    rw [h]
  simpa [fromSimpleGraph_ofPort] using this

/--
Any simple graph has a port numbering given by choosing the numbers arbitrarily.
-/
noncomputable def chooseNetwork {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] :
    PortNumbered V :=
  fromSimpleGraph G (G.degree ·) fun v => (Fintype.equivFinOfCardEq (by simp)).symm

@[simps toSimpleGraph]
def discrete : PortNumbered V where
  toSimpleGraph := ⊥
  toNonSimplePortNumbered := .discrete _
  adj_eq := by ext x; simp [NonSimplePortNumbered.adj]
  no_multi_edges v i := by simp

variable {N : PortNumbered V} [DecidableEq V]

instance : Coe (PortNumbered V) (SimpleGraph V) := ⟨fun N => N.toSimpleGraph⟩
instance : Coe (PortNumbered V) (NonSimplePortNumbered V) := ⟨fun N => N.toNonSimplePortNumbered⟩

@[simp] nonrec lemma ofPort_adj {v : V} (i : Fin (N.degree v)) : N.Adj v (N.ofPort v i) :=
  N.adj_eq ▸ N.ofPort_adj _ _

/-- We have a bijection between the degree of each node and its neighbours. -/
def numbering (N : PortNumbered V) (v : V) : Fin (N.degree v) ≃ N.neighborSet v :=
  (N.FinEquivAdjSet v (N.no_multi_edges v)).trans (Equiv.subtypeEquiv (Equiv.refl _) (by simp))

@[simp] lemma numbering_apply {N : PortNumbered V} (v : V) (i : Fin (N.degree v)) :
    N.numbering v i = N.ofPort v i := rfl

/-- Given an adjacent node, return the port to reach it. -/
def toPort (v w : V) (h : N.Adj v w) : Fin (N.degree v) := (N.numbering v).symm ⟨w, by simp [h]⟩

@[simp] lemma ofPort_toPort {v w : V} (h : N.Adj v w) : N.ofPort v (N.toPort v w h) = w := by
  rw [←numbering_apply, toPort, Equiv.apply_symm_apply]

@[simp] lemma toPort_ofPort {v : V} (i : Fin (N.degree v)) :
    N.toPort v (N.ofPort v i) (N.ofPort_adj i) = i := by
  simp [←numbering_apply, toPort]

lemma ofPort_injective (v : V) : Function.Injective (N.ofPort v) := N.no_multi_edges v

/--
A claim is true on all ports iff it is true on all adjacent nodes. Useful for rewriting in the
forward direction.
The backward direction is given in `forall_adj`.
-/
lemma forall_ports {v : V} {p : Fin (N.degree v) → Prop} :
    (∀ i, p i) ↔ ∀ (w : V) (h : N.Adj v w), p (N.toPort v w h) := by
  simp [Equiv.forall_congr_left' (N.numbering v), toPort]

/--
A claim is true on all adjacent nodes iff it is true on all ports. Useful for rewriting in the
forward direction.
The backward direction is given in `forall_ports`.
-/
lemma forall_adj {v : V} {p : (w : V) → (h : N.Adj v w) → Prop} :
    (∀ w (h : N.Adj v w), p w h) ↔ ∀ i, p (N.ofPort v i) (N.ofPort_adj _) := by
  simp [forall_ports]

/--
A claim is true on some port iff it is true on some adjacent node. Useful for rewriting in the
forward direction.
The backward direction is given in `exists_adj`.
-/
lemma exists_ports {v : V} {p : Fin (N.degree v) → Prop} :
    (∃ i : Fin (N.degree v), p i) ↔ ∃ (w : V) (h : N.Adj v w), p (N.toPort v w h) := by
  simp [Equiv.exists_congr_left (N.numbering v), toPort]

/--
A claim is true on some adjacent node iff it is true on some port. Useful for rewriting in the
forward direction.
The backward direction is given in `exists_ports`.
-/
lemma exists_adj {v : V} {p : (w : V) → (h : N.Adj v w) → Prop} :
    (∃ (w : V) (h : N.Adj v w), p w h) ↔ ∃ i, p (N.ofPort v i) (N.ofPort_adj _) := by
  simp [exists_ports]

lemma reversePort_toPort (v w : V) (h : N.Adj v w) :
    N.reversePort v (N.toPort v w h) = Fin.cast (by rw [N.ofPort_toPort]) (N.toPort w v h.symm) :=
  N.ofPort_injective _ <| by
    simp only [N.ofPort_reversePort]
    rw [N.ofPort_cast]
    · simp
    · simp

lemma reversePort_of_ofPort {u v : V} {i : Fin (N.degree u)} {j : Fin (N.degree v)}
    (h : N.ofPort u i = v) (h' : N.ofPort v j = u) :
    (N.reversePort u i : ℕ) = j := by
  cases h
  rw [←Fin.ext_iff]
  refine N.ofPort_injective _ ?_
  rw [N.ofPort_reversePort, h']

lemma ofPort_of_reversePort {u v : V} {i : Fin (N.degree u)} {j : Fin (N.degree v)}
    (h : N.ofPort u i = v) (h' : (N.reversePort u i : ℕ) = j) :
    N.ofPort v j = u := by
  cases h
  rw [←Fin.ext_iff] at h'
  cases h'
  rw [N.ofPort_reversePort]

lemma reversePort_eq_iff {u v : V} {i : Fin (N.degree u)} {j : Fin (N.degree v)}
    (h : N.ofPort u i = v) :
    (N.reversePort u i : ℕ) = j ↔ N.ofPort v j = u :=
  ⟨ofPort_of_reversePort h, reversePort_of_ofPort h⟩

@[ext]
lemma ext (N N' : PortNumbered V) (degree : ∀ v, N.degree v = N'.degree v)
    (ofPort : ∀ v i, N.ofPort v i = N'.ofPort v (Fin.cast (degree v) i)) :
    N = N' :=
  fromNonSimple_inj (N.ext_noMultiEdges _ degree ofPort N.no_multi_edges)

instance [DecidableEq V] : N.LocallyFinite := fun _ => Fintype.ofEquiv _ (numbering _ _)
instance [DecidableEq V] : DecidableRel N.Adj := fun v w =>
  decidable_of_decidable_of_eq (p := Exists _) (congrArg (· v w) N.adj_eq)

/-- We ensure that the degree that's a field of NonSimplePortNumbered is the simp normal form. -/
@[simp] lemma degree_eq {V : Type*} {N : PortNumbered V} (v : V) [Fintype (N.neighborSet v)] :
    (N : SimpleGraph V).degree v = N.degree v := by
  classical
  rw [←SimpleGraph.card_neighborSet_eq_degree, Fintype.card_congr (N.numbering v).symm]
  simp only [Fintype.card_fin]

lemma degree_iso {V V' : Type*} (G : SimpleGraph V) (G' : SimpleGraph V') (e : G ≃g G') (v : V)
    [Fintype (G.neighborSet v)] [Fintype (G'.neighborSet (e v))] :
    G.degree v = G'.degree (e v) := by
  rw [←SimpleGraph.card_neighborSet_eq_degree, ←SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_congr (e.mapNeighborSet v)

-- NOTE: when the fix to maxDegree hits mathlib, the assumptions here should change.
nonrec lemma degree_le_maxDegree {V : Type*} [Fintype V] {N : PortNumbered V}
    [DecidableRel N.Adj] (v : V) :
    N.degree v ≤ N.maxDegree := by
  rw [←N.degree_eq]
  convert N.degree_le_maxDegree v

/--
If N is a port numbered network whose underlying graph is isomorphic to G', we can construct a
port numbered network on G'.
-/
@[simps! toSimpleGraph degree ofPort reversePort]
def transfer {V V' : Type*} {N : PortNumbered V} {G' : SimpleGraph V'}
    (e : G' ≃g (N : SimpleGraph V)) :
    PortNumbered V' where
  degree v' := N.degree (e v')
  ofPort v' i := e.symm (N.ofPort (e v') i)
  reversePort v' i := Fin.cast (by simp) (N.reversePort (e v') i)
  ofPort_reversePort v' i := by simp [N.ofPort_cast]
  coe_reversePort_reversePort := by simp [N.reversePort_cast]
  toSimpleGraph := G'
  adj_eq := by
    ext x y
    simp only [NonSimplePortNumbered.adj, ←e.map_adj_iff, ←N.adj_eq]
    refine exists_congr ?_
    intro i
    exact e.symm_apply_eq
  no_multi_edges := fun v i j h => N.no_multi_edges (e v) (e.symm.injective h)

def inducing {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset (PortNumbered V) :=
  (Finset.univ (α := (v : V) → Fin (G.degree v) ≃ ↑(G.neighborSet v))).map
    ⟨ fun n => fromSimpleGraph G _ n, fromSimpleGraph_inj _ _ ⟩

lemma self_induce {V : Type*} [Fintype V] [DecidableEq V] (N : PortNumbered V) :
    fromSimpleGraph N.toSimpleGraph (fun v ↦ (N : SimpleGraph V).degree v)
      (fun v => (finCongr (by simp)).trans (N.numbering v)) = N := by ext <;> simp

lemma mem_inducing {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {N : PortNumbered V} :
    N ∈ inducing G ↔ N.toSimpleGraph = G := by
  constructor
  case mp =>
    simp only [inducing, Finset.mem_map, Finset.mem_univ,
      Function.Embedding.coeFn_mk, true_and, forall_exists_index]
    rintro n rfl
    rfl
  case mpr =>
    rintro rfl
    simp only [inducing, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
    refine ⟨fun v => Equiv.trans (finCongr (by simp)) (N.numbering v), ?_⟩
    convert self_induce N using 6

end PortNumbered

/--
A problem is a set of possible values for vector of local values. This most commonly encodes the
input to a distributed algorithm, or the output from a distributed algorithm.
-/
structure Problem (localValue : Type*) :=
/-- The set of valid local outputs for a given network. -/
(valid (V : Type*) : PortNumbered V → Set (V → localValue))

namespace Problem

/-- The trivial input as a problem. -/
@[simp] def trivialInp : Problem PUnit := ⟨fun _ _ => Set.univ⟩

/--
The colouring problem: each node is assigned a value from `α` such that adjacent nodes have
different values.
-/
def Colouring (α : Type*) : Problem α where
  valid V N := {f | ∀ x y : V, N.Adj x y → f x ≠ f y}

lemma colouring_subtype_iff {α V : Type*} {N : PortNumbered V} (p : α → Prop)
    (f : V → {a // p a}) :
    f ∈ (Colouring {a // p a}).valid V N ↔ ((↑) ∘ f) ∈ (Colouring α).valid V N := by
  simp only [Colouring, Set.mem_setOf_eq, Function.comp_apply, ne_eq, Subtype.ext_iff]

/--
The problem of returning a subset of the edges. Essentially this ensures that the encoding returned
by the algorithm does indeed encode a subset of the edges.

Most useful as a building block problem.
 -/
def EdgeSubset : Problem (Set ℕ) where
  valid V N :=
    {f | ∀ v : V,
      -- each edge label is a valid port number
      (∀ i, i ∈ f v → i < N.degree v) ∧
      -- edges are symmetric
      (∀ i : Fin (N.degree v),
        (i : ℕ) ∈ f v ↔ (N.reversePort v i : ℕ) ∈ f (N.ofPort v i))}

/--
Option ℕ encodes a matching on a PN network: none means no edge, some n means edge to the nth port.
-/
def Matching : Problem (Option ℕ) where
  valid V N := {f | (fun v => (f v).getM) ∈ EdgeSubset.1 V N}

/-- The problem of finding a maximal matching in a graph. -/
def MaximalMatching : Problem (Option ℕ) where
  valid V N := Matching.valid V N ∩
    {f | ∀ v : V, f v = none → -- for every unmatched node
      ∀ i : Fin (N.degree v), -- and every outward port
        f (N.ofPort v i) ≠ none} -- the corresponding node is matched

/-- The problem of finding a maximal matching in a graph (in terms of adjacency). -/
def MaximalMatching' : Problem (Option ℕ) where
  valid V N := Matching.valid V N ∩
    {f | ∀ v : V, f v = none → -- for every unmatched node
      ∀ w : V, N.Adj v w → -- and every adjacent port
        f w ≠ none} -- the corresponding node is matched

end Problem
