import Mathlib


/-!
# Port-Numbered Networks

In this file, we define PN Networks and what it means for a network to be
simple. We then provide the natural coersion from the simple network into a
[Mathlib.SimpleGraph]. Finally, we prove some simplification lemmas.
-/

namespace DGAlgorithms

/-- A shorthand for the type of a port. -/

structure Port (V : Type u) (α : V → Type v) where
  node : V
  port : α node


/-- A Port-Numbered Network.

Each node `v` of the network has some `deg v` ports attached to it. Each port
is attached to another port, given by `pmap`. Function `pmap` is involutive,
that is if `p₁` is connected to `p₂`, then `p₂` is also connected to `p₁`.

Note that here we define ports to be pairs of a node and an arbitrary natural
number. In particular, this differes from the more typical definition where a
port is a dependent pair `(v : V) × Fin (deg v)`. We extract this to
`PNNetwork.IsWellDefined`.
 -/
structure PNNetwork (V : Type u) (α : V → Type v) where

  /-- Map from a given port of a node to the other end of the edge. -/
  pmap : Port V α → Port V α
  /-- Ensure that ports are properly connected. -/
  pmap_involutive : ∀ v : V, ∀ i : α v, pmap (pmap ⟨v, i⟩) = ⟨v, i⟩


variable {V : Type*} {α : V → Type*}

def PNNetwork.eq  (N₁ N₂ : PNNetwork V α) : Prop :=
  ∀ v : V, ∀ i : α v , N₁.pmap ⟨v, i⟩ = N₂.pmap ⟨v, i⟩

def PNNetwork.eq.equivalence : Equivalence (@PNNetwork.eq  V α) where
  refl := by simp [eq]
  symm := by simp_all [eq]
  trans := by simp_all [eq]

instance PNNetwork.setoid : Setoid (PNNetwork V α) where
  r:= PNNetwork.eq
  iseqv := PNNetwork.eq.equivalence

-- def PNNetwork' (V : Type*) := Quotient (PNNetwork.setoid (V := V))

@[simp]
lemma PNNetwork.pmap_involutive' (N : PNNetwork V α)
  (vp : Port V α) : N.pmap (N.pmap vp) = vp := by
  apply N.pmap_involutive


/-- A Simple Port-Numbered Network.

A PN network is simple if it is both loopless and simple, i.e. there are no
duplicate edges.
-/
class SimplePN (N : PNNetwork V α) : Prop where
  /-- There are no edges from a node to itself. -/
  loopless : ∀ v : V, ∀ i j : α v, N.pmap ⟨v, i⟩ ≠ ⟨v, j⟩
  /-- There is at most one edge between any pair of nodes. -/
  simple : ∀ v : V, ∀ i j : α v, (N.pmap ⟨v, i⟩).node = (N.pmap ⟨v, j⟩).node → i = j

variable (N : PNNetwork V α)

lemma SimplePN.simple_injective [s : SimplePN N] (v : V) :
    Function.Injective fun (i : α v) ↦ (N.pmap ⟨v, i⟩).node := by
  apply s.simple v

/-- Adjacency relation for a network.

See [Mathlib.SimpleGraph.Adj] for comparison.
-/
def PNNetwork.Adj (u v : V) : Prop :=
  ∃ i : α u, ∃ j : α v, N.pmap ⟨u, i⟩ = ⟨v, j⟩

/-- Another way to define adjacency using only one exists. -/
def PNNetwork.Adj' (u v : V) : Prop :=
  ∃ i : α u, (N.pmap ⟨u, i⟩).node = v

/-- Both definitions of adjacency are equal. -/
lemma PNNetwork.Adj_eq_Adj': Adj N = Adj' N := by
  ext u v
  constructor
  case mp =>
    intro h
    obtain ⟨i, j, h⟩ := h
    use i
    simp_all
  case mpr =>
    intro h
    unfold Adj
    unfold Adj' at h
    obtain ⟨i, h⟩ := h
    subst h
    use i
    use (N.pmap ⟨u, i⟩).port


/-- The induced adjacency relation is symmetric. -/
lemma PNNetwork.Adj.symm : Symmetric (Adj N) := by
  intro u v h
  obtain ⟨i, j, h⟩ := h
  use j, i
  rw [←h, N.pmap_involutive]

variable [s : SimplePN N]

/-- The induced adjacency relation is irreflexive.

This essentially says that induced graph is loopless.
-/
lemma PNNetwork.Adj.irrefl : Irreflexive (Adj N) := by
  intro u h
  obtain ⟨i, j, h⟩ := h
  exact s.loopless u i j h

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

/-- Well-defined networks always induce a locally finite graph. -/
noncomputable instance PNNetwork.to_SimpleGraph_LocallyFinite
  {N : PNNetwork V α}
  [finportmap : ∀ v : V, Fintype (α v)] [SimplePN N]
  : N.to_SimpleGraph.LocallyFinite := by
  intro v
  unfold SimpleGraph.neighborSet to_SimpleGraph
  simp_rw [Adj_eq_Adj']
  apply Set.Finite.fintype
  exact Finite.Set.finite_replacement fun x ↦ (N.pmap { node := v, port := x }).node

-- noncomputable instance PNNetwork.to_SimpleGraph.neighbourSet.Fintype
--   {N : PNNetwork V α} [DecidableEq (Port V α)]
--   [finportmap : ∀ v : V, Fintype (α v)] [SimplePN N] : ∀ v : V, Fintype ↑(N.to_SimpleGraph.neighborSet v) := by
--     intro v
--     specialize finportmap v
--     simp [to_SimpleGraph, SimpleGraph.neighborSet, Adj]
--     constructor
--     case elems =>
--       exact Finset.image N.pmap
--     case complete =>
--       intro x

--       sorry





/-- Degree in the induced [Mathlib.SimpleGraph] is the same as in the original
network.
-/
@[simp] lemma PNNetwork.to_SimpleGraph_degree_eq_deg
  (v : V) [Fintype (α v)]
  (N : PNNetwork V α) [iS : SimplePN N]
  [SimpleGraph.LocallyFinite (N.to_SimpleGraph)]
  : N.to_SimpleGraph.degree v = Fintype.card (α v) := by
  -- Unfold the definition of degree
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset, Set.toFinset_card]

  -- We provide a bijection from `α v` to neighbors of `v`
  let f : (α v) → {w : V // N.Adj v w } := fun i ↦ ⟨(N.pmap ⟨v, i⟩).node, by
    use i
    use (N.pmap ⟨v, i⟩).port
  ⟩

  have f_bij : Function.Bijective f := by
    constructor
    · intro i j hij
      simp_all [f]
      apply iS.simple
      assumption
    · intro u
      have := u.property.choose
      obtain ⟨c, _⟩ := u.property.choose_spec
      use u.property.choose
      simp_all [f]

  -- Now the result is immediate
  symm
  apply Finset.card_bijective f f_bij
  simp_all

-- Pairing functions for PNNetwork,boxProd
def unpair (w h : ℕ) (n : ℕ) : ℕ × ℕ :=
  if n < w*h then
    (n % w, n / w)
  else
    -- Poison value for invalid ports
    (w, h)

def pair (w h : ℕ) (p : ℕ × ℕ) : ℕ :=
  if p.1 < w ∧ p.2 < h then
    p.2 * w + p.1
  else
    -- Poison value for invalid prots
    w * h

/-- If both given ports are valid, then pair produces a valid port. -/
lemma pair_valid {w h : ℕ} : ∀ n₁ < w, ∀ n₂ < h, pair w h (n₁, n₂) < w*h := by
  intro n₁ hn₁ n₂ hn₂
  unfold pair
  by_cases hc : n₁ < w ∧ n₂ < h
  simp [hc]
  suffices n₂ * w + w ≤ w * h by linarith
  rw [←Nat.succ_mul, mul_comm]
  exact Nat.mul_le_mul le_rfl hn₂
  simp_all

lemma pair_valid_iff {w h n₁ n₂ : ℕ} : n₁ < w ∧ n₂ < h ↔ pair w h (n₁, n₂) < w*h := by
  constructor
  · intro h'
    exact pair_valid _ h'.left _ h'.right
  · intro h'
    unfold pair at h'
    split_ifs at h' with h''
    repeat simp_all

lemma pair_invalid_iff {w h n₁ n₂ : ℕ} : n₁ ≥ w ∨ n₂ ≥ h ↔ pair w h (n₁, n₂) ≥ w*h := by
  rw [←not_iff_not]
  simp [pair_valid_iff]

/-- Pair and unpair cancel each other. -/
@[simp] lemma pair_unpair {w h : ℕ} : ∀ n < w*h, pair w h (unpair w h n) = n := by
  intro n hn
  unfold unpair pair
  have : n % w < w := by
    by_cases hw : w = 0
    · simp_all
    · exact Nat.mod_lt n (Nat.zero_lt_of_ne_zero hw)
  have : n / w < h := by exact Nat.div_lt_of_lt_mul hn
  simp_all [Nat.div_add_mod']

/-- Unpair and pair cancel each other. -/
@[simp] lemma unpair_pair {w h : ℕ} : ∀ n₁ < w, ∀ n₂ < h, unpair w h (pair w h (n₁, n₂)) = (n₁, n₂) := by
  intro n₁ hn₁ n₂ hn₂
  unfold unpair pair
  have : n₂ * w + n₁ < w * h := by
    suffices n₂ * w + w ≤ w * h by linarith
    rw [←Nat.succ_mul, mul_comm]
    exact Nat.mul_le_mul le_rfl hn₂
  simp_all
  constructor
  exact Nat.mod_eq_of_lt hn₁
  apply Nat.div_eq_of_lt_le
  linarith
  linarith

/-- Given a valid port, unpair produces two valid ports. -/
lemma unpair_valid {w h : ℕ} : ∀ n < w*h, (unpair w h n).1 < w ∧ (unpair w h n).2 < h := by
  intro n hn
  unfold unpair
  by_cases hw : w = 0
  all_goals simp_all
  constructor
  · exact Nat.mod_lt n $ Nat.zero_lt_of_ne_zero hw
  · exact Nat.div_lt_of_lt_mul hn

lemma unpair_valid_iff {w h n : ℕ} : n < w*h ↔ (unpair w h n).1 < w ∧ (unpair w h n).2 < h := by
  constructor
  · exact unpair_valid n
  · intro h'
    by_contra hc
    have : unpair w h n = (w, h) := by simp [unpair, hc]
    simp_all

lemma unpair_invalid_iff (w h n : ℕ) : n ≥ w*h ↔ unpair w h n = (w, h) := by
  constructor
  · intro h
    unfold unpair
    simp_all
  · have := unpair_valid_iff (w := w) (h := h) (n := n)
    intro h
    simp_all [lt_self_iff_false, and_self, iff_false, not_lt, ge_iff_le]

abbrev prod_fun (f : a → β) (g : γ → δ) : a × γ → β × δ:= fun (x,y) => (f x, g y)


def PNNetwork.boxProd (G : PNNetwork V α) (G' : PNNetwork V' α') : PNNetwork (V × V') (fun (v : V × V') ↦ α v.fst × α' v.snd) where
  pmap := fun vv ↦
    let res₁ := G.pmap ⟨vv.node.1, vv.port.1⟩
    let res₂ := G'.pmap ⟨vv.node.2, vv.port.2⟩
    {
      node := (res₁.node, res₂.node)
      port := (res₁.port, res₂.port)
    }

  pmap_involutive := by
    intro (vv₁, vv₂) (p₁,p₂)
    -- Give names to all intermediate values
    simp at p₁ p₂
    simp_all
    rw [G.pmap_involutive, G'.pmap_involutive]
    constructor
    · simp
    · simp




infixl:70 " □ " => PNNetwork.boxProd

-- instance  (G : PNNetwork V) (G' : PNNetwork V') [SimplePN G] [SimplePN G'] : SimplePN (G □ G') := sorry

-- lemma box_prod_comm (G : PNNetwork V) (G' : PNNetwork V') [SimplePN G] [SimplePN G'] : (G □ G').to_SimpleGraph = (G.to_SimpleGraph □ G'.to_SimpleGraph) := by
--   ext v v'

--   sorry

inductive PNWalk {V : Type u} {α : V → Type v} (N : PNNetwork V α) : V → V → Type (max u v)
  | nil (v : V) : PNWalk N v v
  | cons (v : V) (i : α v) (tail : PNWalk N ((N.pmap ⟨v, i⟩).node) u) : PNWalk N v u

def PNWalk.length : PNWalk N u v → ℕ
  | nil _ => 0
  | cons _ _ tail => tail.length + 1

omit s in
@[simp]
lemma PNWalk.length_nil : (PNWalk.nil (N := N) v).length = 0 := by rfl

omit s in
@[simp]
lemma PNWalk.length_cons : (PNWalk.cons (N := N) v i tail).length = tail.length + 1 := by rfl

noncomputable def PNNetwork.edist (N : PNNetwork V α) (u v : V) : ℕ∞ :=
  ⨅ w : PNWalk N u v, w.length
