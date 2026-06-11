import Mathlib


namespace DGAlgorithms

section PNNetwork

structure Port {V : Type u} (P : V → Type v) where
  node : V
  port : P node

/-- A pre-PNNetwork.
 -/
structure PNNetwork {V : Type u} (P : V → Type v) where
  pmap : Port P → Port P
  pmap_involutive : Function.Involutive pmap

@[simp]
lemma PNNetwork.pmap_pmap {N : PNNetwork P} : ∀ vp : Port P, N.pmap (N.pmap vp) = vp := N.pmap_involutive

@[simp]
lemma PNNetwork.pmap_pmap_port {N : PNNetwork P} : ∀ vp : Port P, (N.pmap (N.pmap vp)).port = vp.port := sorry

-- def PNNetwork.ofDeg (deg : V → N) : PNNetwork (Fin ∘ deg) where
--   pmag := sorry
--   pmap_involution := sorry

variable {V : Type u} {P : V → Type u} (N : PNNetwork P)

#check Type 2 × Type 2

structure Foo (A B : Type*) where
  a : A
  b : B


def foo {U V : Type u} (G : U → Type v) (P : V → Type v) : U × V → Type v := fun (u, v) ↦ Prod (G u) (P v)

def PNNetwork.boxProd' {P₁ : V₁ → Type u} {P₂ : V₂ → Type u} (N₁ : PNNetwork P₁) (N₂ : PNNetwork P₂) : PNNetwork (fun (v₁, v₂) ↦ Prod (P₁ v₁) (P₂ v₂)) where
  pmap := fun vp ↦
    let ⟨⟨v₁, v₂⟩, p₁, p₂⟩ := vp
    let ⟨u₁, q₁⟩ := N₁.pmap ⟨v₁, p₁⟩
    let ⟨u₂, q₂⟩ := N₂.pmap ⟨v₂, p₂⟩
    ⟨(u₁, u₂), ⟨q₁, q₂⟩⟩
  pmap_involutive := by
    intro vp
    simp
    eta_struct
    congr
    simp
    simp
    simp
    simp

    -- conv =>
    --   enter [1, 2]

    --   rw [pmap_pmap]
    -- rw [N₁.pmap_pmap]
    -- simp_rw [pmap_pmap]
    sorry

include N
/-- Adjacency relation for a network.

See [`Mathlib.SimpleGraph.Adj`] for comparison.
-/
def PNNetwork.Adj (u v : V) : Prop :=
  ∃ vp : Port P, vp.node = u ∧ (N.pmap vp).node = v

/-- The induced adjacency relation is symmetric. -/
@[symm]
lemma PNNetwork.Adj.symm : Symmetric (Adj N) := by
  intro u v h
  obtain ⟨vp, h, h'⟩ := h
  use (N.pmap vp)
  simp_all

@[simp]
lemma PNNetwork.Adj_of_pmap : ∀ vp : Port P, N.Adj vp.node (N.pmap vp).node := by
  intro vp
  use vp

-- #check Pi.

def foo (U V : Type u) (G : U → Type u) (H : V → Type u) : (U × V) → Type u := fun (u, v) ↦ Prod.mk (G u) (H v)

def PNNetwork.boxProd' (N₁ : PNNetwork P₁) (N₂ : PNNetwork P₂) : PNNetwork (Pi.prod P₁ P₂)

section SimplePN

/-- A Simple Port-Numbered Network.

A PN network is simple if it is both loopless and simple, i.e. there are no
duplicate edges.
-/
class SimplePN {V : Type u} (N : PNNetwork V) : Prop where
  /-- There are no edges from a node to itself. -/
  loopless : ∀ vp : N.Port, (N.pmap vp).node ≠ vp.node
  /-- There is at most one edge between any pair of nodes. -/
  simple : ∀ vp₁ vp₂ : N.Port, vp₁.node = vp₂.node → (N.pmap vp₁).node = (N.pmap vp₂).node → vp₁ = vp₂

def SimplePN.simple' [s : SimplePN N] :
    ∀ v : V, ∀ i j : ℕ, i < N.deg v → j < N.deg v → (N.pmap' (v, i)).node = (N.pmap' (v, j)).node → i = j := by
  intro v i j hi hj h
  have := s.simple ⟨(v, i), hi⟩ ⟨(v, j), hj⟩ rfl h
  rw [←Subtype.val_inj] at this
  simp_all


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

/-- Well-defined networks always induce a locally finite graph. -/
noncomputable instance PNNetwork.to_SimpleGraph_LocallyFinite : N.to_SimpleGraph.LocallyFinite := by
  intro v
  apply Set.Finite.fintype
  have index_finite : Finite {i : ℕ | i < N.deg v} := inferInstance
  apply Set.Finite.of_surjOn (fun i ↦ (N.pmap' (v, i)).node) _ index_finite
  intro u h
  obtain ⟨vp, hp, h⟩ := h
  use vp.index
  subst hp h
  constructor
  · exact vp.port_valid
  · simp [N.pmap_eq_pmap']


/-- Degree in the induced [Mathlib.SimpleGraph] is the same as in the original
network.
-/
@[simp]
lemma PNNetwork.to_SimpleGraph_degree_eq_deg :
    ∀ v : V, N.to_SimpleGraph.degree v = N.deg v := by
  intro v
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset, Set.toFinset_card, ←Finset.card_fin (N.deg v)]
  symm
  apply Finset.card_bij (fun i b ↦ ⟨(N.pmap' (v, i)).node, by
    unfold SimpleGraph.neighborSet
    simp
    apply Adj_of_pmap'
    grind
  ⟩)
  · simp
  · intro i _ j _ h
    ext
    apply s.simple' N v i j i.prop j.prop
    simp_all
  unfold SimpleGraph.neighborSet
  intro u hu
  obtain ⟨u, up, hun, hupn⟩ := u
  subst hun hupn
  use ⟨up.index, up.port_valid⟩
  simp_all [N.pmap_eq_pmap']

end SimplePN

-- Pairing functions for PNNetwork.boxProd
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
    -- Poison value for invalid ports
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

def PNNetwork.boxProd (G : PNNetwork V) (G' : PNNetwork V') : PNNetwork (V × V') where
  deg := fun ⟨v, v'⟩ ↦ (G.deg v) * (G'.deg v')

  pmap' := fun vp ↦
    let pp := unpair (G.deg vp.node.1) (G'.deg vp.node.2) vp.index
    let uq := G.pmap' (vp.node.1, pp.1)
    let uq':= G'.pmap' (vp.node.2, pp.2)
    ((uq.node, uq'.node), pair (G.deg uq.node) (G'.deg uq'.node) (uq.index, uq'.index))

  -- pmap_involutive : ∀ v : V, ∀ i < deg v, pmap (pmap (v, i)) = (v, i)
  pmap'_involutive := by
    intro vu p hp
    -- Give names to all intermediate values
    extract_lets pp uq uq' pp' wq wq'

    -- Show that the ports after the first pmaps are valid. This is needed by unpair_pair lemma
    let valids := unpair_valid _ hp
    have huq_valid : G.PortValid uq := by
      have : G.PortValid (vu.1, (unpair _ _ p).1) := valids.left
      have := (G.is_well_defined_iff _).mpr this
      simp_all [uq, pp]
    have huq'_valid : G'.PortValid uq' := by
      have : G'.PortValid (vu.2, (unpair _ _ p).2) := valids.right
      have := (G'.is_well_defined_iff _).mpr this
      simp_all [uq', pp]

    ext
    all_goals simp_all [wq, wq', uq, pp', pp, uq', Port'.index, Port'.node]


  -- is_well_defined : ∀ vp : Port V, (pmap vp).port < deg (pmap vp).node → vp.port < deg vp.node
  is_well_defined := by
    -- Let vup denote the node we start from and vup' the node with pmap applied to it
    intro vup hvup'_valid

    -- Give names to all intermediate values
    extract_lets pp vp' up' at hvup'_valid

    -- Assume now for contradiction vup is invalid but we still managed to get into a valid vup'
    by_contra hvup_invalid
    simp at hvup_invalid

    -- Divide vup into its part: a port in G (and a port in G' that we ignore)
    let vp : Port' V := (vup.node.1, pp.1)

    -- Because we assumed (for contradiction) that vup is invalid, then its constituent port vp must be invalid
    have hvp_invalid : vp.index ≥ G.deg vup.node.1 := by
      simp_all [unpair_invalid_iff, vp', pp, up', vp]

    -- An invalid port also maps to an invalid port in G
    have hvp'_invalid : ¬G.PortValid vp' := (Nat.not_lt_of_ge $ hvp_invalid) ∘ (G.is_well_defined vp)

    -- We now that pair function maps valid ports to valid ports, and invalid ports to invalid ports.
    -- Let's use that to show that the combination of vp' an up' is invalid, which then immediately leads
    -- to a contradiction.
    exact hvup'_valid.not_ge $ pair_invalid_iff.mp $ Or.inl $ Nat.ge_of_not_lt hvp'_invalid

/-- Box product of PNNetworks. -/
infixl:70 " □ " => PNNetwork.boxProd
