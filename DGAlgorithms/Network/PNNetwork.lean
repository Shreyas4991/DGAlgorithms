import Mathlib

/-!
# Port-Numbered Networks

In this file, we define PN Networks and what it means for a network to be
simple. We then provide the natural coersion from the simple network into a
[Mathlib.SimpleGraph]. Finally, we prove some simplification lemmas.
-/

namespace DGAlgorithms

/-- A shorthand for the type of a port. -/
abbrev Port (V : Type u) : Type u := V × ℕ

abbrev Port.node {V : Type u} (vp : Port V) : V := vp.fst

abbrev Port.port {V : Type u} (vp : Port V) : ℕ := vp.snd

/-- A Port-Numbered Network.

Each node `v` of the network has some `deg v` ports attached to it. Each port
is attached to another port, given by `pmap`. Function `pmap` is involutive,
that is if `p₁` is connected to `p₂`, then `p₂` is also connected to `p₁`.

Note that here we define ports to be pairs of a node and an arbitrary natural
number. In particular, this differes from the more typical definition where a
port is a dependent pair `(v : V) × Fin (deg v)`. We extract this to
`PNNetwork.IsWellDefined`.
 -/
structure PNNetwork (V : Type u) where
  /-- Degree of a node. -/
  deg : V → ℕ
  /-- Map from a given port of a node to the other end of the edge. -/
  pmap : Port V → Port V
  /-- Ensure that ports are properly connected. -/
  pmap_involutive : ∀ v : V, ∀ i < deg v, pmap (pmap (v, i)) = (v, i)
  /-- If pmap takes us to a valid port, then we must have started from a valid port.

  This helps the above involutive property to be sufficient.
  -/
  is_well_defined : ∀ vp : Port V, (pmap vp).port < deg (pmap vp).node → vp.port < deg vp.node



/-- Validity of a port.

A port is valid iff its port number is less than the degree of the node.
-/
abbrev PNNetwork.PortValid {V : Type u} (vp : DGAlgorithms.Port V) (N : PNNetwork V) : Prop := vp.port < N.deg vp.node

def PNNetwork.Port' {V : Type u} (N : PNNetwork V) := { vp : DGAlgorithms.Port V // N.PortValid vp }

abbrev PNNetwork.Port'.node {V : Type u} {N : PNNetwork V} (vp : N.Port') : V := vp.val.node

abbrev PNNetwork.Port'.port {V : Type u} {N : PNNetwork V} (vp : N.Port') : ℕ := vp.val.port

abbrev PNNetwork.Port'.port' {V : Type u} {N : PNNetwork V} (vp : N.Port') : Fin (N.deg vp.node) := ⟨vp.port, vp.prop⟩

@[simp] lemma PNNetwork.pmap_involutive' {V : Type u} (N : PNNetwork V) (vp : Port V) (h : N.PortValid vp) : N.pmap (N.pmap vp) = vp :=
  N.pmap_involutive vp.node vp.port h

-- This doesn't seem very useful
@[simp] lemma PNNetwork.pmap_involutive'' {V : Type u} (N : PNNetwork V) (vp : Port V) (h : N.PortValid (N.pmap (N.pmap vp))) : N.pmap (N.pmap vp) = vp := by
  apply N.pmap_involutive
  exact N.is_well_defined _ (N.is_well_defined _ h)

@[simp] lemma PNNetwork.is_well_defined_iff {V : Type u} (N : PNNetwork V) (vp : Port V) : N.PortValid (N.pmap vp) ↔ N.PortValid vp := by
  constructor
  · intro h
    have := N.is_well_defined _ h
    exact this
  · intro h
    rw [←N.pmap_involutive' vp] at h
    have := N.is_well_defined _ h
    exact this
    exact h

/-- A Simple Port-Numbered Network.

A PN network is simple if it is both loopless and simple, i.e. there are no
duplicate edges.
-/
class SimplePN {V : Type u} (N : PNNetwork V) : Prop where
  /-- There are no edges from a node to itself. -/
  loopless : ∀ v : V, ∀ i j : ℕ, i < N.deg v → N.pmap ⟨v, i⟩ ≠ ⟨v, j⟩
  /-- There is at most one edge between any pair of nodes. -/
  simple : ∀ v : V, ∀ i j : ℕ, i < N.deg v → j < N.deg v → (N.pmap ⟨v, i⟩).node = (N.pmap ⟨v, j⟩).node → i = j

variable {V : Type u} (N : PNNetwork V)

lemma SimplePN.simple_injective [s : SimplePN N] (v : V) :
    Function.Injective fun (i : Fin (N.deg v)) ↦ (N.pmap (v, i)).node := by
  intro ⟨i, hi⟩ ⟨j, hj⟩ h
  simp
  apply s.simple v i j hi hj h

/-- Adjacency relation for a network.

See [Mathlib.SimpleGraph.Adj] for comparison.
-/
def PNNetwork.Adj (u v : V) : Prop :=
  ∃ i < N.deg u, ∃ j < N.deg v, N.pmap ⟨u, i⟩ = ⟨v, j⟩

/-- Another way to define adjacency using only one exists. -/
def PNNetwork.Adj' (u v : V) : Prop :=
  ∃ i < N.deg u, (N.pmap ⟨u, i⟩).node = v

/-- Both definitions of adjacency are equal. -/
lemma PNNetwork.Adj_eq_Adj': Adj N = Adj' N := by
  ext u v
  constructor
  case mp =>
    intro h
    obtain ⟨i, hi, j, hj, h⟩ := h
    use i
    simp_all
  case mpr =>
    intro h
    unfold Adj
    unfold Adj' at h
    obtain ⟨i, hi, h⟩ := h
    subst h
    use i, hi
    use (N.pmap (u, i)).port
    simp [hi]

/-- The induced adjacency relation is symmetric. -/
lemma PNNetwork.Adj.symm : Symmetric (Adj N) := by
  intro u v h
  obtain ⟨i, hi, j, hj, h⟩ := h
  use j, hj, i, hi
  rw [←h, N.pmap_involutive]
  exact hi

variable [s : SimplePN N]

/-- The induced adjacency relation is irreflexive.

This essentially says that induced graph is loopless.
-/
lemma PNNetwork.Adj.irrefl : Irreflexive (Adj N) := by
  intro u h
  obtain ⟨i, hi, j, hj, h⟩ := h
  exact s.loopless u i j hi h

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
  unfold SimpleGraph.neighborSet to_SimpleGraph
  simp_rw [Adj_eq_Adj']
  apply Set.Finite.fintype
  have : Finite {i : ℕ | i < N.deg v} := inferInstance
  exact Set.Finite.of_surjOn (fun i ↦ (N.pmap (v, i)).node) (fun ⦃a⦄ a ↦ a) this

/-- Degree in the induced [Mathlib.SimpleGraph] is the same as in the original
network.
-/
-- @[simp] lemma SimplePN.to_SimpleGraph_degree_eq_deg :
--     ∀ v : V, s.to_SimpleGraph.degree v = N.deg v := by
--   intro v

--   -- Unfold the definition of degree
--   rw [SimpleGraph.degree, SimpleGraph.neighborFinset, Set.toFinset_card]

--   -- We provide a bijection from Fin (N.deg v) to neighbors of v
--   let f : Fin (N.deg v) → { w : V // Adj N v w } := fun i ↦ ⟨(N.pmap ⟨v, i⟩).node, by
--     use i.val, i.prop
--     use (N.pmap ⟨v, i⟩).port, N.is_well_defined (v, i) i.prop
--     rfl
--   ⟩

--   have f_bij : Function.Bijective f := by
--     constructor
--     · intro i j h
--       exact Fin.eq_of_val_eq $ s.simple v i.val j.val i.prop j.prop (Subtype.eq_iff.mp h)
--     · intro u
--       have := u.property.choose
--       obtain ⟨c, hc, _⟩ := u.property.choose_spec
--       use ⟨u.property.choose, c⟩
--       simp_all [f]

--   -- Write n as #(Fin n)
--   rw [←Finset.card_fin (N.deg v)]

--   -- Now the result is immediate
--   symm
--   apply Finset.card_bijective f f_bij
--   simp_all


-- Helper constructor
def PNNetwork.mk' {V : Type u} {deg : V → ℕ} (pmap : (v : V) × Fin (deg v) → (v : V) × Fin (deg v)) (h : Function.Involutive pmap) : PNNetwork V := sorry

instance {V : Type u} {deg : V → ℕ} (pmap : (v : V) × Fin (deg v) → (v : V) × Fin (deg v)) (h : Function.Involutive pmap) : SimplePN (PNNetwork.mk' pmap h) := sorry

-- instance {V : Type u} {deg : V → ℕ} (pmap : (v : V) × Fin (deg v) → (v : V) × Fin (deg v)) (h : Function.Involutive pmap) :
--   PNNetwork.IsWellDefined (PNNetwork.mk' pmap h).toPNNetwork := sorry

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

def PNNetwork.boxProd (G : PNNetwork V) (G' : PNNetwork V') : PNNetwork (V × V') where
  deg := fun ⟨v, v'⟩ ↦ (G.deg v) * (G'.deg v')

  pmap := fun vp ↦
    let pp := unpair (G.deg vp.node.1) (G'.deg vp.node.2) vp.port
    let uq := G.pmap (vp.node.1, pp.1)
    let uq':= G'.pmap (vp.node.2, pp.2)
    ((uq.node, uq'.node), pair (G.deg uq.node) (G'.deg uq'.node) (uq.port, uq'.port))

  -- pmap_involutive : ∀ v : V, ∀ i < deg v, pmap (pmap (v, i)) = (v, i)
  pmap_involutive := by
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

    -- Luckily the simplifier is now on our side
    simp_all [pp', wq, wq', Port.port, uq, uq', pp]

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
    let vp : Port V := (vup.node.1, pp.1)

    -- Because we assumed (for contradiction) that vup is invalid, then its constituent port vp must be invalid
    have hvp_invalid : vp.port ≥ G.deg vup.node.1 := by
      simp_all [unpair_invalid_iff, vp', pp, up', vp]

    -- An invalid port also maps to an invalid port in G
    have hvp'_invalid : ¬G.PortValid vp' := (Nat.not_lt_of_ge $ hvp_invalid) ∘ (G.is_well_defined vp)

    -- We now that pair function maps valid ports to valid ports, and invalid ports to invalid ports.
    -- Let's use that to show that the combination of vp' an up' is invalid, which then immediately leads
    -- to a contradiction.
    exact hvup'_valid.not_ge $ pair_invalid_iff.mp $ Or.inl $ Nat.ge_of_not_lt hvp'_invalid

-- Working proof
    -- intro vup hvumapvalid
    -- simp at hvumapvalid

    -- -- by_cases h' : vp.port < (G.deg vp.node.1) * (G'.deg vp.node.2)
    -- -- · assumption
    --   -- have := pair_unpair _ h'
    --   -- -- have := unpair_pair _ h'
    --   -- simp
    --   -- -- grw [pair_valid]
    --   -- simp at h

    --   -- sorry
    -- -- ·
    -- by_contra hcontra
    -- simp at hcontra
    -- -- simp at hvumapvalid
    -- generalize hw : G.deg vup.node.1 = w at *
    -- generalize hh : G'.deg vup.node.2 = h at *
    -- generalize hvq : (vup.node.1, (unpair w h vup.port).1) = vq at *
    -- generalize hvq' : (vup.node.2, (unpair w h vup.port).2) = vq' at *
    -- -- generalize G.2 vq = uq at *

    -- let vup_dis := unpair w h vup.port
    -- -- let p := vup_dis.1
    -- -- let p' := vup_dis.2

    -- have hp : vup_dis.1 = w := by
    --   apply unpair_invalid at hcontra
    --   subst hw hvq' hvq hh
    --   simp_all only [vup_dis]

    -- have hp' : vup_dis.2 = h := by
    --   apply unpair_invalid at hcontra
    --   subst hw hvq' hvq hh
    --   simp_all only [vup_dis]

    -- have hc : vup_dis.1 ≥ w := Nat.le_of_eq hp.symm
    -- have hc := Nat.not_lt_of_ge hc
    -- have := Nat.ge_of_not_lt $ hvq ▸ hc ∘ (hw ▸ G.is_well_defined (vup.node.1, vup_dis.1))

    -- -- rw [hvq] at this
    -- unfold Port.port at hvumapvalid
    -- -- apply pair_unpair_monotone (w := (G.deg (G.2 vq).1)) (h := h) at hvumapvalid
    -- simp at hvumapvalid

    -- have := pair_left_invalid (G.deg (G.2 vq).1) (G'.deg (G'.2 vq').1) (G.2 vq).2 (G'.2 vq').2 this
    -- rw [this] at hvumapvalid
    -- simp_all

/-- Box product of PNNetworks. -/
infixl:70 " □ " => PNNetwork.boxProd

instance  (G : PNNetwork V) (G' : PNNetwork V') [SimplePN G] [SimplePN G'] : SimplePN (G □ G') := sorry

lemma box_prod_comm (G : PNNetwork V) (G' : PNNetwork V') [SimplePN G] [SimplePN G'] : (G □ G').to_SimpleGraph = (G.to_SimpleGraph □ G'.to_SimpleGraph) := by
  ext v v'

  sorry
