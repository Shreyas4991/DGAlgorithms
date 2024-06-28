import Mathlib.Tactic.IntervalCases
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Set.Card

lemma Fin.val_eq_one_iff {n : ℕ} (x : Fin (n + 2)) : (x : ℕ) = 1 ↔ x = 1 := by
  rw [Fin.ext_iff, Fin.val_one]

lemma Set.ncard_congr' {α β : Type*} {s : Set α} {t : Set β} (e : s ≃ t) : s.ncard = t.ncard := by
  rw [Set.ncard_def, Set.ncard_def, Set.encard_congr e]

namespace SimpleGraph

@[simp] lemma coe_neighborFinset {G : SimpleGraph V} {v : V} [Fintype (G.neighborSet v)] :
    G.neighborFinset v = G.neighborSet v := Set.coe_toFinset _

theorem degree_eq_zero_iff_forall_adj {V : Type*} (G : SimpleGraph V) (v : V)
    [Fintype (G.neighborSet v)] :
    G.degree v = 0 ↔ ∀ w, ¬ G.Adj v w := by
  rw [←le_zero_iff, ←not_lt, degree_pos_iff_exists_adj, not_exists]

lemma degree_subsingleton
    {V : Type*} [Subsingleton V] (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] :
    G.degree v = 0 := by
  rw [degree_eq_zero_iff_forall_adj]
  intro w hw
  exact hw.ne (Subsingleton.elim v w)

lemma maxDegree_subsingleton {V : Type*} [Subsingleton V] [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : G.maxDegree = 0 :=
  le_zero_iff.1 <| maxDegree_le_of_forall_degree_le _ _
    fun _ => le_zero_iff.2 <| degree_subsingleton _ _

lemma maxDegree_empty {V : Type*} [IsEmpty V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.maxDegree = 0 :=
  maxDegree_subsingleton _

lemma degree_bot {V : Type*} (v : V) [Fintype ((⊥ : SimpleGraph V).neighborSet v)] :
    (⊥ : SimpleGraph V).degree v = 0 := by
  suffices ¬ 0 < (⊥ : SimpleGraph V).degree v by omega
  rw [degree_pos_iff_exists_adj]
  simp

lemma maxDegree_bot {V : Type*} [Fintype V] : (⊥ : SimpleGraph V).maxDegree = 0 :=
  le_zero_iff.1 <| maxDegree_le_of_forall_degree_le _ _ fun _ => le_zero_iff.2 <| degree_bot _

lemma neighborSet_top {V : Type*} (v : V) : (⊤ : SimpleGraph V).neighborSet v = {v}ᶜ := by
  ext w; simp [eq_comm]

lemma neighborFinset_top {V : Type*} [Fintype V] [DecidableEq V] (v : V)
    [Fintype ((⊤ : SimpleGraph V).neighborSet v)] :
    (⊤ : SimpleGraph V).neighborFinset v = {v}ᶜ := by
  ext w; simp [eq_comm]

lemma degree_top {V : Type*} [Fintype V] (v : V) [Fintype ((⊤ : SimpleGraph V).neighborSet v)] :
    (⊤ : SimpleGraph V).degree v = Fintype.card V - 1 := by
  classical
  rw [degree, neighborFinset_top, Finset.card_compl, Finset.card_singleton]

lemma maxDegree_top {V : Type*} [Fintype V] [DecidableEq V] :
    (⊤ : SimpleGraph V).maxDegree = Fintype.card V - 1 := by
  rcases isEmpty_or_nonempty V with hv | hv
  case inl => rw [maxDegree_empty, Fintype.card_eq_zero]
  case inr =>
    obtain ⟨v, hv⟩ := exists_maximal_degree_vertex (⊤ : SimpleGraph V)
    rw [hv, degree_top]

lemma degree_eq_ncard {V : Type*} {G : SimpleGraph V} (v : V) [Fintype (G.neighborSet v)] :
    G.degree v = (G.neighborSet v).ncard := by
  rw [degree, ←Set.ncard_coe_Finset, coe_neighborFinset]

lemma degree_iso {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H)
    (v : V) [Fintype (G.neighborSet v)] [Fintype (H.neighborSet (e v))] :
    G.degree v = H.degree (e v) := by
  rw [degree_eq_ncard, degree_eq_ncard, Set.ncard_congr' (e.mapNeighborSet v)]

lemma bot_preconnected [Subsingleton V] (G : SimpleGraph V) : G.Preconnected :=
  fun u v => Subsingleton.elim u v ▸ by rfl

lemma bot_walk_nil {u v : V} : (p : (⊥ : SimpleGraph V).Walk u v) → p.Nil | .nil => .nil

lemma bot_not_preconnected [Nontrivial V] : ¬(⊥ : SimpleGraph V).Preconnected := fun h => by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne V
  obtain ⟨h⟩ := h x y
  exact hxy (bot_walk_nil h).eq

lemma bot_connected [Nonempty V] [Subsingleton V] : (⊥ : SimpleGraph V).Connected where
  preconnected := bot_preconnected _

lemma bot_not_connected [Nontrivial V] : ¬(⊥ : SimpleGraph V).Connected := fun h =>
  bot_not_preconnected h.preconnected

/-- The condition for a graph to be a path graph. -/
def IsPath {V : Type u} (G : SimpleGraph V) : Prop := ∃ n, Nonempty (G ≃g pathGraph n)

instance {α : Type*} [LT α] [Fintype α] [DecidableRel (· < · : α → α → Prop)] :
    DecidableRel (· ⋖ · : α → α → Prop) :=
  fun x y => inferInstanceAs (Decidable (x < y ∧ _))

instance DecidableRel_hasse_adj {α : Type*} [Preorder α] [Fintype α]
    [DecidableRel (· < · : α → α → Prop)] :
    DecidableRel (hasse α).Adj :=
  fun x y => inferInstanceAs (Decidable (x ⋖ y ∨ _))

instance {n : ℕ} : DecidableRel (pathGraph n).Adj := DecidableRel_hasse_adj

lemma hasse_neighborSet {α : Type*} [LinearOrder α] (v : α) :
    ∃ x y : α, (hasse α).neighborSet v ⊆ {x, y} := by
  classical
  refine ⟨if h : ∃ x : α, v ⋖ x then h.choose else v, if h : ∃ y : α, y ⋖ v then h.choose else v,
    fun z => ?_⟩
  simp only [mem_neighborSet, hasse_adj, Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro (h | h)
  · left
    rw [dif_pos ⟨_, h⟩]
    exact h.unique_right (Classical.choose_spec _)
  · right
    rw [dif_pos ⟨_, h⟩]
    exact h.unique_left (Classical.choose_spec (p := (· ⋖ v)) _)

lemma hasse_neighbor_set_finite {α : Type*} [LinearOrder α] (v : α) :
    ((hasse α).neighborSet v).Finite :=
  have ⟨x, y, h⟩ := hasse_neighborSet v
  Set.Finite.subset (by simp) h

/--
Note there is no way of making this computable, consider {0, 1} with the order 0 < 1 iff p.
Then the neighbor set of 0 is {1} if p, and ∅ otherwise, so if this definition were computable, we
could compute the degree of 0 and thus compute p.
-/
noncomputable instance hasse_locally_finite {α : Type*} [LinearOrder α] (v : α) :
    Fintype ((hasse α).neighborSet v) :=
  @Fintype.ofFinite _ (hasse_neighbor_set_finite v)

noncomputable instance pathGraph_locally_finite {n : ℕ} (x : Fin n) :
    Fintype ((pathGraph n).neighborSet x) :=
  hasse_locally_finite _

lemma hasse_neighborFinset {α : Type*} [LinearOrder α] (v : α) [Fintype ((hasse α).neighborSet v)] :
    ∃ x y : α, (hasse α).neighborFinset v ⊆ {x, y} :=
  have ⟨x, y, h⟩ := hasse_neighborSet v
  ⟨x, y, by simpa [←Finset.coe_subset]⟩

lemma hasse_degree_le {α : Type*} [LinearOrder α] (v : α)
    [Fintype ((hasse α).neighborSet v)] : (hasse α).degree v ≤ 2 :=
  have ⟨_, _, h⟩ := hasse_neighborFinset v
  (Finset.card_le_card h).trans Finset.card_le_two

lemma hasse_maxDegree_le {α : Type*} [Fintype α] [LinearOrder α]
    [DecidableRel (· < · : α → α → Prop)] : (hasse α).maxDegree ≤ 2 :=
  maxDegree_le_of_forall_degree_le _ _
    fun v => @hasse_degree_le _ _ _ ((hasse α).neighborSetFintype v)

lemma pathGraph_adj_iff {i j : Fin (n + 1)} :
    (pathGraph (n + 1)).Adj i j ↔ ∃ k : Fin n, s(i, j) = s(k.castSucc, k.succ) := by
  constructor
  case mpr =>
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, forall_exists_index]
    rintro k (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    case inl => simp [pathGraph_adj]
    case inr => simp [pathGraph_adj]
  case mp =>
    intro h
    rw [pathGraph_adj] at h
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, Fin.exists_iff,
      Fin.castSucc_mk, Fin.succ_mk, Nat.succ_eq_add_one, Fin.ext_iff, exists_prop]
    cases h with
    | inl h => exact ⟨i, by omega, Or.inl ⟨rfl, h.symm⟩⟩
    | inr h => exact ⟨j, by omega, Or.inr ⟨h.symm, rfl⟩⟩

lemma pathGraph_neighborSet_zero {n : ℕ} : (pathGraph (n + 2)).neighborSet 0 = {1} := by
  ext i
  simp [pathGraph_adj, eq_comm, Fin.ext_iff]

lemma pathGraph_neighborSet_last {n : ℕ} :
    (pathGraph (n + 2)).neighborSet (Fin.last (n + 1)) = {(Fin.last n).castSucc} := by
  ext i
  simp [pathGraph_adj, i.isLt.ne', Fin.ext_iff]

lemma pathGraph_neighborSet_middle {n : ℕ} (i : Fin n) :
    (pathGraph (n + 2)).neighborSet i.succ.castSucc =
      {i.castSucc.castSucc, i.succ.succ} := by
  ext j
  simp [pathGraph_adj, Fin.ext_iff, or_comm, eq_comm]

lemma pathGraph_degree_zero {n : ℕ} : (pathGraph (n + 2)).degree 0 = 1 := by
  have : (pathGraph (n + 2)).neighborFinset 0 = {1} :=
    Finset.coe_inj.1 <| by simp [pathGraph_neighborSet_zero]
  simp [degree, this]

lemma pathGraph_degree_last {n : ℕ} : (pathGraph (n + 2)).degree (Fin.last (n + 1)) = 1 := by
  have : (pathGraph (n + 2)).neighborFinset (Fin.last (n + 1)) = {(Fin.last n).castSucc} :=
    Finset.coe_inj.1 <| by simp [pathGraph_neighborSet_last]
  simp [degree, this]

lemma pathGraph_degree_middle {n : ℕ} (i : Fin n) :
    (pathGraph (n + 2)).degree i.succ.castSucc = 2 := by
  have : (pathGraph (n + 2)).neighborFinset i.succ.castSucc =
      {i.castSucc.castSucc, i.succ.succ} :=
    Finset.coe_inj.1 <| by simp [pathGraph_neighborSet_middle]
  rw [degree, this, Finset.card_pair]
  simp only [←Fin.val_ne_iff, Fin.coe_castSucc, Fin.val_succ]
  omega

lemma pathGraph_degree_le {n : ℕ} (v : Fin n) : (pathGraph n).degree v ≤ 2 :=
  hasse_degree_le _

lemma pathGraph_maxDegree_le {n : ℕ} : (pathGraph n).maxDegree ≤ 2 :=
  hasse_maxDegree_le

lemma pathGraph_zero_eq_top : pathGraph 0 = ⊤ := Subsingleton.elim _ _
lemma pathGraph_one_eq_top : pathGraph 1 = ⊤ := Subsingleton.elim _ _

@[simp] lemma pathGraph_maxDegree_zero : (pathGraph 0).maxDegree = 0 := maxDegree_empty _
@[simp] lemma pathGraph_maxDegree_one : (pathGraph 1).maxDegree = 0 := maxDegree_subsingleton _
@[simp] lemma pathGraph_maxDegree_two : (pathGraph 2).maxDegree = 1 := by
  simp [pathGraph_two_eq_top, maxDegree_top]

lemma pathGraph_maxDegree' {n : ℕ} : (pathGraph (n + 3)).maxDegree = 2 := by
  refine le_antisymm pathGraph_maxDegree_le ?_
  refine ((pathGraph (n + 3)).degree_le_maxDegree 1).trans_eq' ?_
  convert (pathGraph_degree_middle 0).symm

lemma pathGraph_maxDegree : {n : ℕ} → 3 ≤ n → (pathGraph n).maxDegree = 2
| _ + 3, _ => pathGraph_maxDegree'

lemma pathGraph_maxDegree_eq_two_iff {n : ℕ} : (pathGraph n).maxDegree = 2 ↔ 3 ≤ n := by
  refine ⟨fun h => ?_, pathGraph_maxDegree⟩
  contrapose! h
  interval_cases n <;> simp

private lemma maxDegree_iso_aux {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [Fintype V] [Fintype W] (e : G ≃g H) :
    G.maxDegree ≤ H.maxDegree :=
  maxDegree_le_of_forall_degree_le _ _ fun v => by
    rw [degree_iso G H e v]
    exact degree_le_maxDegree _ _

lemma maxDegree_iso {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [Fintype V] [Fintype W] (e : G ≃g H) :
    G.maxDegree = H.maxDegree :=
  le_antisymm (maxDegree_iso_aux _ _ e) (maxDegree_iso_aux _ _ e.symm)

lemma isPath.maxDegree {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsPath) :
    G.maxDegree ≤ 2 := by
  obtain ⟨n, ⟨e⟩⟩ := hG
  rw [maxDegree_iso _ _ e]
  exact pathGraph_maxDegree_le

end SimpleGraph
