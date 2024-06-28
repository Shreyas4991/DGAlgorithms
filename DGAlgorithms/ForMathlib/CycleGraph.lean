import DGAlgorithms.ForMathlib.SimpleGraph
import Mathlib.Data.Set.Pointwise.Basic

namespace SimpleGraph

variable {G : Type*} [AddGroup G] (s : Set G)

@[simps!] def CirculantGraph {G : Type*} [AddGroup G] (s : Set G) : SimpleGraph G :=
  fromRel (· - · ∈ s)

lemma circulantGraph_eq_erase_zero : CirculantGraph s = CirculantGraph (s \ {0}) := by
  aesop (add simp sub_eq_zero)

open scoped Pointwise in
lemma circulantGraph_eq_symm : CirculantGraph s = CirculantGraph (s ∪ (-s)) := by aesop

lemma symm_comm_erase_zero : (s \ {0}) ∪ -(s \ {0}) = (s ∪ (-s)) \ {0} := by aesop

lemma circulantGraph_adj_iff (h0 : 0 ∉ s) (hsymm : ∀ x ∈ s, -x ∈ s) {x y : G} :
    (CirculantGraph s).Adj x y ↔ x - y ∈ s := by
  simp only [CirculantGraph_adj]
  constructor
  case mp =>
    rintro ⟨-, h₂ | h₂⟩
    case inl => exact h₂
    case inr => simpa using hsymm _ h₂
  case mpr => aesop

instance {s : Set G} [DecidableEq G] [DecidablePred (· ∈ s)] :
    DecidableRel (CirculantGraph s).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

example {n : ℕ} [NeZero n] {x y z : Fin n} : x + z - (y + z) = x - y := by
  rw [add_sub_add_right_eq_sub]

lemma circulantGraph_adj_translate {s : Set G} {x y d : G} :
    (CirculantGraph s).Adj (x + d) (y + d) ↔ (CirculantGraph s).Adj x y := by aesop

def cycleGraph : (n : ℕ) → SimpleGraph (Fin n)
| 0 => ⊥
| _ + 1 => CirculantGraph {1}

instance : (n : ℕ) → DecidableRel (cycleGraph n).Adj
  | 0 => fun _ _ => inferInstanceAs (Decidable False)
  | _ + 1 => inferInstanceAs (DecidableRel (CirculantGraph _).Adj)

@[simp] lemma cycleGraph_zero_adj {x y : Fin 0} : ¬ (cycleGraph 0).Adj x y := Fin.elim0 x

lemma cycleGraph_one_eq : cycleGraph 1 = ⊥ := Subsingleton.elim _ _

@[simp] lemma cycleGraph_one_adj {x y : Fin 1} : ¬ (cycleGraph 1).Adj x y := by
  rw [cycleGraph_one_eq]
  simp

lemma cycleGraph_adj_iff' {n : ℕ} {x y : Fin (n + 2)} :
    (cycleGraph (n + 2)).Adj x y ↔ x - y = 1 ∨ y - x = 1 := by
  simp only [cycleGraph, CirculantGraph_adj, Finset.mem_singleton, and_iff_right_iff_imp]
  aesop

lemma cycleGraph_adj_iff :
    ∀ {n : ℕ} {x y : Fin n}, (cycleGraph n).Adj x y ↔ (x - y).1 = 1 ∨ (y - x).1 = 1
  | 0, x, y => Fin.elim0 x
  | 1, x, y => by simp
  | n + 2, x, y => by simp only [cycleGraph_adj_iff', Fin.val_eq_one_iff]

lemma cycleGraph_adj_iff_exists {i j : Fin (n + 2)} :
    (cycleGraph (n + 2)).Adj i j ↔ ∃ k : Fin (n + 2), s(i, j) = s(k, k + 1) := by
  rw [cycleGraph_adj_iff', sub_eq_iff_eq_add', sub_eq_iff_eq_add']
  simp [exists_or, or_comm]

lemma cycleGraph_zero_eq_top : cycleGraph 0 = ⊤ := Subsingleton.elim _ _
lemma cycleGraph_one_eq_top : cycleGraph 1 = ⊤ := Subsingleton.elim _ _
lemma cycleGraph_two_eq_top : cycleGraph 2 = ⊤ := by
  simp only [SimpleGraph.ext_iff, Function.funext_iff]; decide
lemma cycleGraph_three_eq_top : cycleGraph 3 = ⊤ := by
  simp only [SimpleGraph.ext_iff, Function.funext_iff]; decide
lemma cycleGraph_eq_top_iff (n : ℕ) (hn : 4 ≤ n) : cycleGraph n < ⊤ := by
  match n, hn with
  | n + 4, _ =>
      rw [lt_top_iff_ne_top]
      intro h
      have h' : (cycleGraph (n + 4)).Adj 0 2 := by simp [h, Fin.ext_iff]
      simp only [cycleGraph_adj_iff, zero_sub, sub_zero, Fin.val_two, OfNat.ofNat_ne_one,
        or_false, Fin.val_eq_one_iff, neg_eq_iff_add_eq_zero] at h'
      rw [Fin.add_def] at h'
      simp only [Fin.val_two, Fin.val_one, Nat.reduceAdd] at h'
      rw [Fin.ext_iff, Fin.val_zero, Fin.val_mk, Nat.mod_eq_of_lt] at h'
      · simp at h'
      · simp

lemma cycleGraph_neighborSet {n : ℕ} {v : Fin (n + 2)} :
    (cycleGraph (n + 2)).neighborSet v = {v - 1, v + 1} := by
  ext w
  simp only [mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [cycleGraph_adj_iff', sub_eq_iff_eq_add', sub_eq_iff_eq_add', eq_sub_iff_add_eq, eq_comm]

lemma cycleGraph_degree_two_le {n : ℕ} {v : Fin (n + 2)} :
    (cycleGraph (n + 2)).degree v = Finset.card {v - 1, v + 1} := by
  have : (cycleGraph (n + 2)).neighborFinset v = ({v - 1, v + 1} : Finset (Fin (n + 2))) :=
    Finset.coe_inj.1 <| by simp [cycleGraph_neighborSet]
  simp [degree, this]

lemma neighbours_diff {v : Fin (n + 3)} :
    v - 1 ≠ v + 1 := by
  rw [ne_eq, sub_eq_iff_eq_add, add_assoc v, self_eq_add_right]
  exact Nat.not_dvd_of_pos_of_lt (by simp) (by simp) ∘ Fin.natCast_eq_zero.1

lemma cycleGraph_degree_three_le {n : ℕ} {v : Fin (n + 3)} :
    (cycleGraph (n + 3)).degree v = 2 := by
  rw [cycleGraph_degree_two_le, Finset.card_pair]
  exact neighbours_diff

@[simp] lemma cycleGraph_adj_castSucc_succ {i : Fin n} :
    (cycleGraph (n + 1)).Adj i.castSucc i.succ := by
  rw [cycleGraph_adj_iff]
  right
  rw [Fin.coe_sub_iff_le.2, Fin.val_succ, Fin.coe_castSucc, add_tsub_cancel_left]
  exact (Fin.castSucc_lt_succ _).le

@[simp] lemma cycleGraph_adj_succ_castSucc {i : Fin n} :
    (cycleGraph (n + 1)).Adj i.succ i.castSucc :=
  cycleGraph_adj_castSucc_succ.symm

@[simp] lemma cycleGraph_adj_zero_last : (cycleGraph (n + 2)).Adj 0 (Fin.last (n + 1)) := by
  simp [cycleGraph_adj_iff']

@[simp] lemma cycleGraph_adj_last_zero : (cycleGraph (n + 2)).Adj (Fin.last (n + 1)) 0 := by
  simp [cycleGraph_adj_iff']

lemma pathGraph_le_cycleGraph {n : ℕ} : pathGraph n ≤ cycleGraph n := by
  match n with
  | 0 => simp
  | n + 1 =>
      intro x y
      simp only [pathGraph_adj_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
        forall_exists_index]
      rintro k (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      case inl => exact cycleGraph_adj_castSucc_succ
      case inr => exact cycleGraph_adj_castSucc_succ.symm

lemma le_iff {G H : SimpleGraph V} : G ≤ H ↔ ∀ x y, G.Adj x y → H.Adj x y := Iff.rfl

lemma pathGraph_sup_edge_le_cycleGraph {n : ℕ} :
    pathGraph (n + 1) ⊔ fromEdgeSet {s(0, Fin.last n)} ≤ cycleGraph (n + 1) := by
  cases n
  case zero => simp
  rename_i n
  rw [sup_le_iff]
  refine ⟨pathGraph_le_cycleGraph, ?_⟩
  simp [SimpleGraph.le_iff, forall_and, or_imp]

lemma pathGraph_add {n : ℕ} :
    pathGraph (n + 1) ⊔ fromEdgeSet {s(0, Fin.last n)} = cycleGraph (n + 1) := by
  refine le_antisymm pathGraph_sup_edge_le_cycleGraph ?_
  cases n
  case zero => simp
  rename_i n
  intro x y h
  rw [cycleGraph_adj_iff_exists] at h
  simp only [Sym2.eq, Sym2.rel_iff', Prod.swap_prod_mk, Prod.mk.injEq] at h
  obtain ⟨k, hk⟩ := h
  wlog hxy : x = k ∧ y = k + 1 generalizing x y
  case inr => exact (this (x := y) (y := x) (by tauto) (by tauto)).symm
  obtain ⟨rfl, rfl⟩ := hxy
  induction x using Fin.lastCases
  case last => simp [Fin.last_pos.ne']
  case cast i =>
    left
    simp only [Fin.coeSucc_eq_succ]
    rw [pathGraph_adj_iff]
    simp

lemma cycleGraph_preconnected {n : ℕ} : (cycleGraph n).Preconnected :=
  (pathGraph_preconnected n).mono pathGraph_le_cycleGraph

lemma cycleGraph_connected {n : ℕ} : (cycleGraph (n + 1)).Connected :=
  (pathGraph_connected n).mono pathGraph_le_cycleGraph

def IsCycleGraph {V : Type*} (G : SimpleGraph V) : Prop := ∃ n, Nonempty (G ≃g cycleGraph n)

end SimpleGraph
