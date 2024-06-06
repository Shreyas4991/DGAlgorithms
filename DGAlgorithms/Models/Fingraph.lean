import DGAlgorithms.Models.Vector
import Mathlib
import Batteries

open DG renaming Vector → Vec
open SimpleGraph
namespace DG

structure Fingraph (α : Type) (n : Nat) where
  data : Vec α n
  adj_list : Fin n → List (Fin n)
deriving Repr, BEq



def Vector.fromList (xs : List α) : Vector α xs.length := {
  toArray := {data := xs}
  size_eq := by
    simp only [Array.size_mk]
    done
}

def Vector.toFn (v : Vector α n) : Fin n → α := fun i => v[i]

def fromVec [Inhabited α] (n : Nat)
  (inp : Vector (List (Fin n)) n) : Fingraph α n := {
    data := Vec.mkVector n default,
    adj_list := Vector.toFn inp
  }

def isFinMem (x : α) (f : Fin n → α) := ∃ i : Fin n, f i = x


structure SimpleFinGraph (α : Type) (n : Nat) where
  G : Fingraph α n
  symmetric : ∀ i j : Fin n, j ∈ (G.adj_list i) → i ∈ (G.adj_list j)
  loopless : ∀ i : Fin n, ¬ i ∈ G.adj_list i

namespace SimpleFingraph

@[simp]
def isAdj (g : Fingraph α n) (v w : Fin n) : Prop := w ∈ g.adj_list v

lemma symm_isAdj (g : SimpleFinGraph α n) : ∀ (v w : Fin n),
  isAdj g.G v w → isAdj g.G w v := by
  intro v w h_adj
  simp [isAdj] at *
  apply g.symmetric v w
  exact h_adj
  done

def toSimpleGraph (g : SimpleFinGraph α n) : SimpleGraph (Fin n) := {
  Adj := fun i j => isAdj g.G i j
  symm := by
    simp only [Symmetric]
    intro x y h
    apply (symm_isAdj g x y)
    exact h
    done
  loopless := by
    simp only [Irreflexive]
    apply g.loopless
}
#check Array.getElem_ofFn_go
#check Array.filter_data

def toFinGraph (g : SimpleGraph (Fin n)) [DecidableRel g.Adj] (data : Fin n → α) :Fingraph α n := {
    data := Vector.ofFn data
    adj_list := fun i =>
        List.filter (fun j => decide <| g.Adj i j) (List.finRange n)
  }

lemma ofFinGraph_Adj (g : SimpleGraph (Fin n)) [instDec : DecidableRel g.Adj]:
  ∀ i j : Fin n, g.Adj i j →  isAdj (toFinGraph g data) i j := by
  intro i j h_adj
  simp [isAdj, toFinGraph]
  rw  [List.mem_filter]
  simp only [List.mem_finRange, decide_eq_true_eq, true_and]
  exact h_adj
  done

lemma toFinGraph_Adj (g : SimpleGraph (Fin n)) [instDec : DecidableRel g.Adj]:
  ∀ i j : Fin n, isAdj (toFinGraph g data) i j → g.Adj i j := by
    intro i j
    simp [toFinGraph]
    intro h
    rw [List.mem_filter] at h
    simp_all only [List.mem_finRange, decide_eq_true_eq, true_and]

lemma toFinGraph_SG_symmetric (data : Fin n → α):
  ∀ (g : SimpleGraph (Fin n)) [DecidableRel g.Adj],
  ∀ i : Fin n, ∀ j : Fin n,
    isAdj (toFinGraph g data) i j
    → isAdj (toFinGraph g data) j i := by
  intro g instDec i j adjh
  apply toFinGraph_Adj at adjh
  apply g.symm at adjh
  apply ofFinGraph_Adj
  exact adjh
  done


lemma toFinGraph_SG_loopless (data : Fin n → α) :
  ∀ (g : SimpleGraph (Fin n)) [DecidableRel g.Adj],
  ∀ i : Fin n, ¬ isAdj (toFinGraph g data) i i := by
  intro g iDec i h
  simp [isAdj, toFinGraph, List.mem_filter] at h
  done

def toSimpleFinGraph (g : SimpleGraph (Fin n)) [instDec : DecidableRel g.Adj] (data : Fin n → α) : SimpleFinGraph α n := {
  G := toFinGraph g data
  symmetric := by apply toFinGraph_SG_symmetric
  loopless := by apply toFinGraph_SG_loopless
}

def deg_v (g : SimpleFinGraph α n) (v : Fin n) : ℕ := (g.G.adj_list v).length

def isIsolated (g : SimpleFinGraph α n) (v : Fin n) : Prop :=
  (g.G.adj_list v).isEmpty = true

def isClique (g : SimpleFinGraph α n) : Prop :=
  ∀ v w : Fin n, isAdj g.G v w

def isEmpty (g : SimpleFinGraph α n) : Prop :=
  ∀ v w : Fin n, ¬ isAdj g.G v w


def isWalkList (g : SimpleFinGraph α n) (w : List (Fin n)) : Prop :=
  match w with
  | [] => True
  | [_] => True
  | x :: y :: xs => isAdj g.G x y ∧ isWalkList g (y :: xs)

def isPathListAux (g : SimpleFinGraph α n) (w : List (Fin n)) (visited : Fin n → Bool) :=
  match w with
  | [] => True
  | [_] => True
  | x :: y :: xs =>
      isAdj g.G x y ∧ visited y = false ∧ isPathListAux g (y :: xs) (fun i => if i == y then true else visited i)

def isPathList (g : SimpleFinGraph α n) (w : List (Fin n)) :=
  isPathListAux g w (fun _ => false)

def isCycleList (g : SimpleFinGraph α n) (w : List (Fin n)) (h : w.length ≥ 3):=
  isPathList g w ∧ isAdj g.G (w.get (Fin.ofNat' 0 (by omega)) ) (w.get ⟨w.length - 1, by omega⟩)



-- Helper lemmas
lemma List.filter_pred: ∀ l : List α, ∀ p : α → Bool,
  x ∈ (List.filter p l) → p x = true := by
  exact fun l p a => List.of_mem_filter a

lemma List.membership : ∀ l r : List α, l = r → ∀ x : α, x ∈ l ↔ x ∈ r := by
  intro l r eq x
  exact Eq.to_iff (congrArg (Membership.mem x) eq)

lemma List.filter_equiv : ∀ l : List α, ∀ p q : α → Bool,
  (List.filter p l) = (List.filter q l) → ∀ x ∈ l, p x ↔ q x := by
  intro l p q heq
  intro x x_elem_l
  apply List.membership at heq
  constructor
  · intro hp
    replace heq := (heq x).mp
    have hfiltp : x ∈ List.filter p l := by
      apply List.mem_filter.mpr
      exact And.intro x_elem_l hp
      done
    apply heq at hfiltp
    have hnext := List.mem_filter.mp hfiltp
    exact hnext.right
  · intro hq
    replace heq := (heq x).mpr
    have hfiltp : x ∈ List.filter q l := by
      apply List.mem_filter.mpr
      exact And.intro x_elem_l hq
      done
    apply heq at hfiltp
    have hnext := List.mem_filter.mp hfiltp
    exact hnext.right
  done


-- now comes the pain
def DFS_ConnectedCompAux (g : SimpleFinGraph α n) (start : Fin n) (visited : Fin n → Bool) :=
  if _ : visited start = true
  then visited
  else
    let nextVisited := fun i => if i = start then true else visited i
    let unVisitedNbrs := List.filter visited (g.G.adj_list start)
    match unVisitedNbrs with
    | [] => nextVisited
    | nbr :: _ => DFS_ConnectedCompAux g nbr nextVisited
  termination_by (List.filter (fun i => !(visited i)) (List.finRange n)).length
  decreasing_by
    simp_wf
    have h1 (i : Fin n) : !(i = start) && !(visited i) → !visited i := by
      simp_all
      done
    set l1 := (List.filter (fun i ↦ !(decide (i = start)) && !visited i)) (List.finRange n)
    set l2 := (List.filter (fun i => !visited i) (List.finRange n))
    have hsub: List.Sublist l1 l2 := by
      apply List.monotone_filter_right
      exact h1
      done
    have hle : l1.length ≤ l2.length := by
      apply List.Sublist.length_le
      apply hsub
      done
    have hne : l1 ≠ l2 := by
      intro heq
      have hiff : ∀ i ∈ List.finRange n, !decide (i = start) && !visited i ↔ !visited i := by
        intro i
        apply List.filter_equiv
        exact heq
        done
      replace hiff := hiff start
      simp_all?
      done
    have hlength_ne : l1.length ≠ l2.length := by
      intro heq_length
      have contra : l1 = l2 := by
        apply List.Sublist.eq_of_length
        exact hsub
        exact heq_length
        done
      exact hne contra
      done
    omega
    done



lemma isolated_not_sink (g : SimpleFinGraph α n) (v : Fin n) (h : isIsolated g v)
  : ∀ w : Fin n, ¬ isAdj g.G v w := by
  intro w hcontra
  simp [isAdj] at hcontra
  simp [isIsolated] at h
  rw[List.isEmpty_iff_eq_nil] at h
  rw[h] at hcontra
  cases hcontra
  done


end SimpleFingraph
end DG
