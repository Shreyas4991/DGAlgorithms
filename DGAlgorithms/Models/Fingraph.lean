import DGAlgorithms.Models.Vector
import Mathlib
import Batteries
import DGAlgorithms.Models.ListAPI

open DG renaming Vector → Vec
open SimpleGraph
namespace DG

-- This is a multigraph
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



-- Still a multipgraph.
-- When converting to an actual `SimpleGraph`, we use `isAdj` defined below
structure SimpleFinGraph (α : Type) (n : Nat) where
  G : Fingraph α n
  symmetric : ∀ i j : Fin n, j ∈ (G.adj_list i) → i ∈ (G.adj_list j)
  loopless : ∀ i : Fin n, ¬ i ∈ G.adj_list i

namespace SimpleFingraph

@[simp]
def isAdj (g : Fingraph α n) (v w : Fin n) : Prop := w ∈ g.adj_list v -- ignore multi-edges

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

def deg_v (g : Fingraph α n) (v : Fin n) : ℕ := (g.adj_list v).length

def isIsolated (g : SimpleFinGraph α n) (v : Fin n) : Prop :=
  (g.G.adj_list v).isEmpty = true

lemma isolated_not_sink (g : SimpleFinGraph α n) (v : Fin n) (h : isIsolated g v)
  : ∀ w : Fin n, ¬ isAdj g.G v w := by
  intro w hcontra
  simp [isAdj] at hcontra
  simp [isIsolated] at h
  rw[List.isEmpty_iff_eq_nil] at h
  rw[h] at hcontra
  cases hcontra
  done

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



-- now comes the pain
def DFS_ConnectedCompAux (g : Fingraph α n)
  (stack : List (Fin n))
  (visited : Fin n → Bool)
  (traversal_acc : Array (Fin n)):=
  match stack with
  | [] => (visited, stack, traversal_acc)
  | top :: remaining =>
      if visited top
      then
        (visited,stack, traversal_acc)
      else
        let nextVisited := fun i => if i = top then true else visited i
        let unVisitedNbrs := List.filter (fun i => !visited i) (g.adj_list  top)
        let new_traversal_acc := traversal_acc.push top
        let new_stack := unVisitedNbrs ++ remaining
        DFS_ConnectedCompAux g new_stack nextVisited new_traversal_acc
  -- def ends here. termination proof follows
  termination_by (List.filter (fun i => !(visited i)) (List.finRange n)).length
  decreasing_by
    simp_wf
    have h1 (i : Fin n) : !(i = top) && !(visited i) → !visited i := by
      simp_all
      done
    set l1 := List.filter (fun i ↦ !decide (i = top) && !visited i) (List.finRange n)
    set l2 := (List.filter (fun i => !visited i) (List.finRange n))
    have hsub: List.Sublist l1 l2 := by
      solve_by_elim [List.monotone_filter_right]
    have hle : l1.length ≤ l2.length := by
      simp [List.Sublist.length_le, hsub]
    have hne : l1 ≠ l2 := by
      intro heq
      have hiff : ∀ i ∈ List.finRange n, !decide (i = top) && !visited i ↔ !visited i := by
        intros i; solve_by_elim [List.filter_equiv]
      replace hiff := hiff top
      simp_all
    have hlength_ne : l1.length ≠ l2.length := by
      intro heq_length
      have contra : l1 = l2 := by
        solve_by_elim [List.Sublist.eq_of_length]
      tauto
    omega


def DFS_ConnectedComp (g : Fingraph α n) (start : Fin n) :=
  DFS_ConnectedCompAux g [start] (fun _ => false) #[]

-- now comes the pain
def BFS_ConnectedCompAux (g : Fingraph α n)
  (queue : List (Fin n))
  (visited : Fin n → Bool)
  (traversal_acc : Array (Fin n)):=
  match queue with
  | [] => (visited, queue, traversal_acc)
  | top :: remaining =>
      if visited top
      then
        (visited, queue, traversal_acc)
      else
        let nextVisited := fun i => if i = top then true else visited i
        let unVisitedNbrs := List.filter (fun i => !visited i) (g.adj_list  top)
        let new_trav_acc := traversal_acc.push top
        let new_queue := remaining ++ unVisitedNbrs
        BFS_ConnectedCompAux g new_queue nextVisited new_trav_acc
  -- def ends here. termination proof follows
  termination_by (List.filter (fun i => !(visited i)) (List.finRange n)).length
  decreasing_by
    simp_wf
    have h1 (i : Fin n) : !(i = top) && !(visited i) → !visited i := by
      simp_all
      done
    set l1 := List.filter (fun i ↦ !decide (i = top) && !visited i) (List.finRange n)
    set l2 := (List.filter (fun i => !visited i) (List.finRange n))
    have hsub: List.Sublist l1 l2 := by
      solve_by_elim [List.monotone_filter_right]
    have hle : l1.length ≤ l2.length := by
      simp [List.Sublist.length_le, hsub]
    have hne : l1 ≠ l2 := by
      intro heq
      have hiff : ∀ i ∈ List.finRange n, !decide (i = top) && !visited i ↔ !visited i := by
        intros i; solve_by_elim [List.filter_equiv]
      replace hiff := hiff top
      simp_all
    have hlength_ne : l1.length ≠ l2.length := by
      intro heq_length
      have contra : l1 = l2 := by
        solve_by_elim [List.Sublist.eq_of_length]
      tauto
    omega


def BFS_ConnectedComp (g : Fingraph α n) (start : Fin n) :=
  BFS_ConnectedCompAux g [start] (fun _ => false)  #[]

def exG : Fingraph (Fin 7) 7 where
  data := Vector.fromList (List.finRange 7)
  adj_list := ![{1}, {0, 2}, {1, 3}, {2, 4}, {3}, {6}, {5}]

def exGSim: SimpleFinGraph (Fin 7) 7 where
  G := exG
  symmetric := by decide
  loopless := by decide

/-
          0
        /   \
       /     \
      1       2
    /   \    /  \
   3     4  5    6
          /   \
         7     8
-/
def exG2 : Fingraph (Fin 9) 9 where
  data := Vector.fromList (List.finRange 9)
  adj_list := ![{1,2}, {0,3,4}, {0,5,6}, {1}, {1}, {2,7,8}, {2},{5},{5}]

def exGSim2: SimpleFinGraph (Fin 9) 9 where
  G := exG2
  symmetric := by decide
  loopless := by decide

#eval List.ofFn (fun i => (DFS_ConnectedComp exG i))
#eval List.ofFn (fun i => (BFS_ConnectedComp exG i))
#eval List.ofFn (fun i => (DFS_ConnectedComp exG2 i).2.2) -- DFS traversal order
#eval List.ofFn (fun i => (BFS_ConnectedComp exG2 i).2.2) -- BFS traversal order
#eval exGSim2.G.adj_list 1
#eval exGSim.G.adj_list 3

end SimpleFingraph
end DG
