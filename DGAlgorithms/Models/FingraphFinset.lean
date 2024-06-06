import DGAlgorithms.Models.Vector
import Mathlib
import Batteries

open DG renaming Vector → Vec
open SimpleGraph
namespace DG

structure Fingraph (α : Type) (n : Nat) where
  data : Vec α n
  adj_set : Fin n → Finset (Fin n)
deriving BEq



def Vector.fromList (xs : List α) : Vector α xs.length := {
  toArray := {data := xs}
  size_eq := by
    simp only [Array.size_mk]
    done
}

def Vector.toFn (v : Vector α n) : Fin n → α := fun i => v[i]

def fromVec [Inhabited α] (n : Nat)
  (inp : Vector (Finset (Fin n)) n) : Fingraph α n := {
    data := Vec.mkVector n default,
    adj_set := Vector.toFn inp
  }



structure SimpleFinGraph (α : Type) (n : Nat) where
  G : Fingraph α n
  symmetric : ∀ i j : Fin n, j ∈ (G.adj_set i) → i ∈ (G.adj_set j)
  loopless : ∀ i : Fin n, ¬ i ∈ G.adj_set i

namespace SimpleFingraph

@[simp]
def isAdj (g : Fingraph α n) (v w : Fin n) : Prop := w ∈ g.adj_set v

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
    adj_set := fun i => {j : Fin n | g.Adj i j}.toFinset
  }

lemma ofFinGraph_Adj (g : SimpleGraph (Fin n)) [instDec : DecidableRel g.Adj]:
  ∀ i j : Fin n, g.Adj i j →  isAdj (toFinGraph g data) i j := by
  intro i j h_adj
  simp [isAdj, toFinGraph]
  exact h_adj
  done

lemma toFinGraph_Adj (g : SimpleGraph (Fin n)) [instDec : DecidableRel g.Adj]:
  ∀ i j : Fin n, isAdj (toFinGraph g data) i j → g.Adj i j := by
    intro i j
    simp [toFinGraph]
    done

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

@[simp]
def List.isUnique (xs : List α) : Prop :=
  match xs with
  | [] => True
  | y :: ys => ¬ y ∈ ys ∧ List.isUnique ys

@[simp]
def List.toUnique [DecidableEq α] (xs : List α) : List α :=
  match xs with
  | [] => []
  | y :: ys =>
      let ys' := List.toUnique ys
      if y ∈ ys then ys' else y :: ys'


def deg_v (g : SimpleFinGraph α n) (v : Fin n) : ℕ := (g.G.adj_set v).card

def isIsolated (g : SimpleFinGraph α n) (v : Fin n) : Prop :=
  (g.G.adj_set v) = ∅


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
noncomputable def DFS_ConnectedCompAux (g : SimpleFinGraph α n) (start : Fin n) (visited : Fin n → Bool) :=
  if _ : visited start = true
  then visited
  else
    let nextVisited := fun i => if i = start then true else visited i
    let unVisitedNbrs := {node ∈ g.G.adj_set start  | visited node}
    if unVisitedNbrs = ∅ then sorry else sorry

noncomputable def DFS_ConnectedComp (g : SimpleFinGraph α n) (start : Fin n) : Fin n → Bool :=
  DFS_ConnectedCompAux g start (fun _ => false)


lemma isolated_not_sink (g : SimpleFinGraph α n) (v : Fin n) (h : isIsolated g v)
  : ∀ w : Fin n, ¬ isAdj g.G v w := by
  intro w hcontra
  simp [isAdj] at hcontra
  simp [isIsolated] at h
  rw[h] at hcontra
  cases hcontra
  done

def exG : Fingraph (Fin 5) 5 where
  data := Vector.fromList (List.finRange 5)
  adj_set := ![{1}, {0, 2}, {1, 3}, {2, 4}, {3}]

def exGSim: SimpleFinGraph (Fin 5) 5 where
  G := exG
  symmetric := by decide
  loopless := by decide

#eval List.ofFn (fun i => (DFS_ConnectedComp exGSim) i)
#eval exGSim.G.adj_set 1
#eval exGSim.G.adj_set 3


end SimpleFingraph
end DG
