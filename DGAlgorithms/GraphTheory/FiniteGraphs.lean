import Mathlib
import Batteries

open SimpleGraph
namespace DGAlgorithms

-- This is a multigraph

set_option linter.unusedTactic false
set_option linter.unusedVariables false

variable (V : Type)
variable [iFin : FinEnum V] [iDec : DecidableEq V] [Repr V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


structure SimpleFinGraph where
  adj : V → Finset V
  symm : w ∈ adj v → v ∈ adj w
  loopless : v ∉ adj v


def fromSimpleGraph : SimpleFinGraph V := {
  adj := fun v => {w | G.Adj v w}.toFinset,
  symm := by
    intro w v w_adj_v
    -- used aesop below.
    simp_all only [Set.mem_setOf_eq, Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and]
    apply G.symm w_adj_v
  loopless := by
    intro v vmem
    -- used aesop below
    simp_all only [Set.mem_setOf_eq, Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, SimpleGraph.irrefl,
      and_false]
}

def toSimpleGraph (g : SimpleFinGraph V): SimpleGraph V := {
  Adj := fun v w => v ∈ g.adj w,
  symm := by
    intro x y hadj
    solve_by_elim [g.symm]
  loopless := by
    intro x
    solve_by_elim [g.loopless]
}

def deg_v (g : SimpleFinGraph V) (v : V) : ℕ := (g.adj v).card

def isIsolated (g : SimpleFinGraph V) (v : V) : Prop :=
  (g.adj v) = ∅

omit iFin iDec [Repr V] in
lemma isolated_not_sink (g : SimpleFinGraph V) (v : V) (h : isIsolated V g v)
  : ∀ w : V, ¬ v ∈ g.adj w := by
  intro w hcontra
  simp [isIsolated] at h
  apply g.symm at hcontra
  simp_all only [Finset.not_mem_empty]


def isClique (g : SimpleFinGraph V) : Prop :=
  ∀ v w : V, w ∈ g.adj v

def isEmpty (g : SimpleFinGraph V) : Prop :=
  ∀ v w : V, ¬ w ∈ g.adj v


def isWalkList (g : SimpleFinGraph V) (w : List V) : Prop :=
  match w with
  | [] => True
  | [_] => True
  | x :: y :: xs => y ∈ g.adj  x ∧ isWalkList g (y :: xs)

def isPathListAux (g : SimpleFinGraph V) (w : List V) (visited : V → Bool) :=
  match w with
  | [] => True
  | [_] => True
  | x :: y :: xs =>
      y ∈  g.adj x ∧ visited y = false ∧ isPathListAux g (y :: xs) (fun i => if i == y then true else visited i)

def isPathList (g : SimpleFinGraph V) (w : List V) :=
  isPathListAux V g w (fun _ => false)

-- Fix this : def isCycleList (g : SimpleFinGraph V) (w : List V) (h : w.length ≥ 3):=
--  isPathList V g w ∧ (w.get ⟨w.length - 1, by omega⟩) ∈ g.adj (w.get (Fin.ofNat' 0 (by omega)) )



-- now comes the pain
def DFS_ConnectedCompAux (g : SimpleFinGraph V)
  (stack : List V)
  (visited : Finset V) :=
  match stack with
  | [] => (visited, stack)
  | top :: _ =>
      if h_vis : top ∈ visited then
        (visited, stack)
      else
        let nbrs := List.filter (fun w ↦ w ∈ g.adj top ∧ w ∉ visited) (FinEnum.toList V)
        let newstack := nbrs ++ stack
        let newVis := visited ∪ {top}
        DFS_ConnectedCompAux g newstack newVis
    termination_by (visitedᶜ).card
    decreasing_by
      simp_wf
      observe h_subset : visitedᶜ ∩ {top}ᶜ ⊆ visitedᶜ
      have h_neq : visitedᶜ ∩ {top}ᶜ ≠ visitedᶜ := by simp [h_vis]
      observe h_proper_sub : visitedᶜ ∩ {top}ᶜ ⊂ visitedᶜ
      observe hgoal: (visitedᶜ ∩ {top}ᶜ).card < visitedᶜ.card
      exact hgoal





def DFS_ConnectedComp (g : SimpleFinGraph V) (start : V) :=
  DFS_ConnectedCompAux V g [start] ∅

-- now comes the pain
def BFS_ConnectedCompAux (g : SimpleFinGraph V)
  (queue : List V)
  (visited : Finset V) :=
  match queue with
  | [] => (visited, queue)
  | top :: _ =>
      if h_vis : top ∈ visited then
        (visited, queue)
      else
        let nbrs := List.filter (fun w ↦ w ∈ g.adj top ∧ w ∉ visited) (FinEnum.toList V)
        let newQueue := queue ++ nbrs
        let newVis := visited ∪ {top}
        BFS_ConnectedCompAux g newQueue newVis
    termination_by (visitedᶜ).card
    decreasing_by
      simp_wf
      observe h_subset : visitedᶜ ∩ {top}ᶜ ⊆ visitedᶜ
      have h_neq : visitedᶜ ∩ {top}ᶜ ≠ visitedᶜ := by simp [h_vis]
      observe h_proper_sub : visitedᶜ ∩ {top}ᶜ ⊂ visitedᶜ
      observe hg: (visitedᶜ ∩ {top}ᶜ).card < visitedᶜ.card
      exact hg


def BFS_ConnectedComp (g : SimpleFinGraph V) (start : V) :=
  BFS_ConnectedCompAux V g [start] ∅


end DGAlgorithms
