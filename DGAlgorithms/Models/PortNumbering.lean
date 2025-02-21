import Mathlib

structure PN_Net (V : Type u) where
  deg : V → ℕ
  pmap : ((v : V) × Fin (deg v)) → ((w : V) × (Fin (deg w)))
  p_involutive : ∀ x : (v : V) × (Fin (deg v)), pmap (pmap x) = x

structure SimplePN (V : Type u) extends PN_Net V where
  loopless : ∀ v : V, ∀ i j : Fin (deg v), pmap ⟨v,i⟩ ≠ ⟨v, j⟩
  simple : ∀ v w : V, ∀ i : Fin (deg v), ∀ j k : Fin (deg w), pmap ⟨v,i⟩ = pmap ⟨w,j⟩ ∧ pmap ⟨v, i⟩ = pmap ⟨w,k⟩ → j = k


def SimplePN.connected (N : SimplePN V) (u v : V) : Prop :=
  ∃ i, ∃ j, N.pmap ⟨u,i⟩ = ⟨v,j⟩

lemma connected_symm (N : SimplePN V) : N.connected u v → N.connected v u := by
  intro h
  simp_all[SimplePN.connected]
  cases' h with p₁ h
  cases' h with p₂ h
  use p₂, p₁
  rw [←h, N.p_involutive ⟨u, p₁⟩]

lemma loopless (N : SimplePN V) : ¬ N.connected u u := by
  intro h
  simp[SimplePN.connected, N.loopless] at h

def underlyingSimpleGraph (V : Type) (N : SimplePN V) : SimpleGraph V where
  Adj := fun x y => N.connected x y
  symm := by
    intro v w h
    solve_by_elim [connected_symm]

  loopless := by
    intro u h
    solve_by_elim [loopless]


-- A lemma that just says that if two PN nodes are connected,
-- then they are adjacent in the underlying graph
lemma connected_adjacent :
  ∀ (N : SimplePN V),
    ∀ v w : V, N.connected v w → (underlyingSimpleGraph V N).Adj v w := by
    intro N v w hconn
    simp[underlyingSimpleGraph, hconn]



structure PN_Labelling (V : Type u) (Γ : V → Type u) where -- here Γ is the type of output labels
  network : SimplePN V
  output : (v : V) → Γ v -- the output type can in general be dependent on the vertex. We use this for edge labellings

abbrev NodeSubset_Labelling (V : Type) := PN_Labelling V (fun _ => Prop)




structure EdgeLabelling (N : SimplePN V) (L : Type) extends PN_Labelling  V (fun (v : V)  => (Fin (N.deg v)) → L) where
  consistency :
      ∀ v w : V, ∀ i : Fin (N.deg v), ∀ j : Fin (N.deg w), (N.pmap ⟨v,i⟩) = ⟨w,j⟩
        → output v i = output w j
-- the edge labelling must also be consistent


abbrev EdgeSubsetLabelling (N : SimplePN V) :=
  EdgeLabelling N Prop


-- edge orientation labellings are anti-consistent
structure EdgeOrientationLabelling (N : SimplePN V) extends PN_Labelling  V (fun (v : V)  => (Set <| Fin (N.deg v))) where
  anti_consistency :
      ∀ v w : V, ∀ i : Fin (N.deg v), ∀ j : Fin (N.deg w), (N.pmap ⟨v,i⟩) = ⟨w,j⟩
        → i ∈ output v ↔  j ∉ output w


abbrev AllowedLabellings (V : Type u) (Γ : V → Type u) := Set (PN_Labelling V Γ)


namespace ExampleProblems

-- trivially label all vertices true
def ex1 (N : SimplePN V) : NodeSubset_Labelling V where
  network := N
  output := Set.univ

-- trivially label all edges true
def ex2 (N : SimplePN V) : EdgeSubsetLabelling N where
  network := N
  output := fun _ => Set.univ
  consistency := by
    intro v w i j h
    simp
    tauto


def is_VC (N : SimplePN V) : AllowedLabellings V (fun _ => Prop) :=
  { L | ∀ v w : V, N.connected v w → L.output v ∨ (L.output w)}


def isIndepVertexSet (N : SimplePN V) : AllowedLabellings V (fun _ => Prop) :=
  { L | ∀ v w : V, L.output v ∧ L.output w →  ¬ N.connected v w}


def isEdgeCover (N : SimplePN V)  :=
  { L : EdgeSubsetLabelling N | ∀ v w : V, N.connected v w
      → (∃ i : Fin (N.deg v), L.output v i) ∨ (∃ j : Fin (N.deg w), L.output w j) }

end ExampleProblems


/--
An `Algorithm` is parameterised by the type of inputs `I`, states `S`, and messages `M`.
We also add the node degree `d` as a parameter so that we can use `Fin d` to represent port specific
messages. The alternative is to use the `Option` type for messages, which is much more tedious
`stopStates` is the subset of states at which the algorithm halts
-/
structure Algorithm (I S M: Type) where
  stopStates : Set S
  init : I → S -- initialises the SM to start state from the input
  send : S → ℕ → M
  recv : S × (ℕ → M) → S -- transition to the next state based on current state and received messages
  stopping_condition : ∀ y : ℕ → M, ∀ s : S, s ∈ stopStates → recv (s, y) = s

structure AlgoState (N: SimplePN V) (S M : Type) where
  state_vec : V → S
  round : ℕ

abbrev initState (N : SimplePN V) (A : Algorithm I S M) (inp : V → I) : AlgoState N S M where
  state_vec := fun v => A.init (inp v)
  round := 0

abbrev updateState (N : SimplePN V) (A : Algorithm I S M) (cS : AlgoState N S M) : AlgoState N S M :=
  let message_received := fun v port => A.send (cS.state_vec v) port
  let new_s_vec := fun v => A.recv (cS.state_vec v, message_received v)
  {
    state_vec := fun v => new_s_vec v
    round := cS.round + 1
  }

def terminated (A : Algorithm I S M) (N : SimplePN V) (state : AlgoState N S M): Prop :=
  ∀ v : V, state.state_vec v ∈ A.stopStates

def terminatedByT (A : Algorithm I S M) (N : SimplePN V) (state : AlgoState N S M) : ℕ → Prop :=
  fun T => terminated A N state ∧ state.round ≤ T
/-
From this point there are two ways forward. We can define an operational semantics
for the execution of the algorithm as an inductive type. Alternatively we can define the
execution of an algorithm as a structure. Let's try the inductive structure first.
-/
def terminatedAtT (A : Algorithm I S M) (N : SimplePN V) (state : AlgoState N S M) : ℕ → Prop :=
  fun T => terminatedByT A N state T ∧ ¬(terminatedByT A N state (T - 1))


/--helper lemma for termination -/
lemma not_term_exists_non_output_state
  (N : SimplePN V)
  (A : Algorithm I S M) :
    ∀ state : AlgoState N S M, ¬terminated (A : Algorithm I S M) N state
    → ∃ v : V, state.state_vec v ∉ A.stopStates := by
  intro s h
  simp [terminated] at h
  assumption


inductive ExecutionTrace (N : SimplePN V) (A : Algorithm I S M) : AlgoState N S M → Type where
  | initState (i : V → I) : ExecutionTrace N A (initState N A i)
  | nextState (cs : AlgoState N S M) : ExecutionTrace N A (updateState N A cs)


structure DistributedGraphProblem (N : SimplePN V) (I O : Type) where
  graph_class : Set (SimplePN V)
  input_labellings : Set (PN_Labelling V (fun _ => I))
  output_labellings : Set (PN_Labelling V (fun _ => O))


def Algorithm.initialised (Alg : Algorithm I S M) (N : SimplePN V) (input : V → I) : AlgoState N S M → Prop :=
  fun s ↦ s = initState N Alg input


def Algorithm.Solved (Alg : Algorithm I S M) (N : SimplePN V)
  (Prob : DistributedGraphProblem N I S)  (time : ℕ) : Prop  :=
    ∃ S, terminatedAtT Alg N S time ∧ ⟨N,S.state_vec⟩ ∈ Prob.output_labellings
