import Mathlib
import DGAlgorithms.Network.PNNetwork

namespace DGAlgorithms


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
  { L | ∀ v w : V, N.Adj v w → L.output v ∨ (L.output w)}


def isIndepVertexSet (N : SimplePN V) : AllowedLabellings V (fun _ => Prop) :=
  { L | ∀ v w : V, L.output v ∧ L.output w →  ¬ N.Adj v w}


def isEdgeCover (N : SimplePN V)  :=
  { L : EdgeSubsetLabelling N | ∀ v w : V, N.Adj v w
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
  send : (d : ℕ) → S → Fin d → M
  recv : (d : ℕ) → S × (Fin d → M) → S -- transition to the next state based on current state and received messages
  stopping_condition : ∀ d : ℕ, ∀ y : Fin d → M, ∀ s : S, s ∈ stopStates → recv d (s, y) = s

structure AlgoState (N: SimplePN V) (S M : Type) where
  state_vec : V → S

abbrev initState (N : SimplePN V) (A : Algorithm I S M) (inp : V → I) : AlgoState N S M where
  state_vec := fun v => A.init (inp v)

abbrev updateState (N : SimplePN V) (A : Algorithm I S M) (cS : AlgoState N S M) : AlgoState N S M :=
  let message_received := fun v port => A.send (N.deg v) (cS.state_vec v) port
  let new_s_vec := fun v => A.recv (N.deg v) (cS.state_vec v, message_received v)
  {
    state_vec := fun v => new_s_vec v
  }





section Trace

/-
From this point there are two ways forward. We can define an operational semantics
for the execution of the algorithm as an inductive type. Alternatively we can define the
execution of an algorithm as a structure. Let's try the inductive structure first.
-/


inductive ExecutionTrace (N : SimplePN V) (A : Algorithm I S M) : AlgoState N S M → ℕ → Type where
  | initState (i : V → I) : ExecutionTrace N A (initState N A i) 0
  | nextState (E : ExecutionTrace N A cs t) : ExecutionTrace N A (updateState N A cs) (t + 1)

variable {A : Algorithm I S M} {N : SimplePN V} {st : AlgoState N S M}

def terminated (_ : ExecutionTrace N A st t) : Prop :=
  ∀ v : V, st.state_vec v ∈ A.stopStates

def terminatedByT (E : ExecutionTrace N A st t) : ℕ → Prop :=
  fun T => terminated E ∧ t ≤ T

def terminatedAtT (E : ExecutionTrace N A st t): ℕ → Prop :=
  fun T => terminatedByT E T ∧ ¬(terminatedByT E (T - 1))

lemma not_term_exists_non_output_state
  (E : ExecutionTrace N A st t):
    ¬terminated E → ∃ v : V, st.state_vec v ∉ A.stopStates := by
  intro h
  simp [terminated] at h
  assumption

end Trace
structure DistributedGraphProblem (N : SimplePN V) (I O : Type) where
  graph_class : Set (SimplePN V)
  input_labellings : Set (PN_Labelling V (fun _ => I))
  output_labellings : Set (PN_Labelling V (fun _ => O))


def Algorithm.initialised (Alg : Algorithm I S M) (N : SimplePN V) (input : V → I) : AlgoState N S M → Prop :=
  fun s ↦ s = initState N Alg input


def Algorithm.Solved (Alg : Algorithm I S M) (N : SimplePN V)
  (Prob : DistributedGraphProblem N I S)  (time : ℕ) : Prop  :=
      ∃ st : AlgoState N S M,
        ∃ E : ExecutionTrace N Alg st time, terminatedByT E time
              ∧ ⟨N, st.state_vec⟩ ∈ Prob.output_labellings


end DGAlgorithms
