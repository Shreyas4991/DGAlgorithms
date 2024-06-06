import Mathlib
import DGAlgorithms.ForMathlib.SimpleGraph

/-- Simple port numbered networks -/
structure PortNumbered (V : Type*) extends SimpleGraph V :=
/-- The underlying graph is locally finite. -/
[lf : toSimpleGraph.LocallyFinite]
/--
For every node, we have a bijection between its neighbors and an index. This is
the numbering of the ports.
-/
(numbering : (v : V) → toSimpleGraph.neighborSet v ≃ Fin (toSimpleGraph.degree v))

namespace PortNumbered

variable {V : Type*}

instance : Coe (PortNumbered V) (SimpleGraph V) := ⟨PortNumbered.toSimpleGraph⟩
instance {N : PortNumbered V} : N.LocallyFinite := N.lf

variable (N : PortNumbered V)

/-- Given a port number, return the node it connects to. -/
def ofPort (v : V) (i : Fin (N.degree v)) : V := (N.numbering v).symm i
@[simp] lemma ofPort_adj {v : V} (i : Fin (N.degree v)) : N.Adj v (N.ofPort v i) := by
  simpa [ofPort] using ((N.numbering v).symm i).2
/-- Given an adjacent node, return the port to reach it. -/
def toPort (v w : V) (h : N.Adj v w) : Fin (N.degree v) := N.numbering v ⟨w, by simp [h]⟩

@[simp] lemma ofPort_toPort {v w : V} (h : N.Adj v w) : N.ofPort v (N.toPort v w h) = w := by
  simp [ofPort, toPort]

@[simp] lemma toPort_ofPort {v : V} (i : Fin (N.degree v)) :
    N.toPort v (N.ofPort v i) (N.ofPort_adj i) = i := by
  simp [ofPort, toPort]

lemma ofPort_injective (v : V) : Function.Injective (N.ofPort v) := by
  intro i j h
  simp only [ofPort] at h
  refine (N.numbering v).symm.injective ?_
  ext1
  exact h

lemma ofPort_cast (v w : V) (h : v = w) (i : Fin (N.degree v)) :
    N.ofPort w (Fin.cast (by rw [h]) i) = N.ofPort v i := by
  cases h
  rfl

lemma forall_ports {v : V} {p : Fin (N.degree v) → Prop} :
    (∀ i, p i) ↔ ∀ (w : V) (h : N.Adj v w), p (N.toPort v w h) := by
  simp [Equiv.forall_congr_left' (N.numbering v).symm, toPort]

lemma forall_adj {v : V} {p : (w : V) → (h : N.Adj v w) → Prop} :
    (∀ w (h : N.Adj v w), p w h) ↔ ∀ i, p (N.ofPort v i) (N.ofPort_adj _) := by
  simp [forall_ports]

lemma exists_ports {v : V} {p : Fin (N.degree v) → Prop} :
    (∃ i : Fin (N.degree v), p i) ↔ ∃ (w : V) (h : N.Adj v w), p (N.toPort v w h) := by
  simp [Equiv.exists_congr_left (N.numbering v).symm, toPort]

lemma exists_adj {v : V} {p : (w : V) → (h : N.Adj v w) → Prop} :
    (∃ (w : V) (h : N.Adj v w), p w h) ↔ ∃ i, p (N.ofPort v i) (N.ofPort_adj _) := by
  simp [exists_ports]

/-- The port which sends data *to* port i. -/
def reversePort (v : V) (i : Fin (N.degree v)) : Fin (N.degree (N.ofPort v i)) :=
  N.toPort (N.ofPort v i) v (by simp [N.adj_comm])

lemma reversePort_cast (v w : V) (h : v = w) (i : Fin (N.degree v)) :
    N.reversePort w (Fin.cast (by rw [h]) i) =
      Fin.cast (by rw [ofPort_cast _ _ _ h]) (N.reversePort v i) := by
  cases h
  rfl

@[simp] lemma ofPort_reversePort (v : V) (i : Fin (N.degree v)) :
    N.ofPort (N.ofPort v i) (N.reversePort v i) = v := by
  simp only [reversePort, ofPort_toPort]

lemma reversePort_reversePort (v : V) (i : Fin (N.degree v)) :
    Fin.cast (by rw [ofPort_reversePort])
      (N.reversePort (N.ofPort v i) (N.reversePort v i)) = i :=
  N.ofPort_injective _ <| by rw [ofPort_cast] <;> simp

lemma coe_reversePort_reversePort (v : V) (i : Fin (N.degree v)) :
    (N.reversePort (N.ofPort v i) (N.reversePort v i) : ℕ) = i :=
  congrArg Fin.val (N.reversePort_reversePort v i)

/-- The type of ports in the network N. -/
def Ports := (v : V) × Fin (N.degree v)
/-- The involution on ports defined in the textbook. -/
def p : N.Ports → N.Ports := fun z => ⟨N.ofPort z.1 z.2, N.reversePort z.1 z.2⟩

@[ext]
lemma ports_eq (u v : N.Ports)
    (nodes_eq : u.1 = v.1) (cast_ports_eq : Fin.cast (by rw [nodes_eq]) u.2 = v.2) : u = v := by
  cases' u with u i
  cases' v with v j
  cases nodes_eq
  simp only [Fin.cast_eq_self] at cast_ports_eq
  simp [cast_ports_eq]

lemma p_invol : Function.Involutive N.p := by
  rintro ⟨v, i⟩
  simp only [p]
  ext : 1
  · simp only [ofPort_reversePort]
  · rw [reversePort_reversePort]

/-- From a port number, produce the edge it corresponds to. -/
def edgeOfPort (v : V) (i : Fin (N.degree v)) : N.edgeSet := ⟨s(v, N.ofPort v i), by simp⟩

-- /-- A node labelling of a port numbered network. -/
-- structure NodeLabelling (N : PortNumbered V) (out : Type*) :=
-- /-- The label associated to each node. -/
-- (labels : V → out)

-- namespace NodeLabelling

-- variable {X : Type*}

-- def encodeNodeLabelling (g : V → X) : NodeLabelling N X := ⟨g⟩
-- def encodeNodeSubset (X : Set V) : NodeLabelling N Prop := ⟨X⟩
-- def encodeEdgeLabelling (g : N.edgeSet → X) :
--     NodeLabelling N ((v : V) × (Fin (N.degree v) → X)) :=
--   { labels := fun v => ⟨v, fun i => g (N.edgeOfPort v i)⟩ }

-- end NodeLabelling

end PortNumbered

structure Problem (localOutput : Type*) :=
(valid : (V : Type*) → (N : PortNumbered V) → Set (V → localOutput))

def Problem.Conjunction (P Q : Problem α) : Problem α :=
  { valid := fun V N => P.valid V N ∩ Q.valid V N }

namespace Problem

def trivialInp : Problem PUnit := ⟨fun _ _ _ => true⟩

def Colouring (α : Type*) : Problem α where
  valid V N := {f | ∀ x y : V, N.Adj x y → f x ≠ f y}

lemma colouring_subtype_iff {α V : Type*} {N : PortNumbered V} (p : α → Prop)
    (f : V → {a // p a}) :
    f ∈ (Colouring {a // p a}).valid V N ↔ ((↑) ∘ f) ∈ (Colouring α).valid V N := by
  simp only [Colouring, Set.mem_setOf_eq, Function.comp_apply, ne_eq, Subtype.ext_iff]

end Problem

structure Algorithm (input states msg output : Type*) :=
(endState : states → Option output)
(init : ℕ → input → states)
(send (d : ℕ) : states → Fin d → msg)
(receive (d : ℕ) : (Fin d → msg) → (x : states) → (endState x).isNone → states)

namespace Algorithm

variable {I S M O : Type*} (A : Algorithm I S M O) (N : PortNumbered V)

def stoppingStates : Set S := {x : S | (A.endState x).isSome}

@[simp] lemma mem_stoppingStates {x : S} : x ∈ A.stoppingStates ↔ (A.endState x).isSome :=
  Iff.rfl

instance : DecidablePred (· ∈ A.stoppingStates) :=
  fun x => inferInstanceAs (Decidable (A.endState x).isSome)

lemma mem_stoppingStates' {x : S} : x ∈ A.stoppingStates ↔ ¬ (A.endState x).isNone := by
  rw [mem_stoppingStates, ←Bool.not_eq_false, ←Option.not_isSome]

lemma not_mem_stoppingStates {x : S} : x ∉ A.stoppingStates ↔ (A.endState x).isNone := by
  rw [mem_stoppingStates', not_not]

def initialVector (f : V → I) : V → S :=
  fun v => A.init (N.degree v) (f v)

def fullReceive (d : ℕ) (f : Fin d → M) (x : S) : S :=
  if h : (A.endState x).isNone then A.receive d f x h else x

lemma fullReceive_stoppingState {d : ℕ} {x : S} {f : Fin d → M}
    (hx : x ∈ A.stoppingStates) : A.fullReceive d f x = x :=
  dif_neg <| A.mem_stoppingStates'.1 hx

lemma fullReceive_not_stoppingState {d : ℕ} {x : S} {f : Fin d → M}
    (hx : x ∉ A.stoppingStates) :
    A.fullReceive d f x = A.receive d f x (A.not_mem_stoppingStates.1 hx) := dif_pos _

/-- messageRecd u i is the message *received* by node u on port i. -/
def messageRecd (curr : V → S) : (v : V) → Fin (N.degree v) → M :=
  fun u i => A.send _ (curr (N.ofPort u i)) (N.reversePort u i)

def nextVector (curr : V → S) : V → S :=
  fun v => A.fullReceive (N.degree v) (A.messageRecd N curr v) (curr v)

lemma nextVector_stopped (curr : V → S) {v : V} (h : curr v ∈ A.stoppingStates) :
    A.nextVector N curr v = curr v := by
  rw [nextVector, A.fullReceive_stoppingState h]

/-- When proving the state at v doesn't change, you can assume v is not currently stopped. -/
lemma nextVector_eq_self (curr : V → S)
    {v : V} (h : curr v ∉ A.stoppingStates → A.nextVector N curr v = curr v) :
    A.nextVector N curr v = curr v :=
  Classical.byCases (A.nextVector_stopped N curr) h

def isStopped (curr : V → S) : Prop := ∀ v, curr v ∈ A.stoppingStates

lemma nextVector_eq_of_isStopped (curr : V → S) (h : A.isStopped curr) :
    A.nextVector N curr = curr := funext fun v => nextVector_stopped _ _ _ (h v)

instance [Fintype V] (curr : V → S) : Decidable (A.isStopped curr) :=
  Fintype.decidableForallFintype

def getOutput (curr : V → S) (v : V) (hv : curr v ∈ A.stoppingStates) : O :=
  (A.endState (curr v)).get hv

/-- Given that the algorithm has stopped, extract the output from each node. -/
def outputs (curr : V → S) (h : A.isStopped curr) : V → O :=
  fun v => A.getOutput curr v (h v)

lemma nextVector_isStopped (curr : V → S) (h : A.isStopped curr) :
    A.isStopped (A.nextVector N curr) := by
  intro v
  specialize h v
  rwa [A.nextVector_stopped N _ h]

/--
Given an input vector, `rounds f n` gives the state of each node after n communication rounds.
-/
def rounds (f : V → I) : ℕ → V → S := fun T =>
  T.iterate (A.nextVector N) (A.initialVector N f)

lemma rounds_succ : A.rounds N f (T + 1) = A.nextVector N (A.rounds N f T) :=
  Function.iterate_succ_apply' _ _ _

lemma rounds_zero : A.rounds N f 0 = A.initialVector N f := rfl

/-- The condition that we stop within time t. -/
def stoppedBy (f : V → I) (t : ℕ) : Prop := A.isStopped (A.rounds N f t)

instance [Fintype V] : DecidablePred (A.stoppedBy N f) :=
  fun _ => inferInstanceAs (Decidable (A.isStopped _))

lemma rounds_eq_of_le_stoppedBy {f : V → I} {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂) (h : A.stoppedBy N f t₁) :
    A.rounds N f t₁ = A.rounds N f t₂ := by
  induction t₂, ht using Nat.le_induction
  case base => rfl
  case succ t₂ ht ih => rw [rounds_succ, ←ih, nextVector_eq_of_isStopped _ _ _ h]

/-- If we have stopped by time t, give the output at this time. -/
def outputAt (f : V → I) (t : ℕ) (h : A.stoppedBy N f t) : V → O := A.outputs _ h

/-- If we have stopped at time t₁ and time t₂, the output at those points is equal. -/
lemma outputAt_eq {f : V → I} {t₁ t₂ : ℕ} (h₁ : A.stoppedBy N f t₁) (h₂ : A.stoppedBy N f t₂) :
    A.outputAt N f t₁ h₁ = A.outputAt N f t₂ h₂ := by
  wlog h : t₁ ≤ t₂ generalizing t₁ t₂
  · rw [this h₂ h₁ (le_of_not_le h)]
  rw [outputAt, outputAt]
  simp only [stoppedBy] at h₁ h₂
  congr! 1
  rw [A.rounds_eq_of_le_stoppedBy N h h₁]

/-- The condition that we stop at all. -/
def stops (f : V → I) : Prop := ∃ t, A.stoppedBy N f t

lemma stoppedBy_monotone {f : V → I} : Monotone (A.stoppedBy N f) :=
  monotone_nat_of_le_succ fun n => by
  rw [stoppedBy, stoppedBy, rounds_succ]
  exact nextVector_isStopped _ _ _

/--
If the execution has stopped by time T₁, and T₁ ≤ T₂, then the execution has stopped by time
T₂ as well.
-/
lemma stoppedBy_mono {f : V → I} {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) :
    A.stoppedBy N f t₁ → A.stoppedBy N f t₂ :=
  A.stoppedBy_monotone N h

/--
If we know the execution of A stops on a finite network N (with input f), compute the round number
on which it stops.
This is computable (just run the algorithm!) but most likely won't be efficient.
-/
def firstStoppingTime [Fintype V] (h : A.stops N f) : ℕ := Nat.find h

noncomputable section

open scoped Classical
/--
Compute the stopping time of the algorithm A on a network N with input f. This definition does not
require N to be finite (and thus we can't decide whether the algorithm has stopped at a given point
in time - there are infinitely many states to check), or even for A to terminate on N.
In the non-terminating case, this returns the junk value 0.
-/
def stoppingTime (f : V → I) : ℕ :=
  if h : A.stops N f
    then Nat.find h
    else 0

end

/-- The algorithm which immediately stops. -/
def immediatelyStopping {I S M O : Type*} (f : S → O)
    (init : ℕ → I → S) (send : (d : ℕ) → S → Fin d → M) :
    Algorithm I S M O where
  endState x := some (f x)
  init := init
  send := send
  receive d _ _ hx := False.elim (by simp at hx)

/-- Every vector is stopped. -/
lemma immediatelyStopping_isStopped {f : S → O} {init : ℕ → I → S}
    {send : (d : ℕ) → S → Fin d → M} (curr : V → S) :
    (immediatelyStopping f init send).isStopped curr := fun _ => rfl

lemma immediatelyStopping_stoppedBy_zero {f : S → O} {init : ℕ → I → S}
    {send : (d : ℕ) → S → Fin d → M} {t : ℕ} :
    (immediatelyStopping f init send).stoppedBy N g t := immediatelyStopping_isStopped _

lemma immediatelyStopping_output {f : S → O} {init : ℕ → I → S}
    {send : (d : ℕ) → S → Fin d → M} (curr : V → S) :
    (immediatelyStopping f init send).outputs curr (immediatelyStopping_isStopped curr) =
      (f ∘ curr) := funext fun _ => rfl

@[simps init send receive]
def subtypeMk (I S M : Type*) (O : Set S) [DecidablePred (· ∈ O)]
    (init : ℕ → I → S) (send : (d : ℕ) → S → Fin d → M)
    (receive : (d : ℕ) → (Fin d → M) → (x : S) → x ∉ O → S) :
    Algorithm I S M O where
  endState := fun x => if hx : x ∈ O then some ⟨x, hx⟩ else none
  init := init
  send := send
  receive d f x hx := receive d f x <| by simpa [Option.isNone_iff_eq_none] using hx

@[simp] lemma subtypeMk_stoppingStates {O} [DecidablePred (· ∈ O)]
    {init send receive} :
    (subtypeMk I S M O init send receive).stoppingStates = O := by
  ext a
  simp [subtypeMk, ←Option.ne_none_iff_isSome]

lemma coe_subtypeMk_getOutput_apply {O} [DecidablePred (· ∈ O)]
    {init send receive} {f : V → S} {v : V} (hf : f v ∈ _) :
    ((subtypeMk I S M O init send receive).getOutput f v hf : S) = f v := by
  have : f v ∈ O := by simpa using hf
  simp [getOutput, subtypeMk, this]

lemma coe_subtypeMk_outputs_apply {O} [DecidablePred (· ∈ O)]
    {init send receive} {f : V → S} (hf) (v) :
    ((subtypeMk I S M O init send receive).outputs f hf v : S) = f v := by
  rw [outputs, coe_subtypeMk_getOutput_apply]

end Algorithm

-- Note the time function here *can* depend on the graph, but it doesn't have to. Indeed, this
-- definition is stronger if it doesn't.
def solvesProblemInTime (A : Algorithm I S M O) (Family : (V : Type u) → Set (SimpleGraph V))
    (inp : Problem I) (out : Problem O)
    (T : {V : Type u} → [Fintype V] → (G : SimpleGraph V) → ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] (N : PortNumbered V) (f : V → I),
    (N : SimpleGraph V) ∈ Family V →
    f ∈ inp.valid V N →
    ∃ (t : ℕ) (h : A.stoppedBy N f t),
      t ≤ T (N : SimpleGraph V) ∧
      A.outputs (A.rounds N f t) h ∈ out.valid V N

def solvesProblem (A : Algorithm I S M O) (Family : (V : Type u) → Set (SimpleGraph V))
    (inp : Problem I) (out : Problem O) : Prop :=
  ∀ {V : Type u} [Fintype V] (N : PortNumbered V) (f : V → I),
    (N : SimpleGraph V) ∈ Family V →
    f ∈ inp.valid V N →
    ∃ (t : ℕ) (h : A.stoppedBy N f t),
      A.outputs (A.rounds N f t) h ∈ out.valid V N

lemma solvesProblemInTime.solvesProblem (h : solvesProblemInTime A Family inp out T) :
    solvesProblem A Family inp out := by
  intro V _ N f hf hV
  obtain ⟨t, ht, -, ht'⟩ := h N f hf hV
  exact ⟨t, ht, ht'⟩

-- lemma simpleFunc_inp_solvesProblemInTime {I O : Type*} {f : I → O}
--     {Family : (V : Type u) → Set (SimpleGraph V)}
--     {inp : Problem I} {out : Problem O}
--     (hout : ∀ V N r, r ∈ inp.valid V N → f ∘ r ∈ out.valid V N):
--     solvesProblemInTime (Algorithm.simpleFuncInp I O f) Family inp out (fun _ => 0) := by
--   intro V _ N g hN hg
--   refine ⟨0, ?_, le_rfl, ?_⟩

/-- The family of (finite) path graphs. -/
def PathFamily (V : Type u) : Set (SimpleGraph V) := { G : SimpleGraph V | G.isPath }

def BipartiteFamily (V : Type u) : Set (SimpleGraph V) := { G : SimpleGraph V | G.Colorable 2 }
