import DGAlgorithms.PortNumbered

structure Algorithm (input states msg output : Type*) :=
(endState : states → Option output)
(init : ℕ → input → states)
(send (d : ℕ) : states → Fin d → msg)
(receive (d : ℕ) : (Fin d → msg) → (x : states) → (endState x).isNone → states)

namespace Algorithm

variable {V I S M O : Type*} (A : Algorithm I S M O) -- (N : PortNumbered V)

def stoppingStates : Set S := {x : S | (A.endState x).isSome}

@[simp] lemma mem_stoppingStates {x : S} : x ∈ A.stoppingStates ↔ (A.endState x).isSome :=
  Iff.rfl

instance : DecidablePred (· ∈ A.stoppingStates) :=
  fun x => inferInstanceAs (Decidable (A.endState x).isSome)

lemma mem_stoppingStates' {x : S} : x ∈ A.stoppingStates ↔ ¬ (A.endState x).isNone := by
  rw [mem_stoppingStates, ←Bool.not_eq_false, ←Option.not_isSome]

lemma not_mem_stoppingStates {x : S} : x ∉ A.stoppingStates ↔ (A.endState x).isNone := by
  rw [mem_stoppingStates', not_not]

def fullReceive (d : ℕ) (f : Fin d → M) (x : S) : S :=
  if h : (A.endState x).isNone then A.receive d f x h else x

lemma fullReceive_stoppingState {d : ℕ} {x : S} {f : Fin d → M} (hx : x ∈ A.stoppingStates) :
    A.fullReceive d f x = x :=
  dif_neg <| A.mem_stoppingStates'.1 hx

lemma fullReceive_not_stoppingState {d : ℕ} {x : S} {f : Fin d → M}
    (hx : x ∉ A.stoppingStates) :
    A.fullReceive d f x = A.receive d f x (A.not_mem_stoppingStates.1 hx) := dif_pos _

def isStopped (curr : V → S) : Prop := ∀ v, curr v ∈ A.stoppingStates

instance [Fintype V] (curr : V → S) : Decidable (A.isStopped curr) :=
  Fintype.decidableForallFintype

def getOutput (curr : V → S) (v : V) (hv : curr v ∈ A.stoppingStates) : O :=
  (A.endState (curr v)).get hv

/-- Given that the algorithm has stopped, extract the output from each node. -/
def outputs (curr : V → S) (h : A.isStopped curr) : V → O :=
  fun v => A.getOutput curr v (h v)

variable (N : NonSimplePortNumbered V) (f : V → I)

def initialVector : V → S := fun v => A.init (N.degree v) (f v)

/-- messageRecd u i is the message *received* by node u on port i. -/
def messageRecd (curr : V → S) : (v : V) → Fin (N.degree v) → M :=
  fun u i => A.send _ (curr (N.ofPort u i)) (N.reversePort u i)

def nextVector (curr : V → S) : V → S :=
  fun v => A.fullReceive (N.degree v) (A.messageRecd N curr v) (curr v)

lemma nextVector_stopped (curr : V → S) {v : V} (h : curr v ∈ A.stoppingStates) :
    A.nextVector N curr v = curr v := by
  rw [nextVector, A.fullReceive_stoppingState h]

lemma nextVector_mem_stoppingStates (curr : V → S) {v : V} (h : curr v ∈ A.stoppingStates) :
    A.nextVector N curr v ∈ A.stoppingStates := by rwa [nextVector_stopped _ _ _ h]

/-- When proving the state at v doesn't change, you can assume v is not currently stopped. -/
lemma nextVector_eq_self (curr : V → S)
    {v : V} (h : curr v ∉ A.stoppingStates → A.nextVector N curr v = curr v) :
    A.nextVector N curr v = curr v :=
  Classical.byCases (A.nextVector_stopped N curr) h

lemma nextVector_eq_of_isStopped (curr : V → S) (h : A.isStopped curr) :
    A.nextVector N curr = curr := funext fun v => nextVector_stopped _ _ _ (h v)

lemma nextVector_isStopped (curr : V → S) (h : A.isStopped curr) :
    A.isStopped (A.nextVector N curr) := fun v => nextVector_mem_stoppingStates _ _ _ (h v)

/--
Given an input vector, `rounds f n` gives the state of each node after n communication rounds.
-/
def rounds : ℕ → V → S := fun T =>
  T.iterate (A.nextVector N) (A.initialVector N f)

lemma rounds_succ : A.rounds N f (T + 1) = A.nextVector N (A.rounds N f T) :=
  Function.iterate_succ_apply' _ _ _

lemma rounds_zero : A.rounds N f 0 = A.initialVector N f := rfl

lemma rounds_eq_of_mem_stoppingStates {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂) (v : V)
    (h : A.rounds N f t₁ v ∈ A.stoppingStates) :
    A.rounds N f t₁ v = A.rounds N f t₂ v := by
  induction t₂, ht using Nat.le_induction
  case base => rfl
  case succ t₂ ht ih =>
    rw [rounds_succ]
    rw [ih, nextVector_stopped]
    rwa [←ih]

lemma rounds_mem_stoppingStates {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂) (v : V)
    (h : A.rounds N f t₁ v ∈ A.stoppingStates) :
    A.rounds N f t₂ v ∈ A.stoppingStates := by
  rwa [←rounds_eq_of_mem_stoppingStates A N f ht _ h]

/-- The condition that we stop within time t. -/
def stoppedBy (t : ℕ) : Prop := A.isStopped (A.rounds N f t)

instance [Fintype V] : DecidablePred (A.stoppedBy N f) :=
  fun _ => inferInstanceAs (Decidable (A.isStopped _))

lemma rounds_eq_of_le_stoppedBy {f : V → I} {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂) (h : A.stoppedBy N f t₁) :
    A.rounds N f t₁ = A.rounds N f t₂ :=
  funext fun v => rounds_eq_of_mem_stoppingStates A N f ht _ (h v)

/-- If we have stopped by time t, give the output at this time. -/
def outputAt (t : ℕ) (h : A.stoppedBy N f t) : V → O := A.outputs (A.rounds N f t) h

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
def stops : Prop := ∃ t, A.stoppedBy N f t

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
def stoppingTime : ℕ :=
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

/--
We say algorithm A solves problem `out` on graph family `family` given `inp` in time `T` if for
every graph in the family, every port numbering that induces that graph, and every valid input,
the algorithm stops in time at most `T` and outputs a valid output.

Note the time function here *can* depend on the graph, but it doesn't have to. Indeed, this
definition is stronger if it doesn't.
Note that we quantify over *all* port numberings. Indeed the algorithm may give different outputs
for the same input and underlying graph if the port numbering is different, but the outputs must
be valid in all cases.
-/
def solvesProblemInTime (A : Algorithm I S M O) (family : (V : Type u) → Set (SimpleGraph V))
    (inp : Problem I) (out : Problem O)
    (T : {V : Type u} → [Fintype V] → (G : SimpleGraph V) → ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] (N : PortNumbered V) (f : V → I),
    (N : SimpleGraph V) ∈ family V →
    f ∈ inp.valid V N →
    ∃ (t : ℕ) (h : A.stoppedBy N f t),
      t ≤ T (N : SimpleGraph V) ∧
      A.outputAt N f t h ∈ out.valid V N

/--
We say algorithm A solves problem `out` on graph family `family` given `inp` if for
every graph in the family, every port numbering that induces that graph, and every valid input,
the algorithm stops and outputs a valid output.

Note that we quantify over *all* port numberings. Indeed the algorithm may give different outputs
for the same input and underlying graph if the port numbering is different, but the outputs must
be valid in all cases.
-/
def solvesProblem (A : Algorithm I S M O) (family : (V : Type u) → Set (SimpleGraph V))
    (inp : Problem I) (out : Problem O) : Prop :=
  ∀ {V : Type u} [Fintype V] (N : PortNumbered V) (f : V → I),
    (N : SimpleGraph V) ∈ family V →
    f ∈ inp.valid V N →
    ∃ (t : ℕ) (h : A.stoppedBy N f t),
      A.outputAt N f t h ∈ out.valid V N

lemma solvesProblemInTime.solvesProblem (h : solvesProblemInTime A family inp out T) :
    solvesProblem A family inp out := by
  intro V _ N f hf hV
  obtain ⟨t, ht, -, ht'⟩ := h N f hf hV
  exact ⟨t, ht, ht'⟩
