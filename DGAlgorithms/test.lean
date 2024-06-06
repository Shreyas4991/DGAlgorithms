import Mathlib.Data.Finset.Sort

import DGAlgorithms.ForMathlib.SimpleGraph
import DGAlgorithms.PN

section sec_3_4

namespace ThreeColourPath

def smallestMissing (X : Finset ℕ) : ℕ := Nat.find X.exists_not_mem
lemma smallestMissing_spec (X : Finset ℕ) : smallestMissing X ∉ X := Nat.find_spec X.exists_not_mem
lemma smallestMissing_min' (X : Finset ℕ) {x : ℕ} (hx : x ∉ X) : smallestMissing X ≤ x :=
  Nat.find_min' X.exists_not_mem hx
lemma smallestMissing_min (X : Finset ℕ) {x : ℕ} (hx : x < smallestMissing X) : x ∈ X := by
  simpa using Nat.find_min X.exists_not_mem hx

lemma smallestMissing_le_card {X : Finset ℕ} : smallestMissing X ≤ X.card := by
  by_contra!
  have hX : ∀ i ≤ X.card, i ∈ X := fun i hi => smallestMissing_min _ (by omega)
  have : Finset.range (X.card + 1) ⊆ X := fun i hi => hX _ (Finset.mem_range_succ_iff.1 hi)
  simpa using Finset.card_le_card this

@[simps!]
def colouringPathAlgorithm : Algorithm ℕ ℕ ℕ ({0, 1, 2} : Finset ℕ) :=
  Algorithm.subtypeMk ℕ ℕ ℕ
    ({0, 1, 2} : Finset ℕ)
    (fun _ x => x)
    (fun _ x _ => x) <| fun d f x _ =>
      if ∀ i : Fin d, f i < x -- if x is a local maximum
        then smallestMissing (Finset.univ.image f) -- then pick the smallest colour not used by any neighbour
        else x -- otherwise no change

theorem max'_image_eq_sup' {α β : Type*} [LinearOrder β]
    {s : Finset α} {f : α → β} (hs : s.Nonempty) :
    (s.image f).max' (hs.image f) = s.sup' hs f := by
  rw [Finset.max'_eq_sup', ←Finset.sup'_comp_eq_image hs]
  rfl

lemma max_image_eq_sup {α β : Type*} [LinearOrder β] {s : Finset α} {f : α → β} :
    (s.image f).max = s.sup ((↑) ∘ f) :=
  s.sup_image f _

lemma max_image_unbot_eq_sup {α β : Type*} [LinearOrder β] [OrderBot β] {s : Finset α} {f : α → β} :
    (s.image f).max.unbot' ⊥ = s.sup f := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  rw [max_image_eq_sup, ←Finset.coe_sup' hs, WithBot.unbot'_coe, Finset.sup'_eq_sup]

def maxColour [Fintype V] (f : V → ℕ) : ℕ := Finset.univ.sup f

lemma maxColour_le_iff [Fintype V] (f : V → ℕ) (x : ℕ) :
    maxColour f ≤ x ↔ ∀ v, f v ≤ x := by
  rw [maxColour]
  simp

lemma le_maxColour [Fintype V] (f : V → ℕ) (x : V) :
    f x ≤ maxColour f := Finset.le_sup (by simp)

lemma stoppingStates : colouringPathAlgorithm.stoppingStates = ({0, 1, 2} : Finset ℕ) :=
  Algorithm.subtypeMk_stoppingStates

lemma initialVector (f : V → ℕ) : colouringPathAlgorithm.initialVector N f = f := rfl

lemma coe_outputs_apply (curr : V → ℕ) (h : colouringPathAlgorithm.isStopped curr) (v : V) :
    (colouringPathAlgorithm.outputs curr h v : ℕ) = curr v :=
  Algorithm.coe_subtypeMk_outputs_apply _ _

lemma coe_comp_outputs_apply (curr : V → ℕ) (h : colouringPathAlgorithm.isStopped curr) :
    Subtype.val ∘ colouringPathAlgorithm.outputs curr h = curr :=
  funext (coe_outputs_apply _ _)

lemma messageRecd (curr : V → ℕ) (v : V) (i : Fin (N.degree v)) :
    colouringPathAlgorithm.messageRecd N curr v i = curr (N.ofPort v i) := rfl

-- the collection of received messages is the set of colours of the neighbours
lemma image_messageRecd (curr : V → ℕ) (v : V) :
    (Finset.univ.image (colouringPathAlgorithm.messageRecd N curr v)) =
      (N.neighborFinset v).image curr := by
  ext i
  simp only [Finset.mem_image, Finset.mem_univ, true_and, messageRecd, PortNumbered.ofPort]
  rw [←Equiv.exists_congr_left (N.numbering v) (p := fun a => curr a = i)]
  simp

lemma nextVector_of_stopped (curr : V → ℕ) (v : V)
    (h : curr v ∈ colouringPathAlgorithm.stoppingStates) :
    colouringPathAlgorithm.nextVector N curr v = curr v :=
  Algorithm.nextVector_stopped _ _ _ h

-- in practice we know curr v ≠ curr w, but the proof works in the more general case too
lemma nextVector_of_not_local_max (curr : V → ℕ) (v w : V) (h₁ : N.Adj v w)
    (h₂ : curr v ≤ curr w) : colouringPathAlgorithm.nextVector N curr v = curr v := by
  refine Algorithm.nextVector_eq_self _ _ _ ?_
  intro h₃
  rw [Algorithm.nextVector, Algorithm.fullReceive_not_stoppingState _ h₃,
    colouringPathAlgorithm_receive, if_neg]
  simp only [not_forall, not_lt]
  refine ⟨N.toPort v w h₁, ?_⟩
  rwa [messageRecd, N.ofPort_toPort]

lemma nextVector_of_local_max (curr : V → ℕ) (v : V)
    (h₁ : curr v ∉ colouringPathAlgorithm.stoppingStates)
    (h₂ : ∀ w, N.Adj v w → curr w < curr v) :
    colouringPathAlgorithm.nextVector N curr v =
      smallestMissing ((N.neighborFinset v).image curr) := by
  rw [Algorithm.nextVector, Algorithm.fullReceive_not_stoppingState _ h₁,
    colouringPathAlgorithm_receive, if_pos, image_messageRecd curr]
  simpa [N.forall_ports, messageRecd]

lemma mem_stoppingStates_iff_le {v : ℕ} :
    v ∈ colouringPathAlgorithm.stoppingStates ↔ v ≤ 2 := by
  simp only [stoppingStates, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · aesop
  · intro h
    interval_cases v <;> simp

lemma isStopped_iff_maxColour_le [Fintype V] {curr : V → ℕ} :
    colouringPathAlgorithm.isStopped curr ↔ maxColour curr ≤ 2 := by
  simp only [Algorithm.isStopped, mem_stoppingStates_iff_le, maxColour, Finset.sup_le_iff,
    Finset.mem_univ, true_implies]

lemma nextVector_lt_of_local_max (curr : V → ℕ) (v : V) (hv : N.degree v ≤ 2)
    (h₁ : curr v ∉ colouringPathAlgorithm.stoppingStates)
    (h₂ : ∀ w, N.Adj v w → curr w < curr v) :
    colouringPathAlgorithm.nextVector N curr v < curr v := by
  rw [nextVector_of_local_max _ _ h₁ h₂]
  set M := (N.neighborFinset v).image curr
  have hM : M.card ≤ 2 := Finset.card_image_le.trans hv
  have : smallestMissing M ≤ 2 := smallestMissing_le_card.trans hM
  rw [mem_stoppingStates_iff_le, not_le] at h₁
  omega

lemma validColouring_aux (curr : V → ℕ) (v w : V) (h : N.Adj v w)
    (h₁ : curr v ∉ colouringPathAlgorithm.stoppingStates)
    (h₂ : ∀ w, N.Adj v w → curr w < curr v) :
    colouringPathAlgorithm.nextVector N curr v ≠ curr w := by
  intro h₃
  have h₄ := smallestMissing_spec ((N.neighborFinset v).image curr)
  rw [←nextVector_of_local_max curr v h₁ h₂, h₃] at h₄
  refine h₄ ?_
  simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset]
  exact ⟨w, h, rfl⟩

lemma validColouring (curr : V → ℕ) (v w : V) (h₁ : N.Adj v w) (h₂ : curr v ≠ curr w) :
    colouringPathAlgorithm.nextVector N curr v ≠ colouringPathAlgorithm.nextVector N curr w := by
  wlog h₄ : curr w < curr v generalizing v w
  · exact (this _ _ h₁.symm h₂.symm (lt_of_le_of_ne (le_of_not_lt h₄) h₂)).symm
  intro h₃
  rw [nextVector_of_not_local_max _ _ _ h₁.symm h₄.le] at h₃
  have h₅ : curr v ∉ colouringPathAlgorithm.stoppingStates := by
    contrapose! h₂
    rw [←h₃, nextVector_of_stopped _ _ h₂]
  have h₆ : ∀ w, N.Adj v w → curr w < curr v := by
    contrapose! h₂
    obtain ⟨x, h₆, h₇⟩ := h₂
    rw [←h₃, nextVector_of_not_local_max curr v x h₆ h₇]
  exact validColouring_aux curr v w h₁ h₅ h₆ h₃

lemma validColouring' (curr : V → ℕ) (h : curr ∈ (Problem.Colouring _).valid V N) :
    colouringPathAlgorithm.nextVector N curr ∈ (Problem.Colouring _).valid V N :=
  fun _ _ h' => validColouring _ _ _ h' (h _ _ h')

lemma colour_decreases (N : PortNumbered V) (curr : V → ℕ) (v : V) (hv : N.degree v ≤ 2) :
    colouringPathAlgorithm.nextVector N curr v ≤ curr v := by
  by_contra! h₁
  have h₂ : curr v ∉ colouringPathAlgorithm.stoppingStates := by
    intro h₂
    rw [nextVector_of_stopped _ _ h₂] at h₁
    exact lt_irrefl _ h₁
  have h₃ : ∀ w, N.Adj v w → curr w < curr v := by
    intro w h
    by_contra! h₃
    rw [nextVector_of_not_local_max curr _ _ h h₃] at h₁
    exact lt_irrefl _ h₁
  exact h₁.not_lt (nextVector_lt_of_local_max _ _ hv h₂ h₃)

lemma maxColour_decreases [Fintype V] (N : PortNumbered V) [DecidableRel N.Adj] (curr : V → ℕ)
    (h : N.maxDegree ≤ 2) :
    maxColour (colouringPathAlgorithm.nextVector N curr) ≤ maxColour curr := by
  refine Finset.sup_mono_fun ?_
  simp only [Finset.mem_univ, true_implies]
  intro v
  refine colour_decreases _ _ _ ?_
  convert (N.degree_le_maxDegree v).trans h

lemma maxColour_strict_decreases [Fintype V] (N : PortNumbered V) [DecidableRel N.Adj]
    (curr : V → ℕ) (h : N.maxDegree ≤ 2)
    (h₁ : curr ∈ (Problem.Colouring _).valid V N)
    (h₂ : ¬ colouringPathAlgorithm.isStopped curr) :
    maxColour (colouringPathAlgorithm.nextVector N curr) < maxColour curr := by
  rw [isStopped_iff_maxColour_le, not_le] at h₂
  have h₄ : ∀ x : V, curr x = maxColour curr →
      colouringPathAlgorithm.nextVector N curr x < curr x := by
    intro x hx
    have : ∀ y : V, N.Adj x y → curr y < curr x := by
      intro y h₃
      refine lt_of_le_of_ne ?_ (h₁ x y h₃).symm
      rw [hx]
      exact le_maxColour _ _
    refine nextVector_lt_of_local_max _ _ ?_ ?_ this
    · convert (N.degree_le_maxDegree _).trans ?_
      exact h
    · rwa [mem_stoppingStates_iff_le, not_le, hx]
  rw [maxColour, Finset.sup_lt_iff]
  rintro x -
  swap
  · simp only [bot_eq_zero']
    omega
  refine lt_of_le_of_ne ?_ ?_
  · exact (maxColour_decreases N _ h).trans' (le_maxColour _ _)
  intro h₅
  have h₆ : curr x = maxColour curr := by
    have := colour_decreases N curr x ?_
    · have : curr x ≤ maxColour curr := le_maxColour _ _
      omega
    convert (N.degree_le_maxDegree _).trans ?_
    exact h
  have := h₄ x h₆
  omega

lemma all_valid (N : PortNumbered V) (f : V → ℕ)
    (hf : f ∈ (Problem.Colouring _).valid V N) (T : ℕ) :
    colouringPathAlgorithm.rounds N f T ∈ (Problem.Colouring ℕ).valid V N := by
  induction T with
  | zero => exact hf
  | succ T ih =>
      rw [Algorithm.rounds_succ]
      refine validColouring' _ ih

lemma maxColour_rounds [Fintype V] [DecidableRel N.Adj] (h : N.maxDegree ≤ 2)
    (f : V → ℕ) (hf : f ∈ (Problem.Colouring _).valid V N) (T : ℕ)
    (hf' : ¬ colouringPathAlgorithm.isStopped (colouringPathAlgorithm.rounds N f T)) :
    maxColour (colouringPathAlgorithm.rounds N f T) + T ≤ maxColour f := by
  induction T with
  | zero => rw [Algorithm.rounds_zero, initialVector, add_zero]
  | succ T ih =>
      have : ¬ colouringPathAlgorithm.isStopped (colouringPathAlgorithm.rounds N f T) := by
        contrapose! hf'
        rw [Algorithm.rounds_succ]
        exact Algorithm.nextVector_isStopped _ N _ hf'
      refine (ih this).trans' ?_
      rw [←add_assoc, add_right_comm, add_le_add_iff_right, Nat.add_one_le_iff,
        Algorithm.rounds_succ]
      exact maxColour_strict_decreases _ _ h (all_valid _ _ hf _) this

lemma stops [Fintype V] [DecidableRel N.Adj] (f : V → ℕ)
    (hf : f ∈ (Problem.Colouring ℕ).valid V N) (hd : N.maxDegree ≤ 2)
    (x : ℕ) (hx : maxColour f ≤ x) :
    colouringPathAlgorithm.stoppedBy N f (x - 2) := by
  rcases le_or_lt x 2 with h | h
  · rw [tsub_eq_zero_of_le h, Algorithm.stoppedBy, Algorithm.rounds_zero, initialVector,
      isStopped_iff_maxColour_le]
    omega
  rw [Algorithm.stoppedBy]
  by_contra! h'
  have := maxColour_rounds hd _ hf _ h'
  rw [isStopped_iff_maxColour_le, not_le] at h'
  omega

/-- The basic colouring path algorithm computes a 3-colouring on paths. -/
lemma solvesColouringProblem :
    solvesProblem colouringPathAlgorithm PathFamily
      (Problem.Colouring ℕ)
      (Problem.Colouring ({0, 1, 2} : Finset ℕ)) := by
  rintro V _ N f hN hf
  classical
  refine ⟨maxColour f - 2, stops f hf hN.maxDegree (maxColour f) le_rfl, ?_⟩
  rw [Problem.colouring_subtype_iff, coe_comp_outputs_apply]
  exact all_valid _ _ hf _

end ThreeColourPath

end sec_3_4

section sec_3_5

set_option autoImplicit false

namespace MaximalBipartiteMatching

/--
The problem of returning a subset of the edges. Essentially this ensures that the encoding returned
by the algorithm does indeed encode a subset of the edges.

Most useful as a building block problem.
 -/
def EdgeSubset : Problem (Set ℕ) where
  valid V N f :=
    ∀ v : V,
      -- each edge label is a valid port number
      (∀ i, i ∈ f v → i < N.degree v) ∧
      -- edges are symmetric
      (∀ i : Fin (N.degree v),
        (i : ℕ) ∈ f v ↔ (N.reversePort v i : ℕ) ∈ f (N.ofPort v i))

/--
Option ℕ encodes a matching on a PN network: none means no edge, some n means edge to the nth port.
-/
def Matching : Problem (Option ℕ) where
  valid V N f := EdgeSubset.1 V N fun v => (f v).getM

def MaximalMatching : Problem (Option ℕ) where
  valid V N f := Matching.1 V N f ∧
    ∀ v : V, f v = none → -- for every unmatched node
      ∀ i : Fin (N.degree v), -- and every outward port
        f (N.ofPort v i) ≠ none -- the corresponding node is matched

inductive EdgeState where
  | UR
  | MR : ℕ → EdgeState
  | US
  | MS : ℕ → EdgeState
  deriving Repr

inductive ColourState where
  | white : ColourState
  | black : Finset ℕ → Finset ℕ → ColourState

inductive Msg where | Accept | Matched | Proposal | Empty deriving DecidableEq, Repr

def State := ℕ × ColourState × EdgeState

@[simp]
def asOne {I S M O : Type*} (init : ℕ → I → S) (endState : S → Option O)
    (operate : (d : ℕ) → (s : S) → (Fin d → M) × ((Fin d → M) → (endState s).isNone → S)) :
    Algorithm I S M O where
  send := fun d x i => (operate d x).1 i
  receive := fun d f x => (operate d x).2 f
  init := init
  endState := endState

-- input says if the note is black
@[simps!] def maximalMatching : Algorithm Bool State Msg (Option ℕ) :=
  asOne
    (fun d => fun
      | true => (0, .black ∅ (Finset.range d), .UR)
      | false => (0, .white, .UR))
    (fun
      | (_, _, .UR) => none
      | (_, _, .MR _) => none
      | (_, _, .US) => some none
      | (_, _, .MS i) => some (some i))
    fun d rcs =>
      if Even rcs.1
        then
          match rcs.2.1, rcs.2.2 with
            | .white, .UR =>
                if h : rcs.1 / 2 < d
                  then (fun i => if i = ⟨_, h⟩ then .Proposal else .Empty,
                        fun _ _ => (rcs.1 + 1, .white, .UR))
                  else (fun _ => .Empty, fun _ _ => (rcs.1 + 1, .white, .US))
            | .white, .MR i =>
                  (fun _ => .Matched, fun _ _ => (rcs.1 + 1, .white, .MS i))
            | .black M X, .UR => (fun _ => .Empty,
                fun f _ =>
                  let M_add := (Finset.univ.filter (f · = .Proposal)).map Fin.valEmbedding
                  let X_remove := (Finset.univ.filter (f · = .Matched)).map Fin.valEmbedding
                  (rcs.1 + 1, .black (M ∪ M_add) (X \ X_remove), .UR))
            | c, s => ⟨fun _ => .Empty, fun _ _ => (rcs.1 + 1, c, s)⟩
        else
          match rcs.2.1, rcs.2.2 with
            | .white, .UR => (fun _ => .Empty, fun f _ =>
                if h : (Finset.univ.filter (f · = .Accept)).Nonempty
                  then ⟨rcs.1 + 1, .white, .MR (Finset.min' _ h : Fin d)⟩
                  else ⟨rcs.1 + 1, .white, .UR⟩)
            | .black M X, .UR =>
                if h : M.Nonempty
                  then
                    let i := Finset.min' M h
                    (fun j => if j = i then .Accept else .Empty,
                     fun _ _ => (rcs.1 + 1, .black M X, .MS i))
                  else (fun _ => .Empty,
                        fun _ _ => (rcs.1 + 1, .black M X, if X = ∅ then .US else .UR))
            | c, s => (fun _ => .Empty, fun _ _ => (rcs.1 + 1, c, s))

variable {V : Type*} (N : PortNumbered V)

lemma initialVector (f : V → Bool) (v : V) :
    maximalMatching.initialVector N f v =
      cond (f v) (0, .black ∅ (Finset.range (N.degree v)), .UR) (0, .white, .UR) := rfl

lemma initialVector' (f : V → Bool) (v : V) :
    maximalMatching.initialVector N f v =
      (0, cond (f v) (.black ∅ (Finset.range (N.degree v))) .white, .UR) := by
  rw [initialVector]
  match f v with
  | true => rfl
  | false => rfl

private lemma mem_stoppingStates_iff_left :
    ∀ s : State, s ∈ maximalMatching.stoppingStates → s.2.2 = .US ∨ ∃ i, s.2.2 = .MS i
  | (_, _, .US), _ => Or.inl rfl
  | (_, _, .MS i), _ => Or.inr ⟨i, rfl⟩

private lemma mem_stoppingStates_iff_right :
    ∀ s : State, (s.2.2 = .US ∨ ∃ i, s.2.2 = .MS i) → s ∈ maximalMatching.stoppingStates
  | (_, _, .US), _ => by simp
  | (_, _, .MS i), _ => by simp

lemma mem_stoppingStates_iff (s : State) :
      s ∈ maximalMatching.stoppingStates ↔ s.2.2 = EdgeState.US ∨ ∃ i, s.2.2 = EdgeState.MS i :=
  ⟨mem_stoppingStates_iff_left _, mem_stoppingStates_iff_right _⟩

lemma nextVector_fst {curr next : V → State} (v : V)
    (hnext : next = maximalMatching.nextVector N curr)
    (h : next v ∉ maximalMatching.stoppingStates) :
    (next v).1 = (curr v).1 + 1 := by
  subst hnext
  have hcurr : curr v ∉ maximalMatching.stoppingStates := by
    contrapose! h
    rwa [Algorithm.nextVector_stopped _ _ _ h]
  rw [Algorithm.nextVector, Algorithm.fullReceive_not_stoppingState _ hcurr,
    maximalMatching_receive]
  aesop -- this aesop is doing a lot of work!

/--
As long as we haven't hit a stopped state, the round count is correct.
(Once the node stops, the round count is not updated and will become out of date.)
-/
lemma maximalMatching_round_count (f : V → Bool) (t : ℕ) (v : V)
    (h : maximalMatching.rounds N f t v ∉ maximalMatching.stoppingStates) :
    (maximalMatching.rounds N f t v).1 = t := by
  induction t with
  | zero => rw [Algorithm.rounds_zero, initialVector']
  | succ t ih =>
      rw [nextVector_fst N v (Algorithm.rounds_succ _ _) h, ih]
      contrapose! h
      rwa [Algorithm.rounds_succ, Algorithm.nextVector_stopped _ _ _ h]

lemma nextVector_snd_fst_white (curr next : V → State) (v : V)
    (hnext : next = maximalMatching.nextVector N curr)
    (h : (curr v).2.1 = .white) :
    (next v).2.1 = .white := by
  subst hnext
  by_cases h' : curr v ∈ maximalMatching.stoppingStates
  · rw [Algorithm.nextVector, Algorithm.fullReceive_stoppingState _ h', h]
  rw [Algorithm.nextVector, Algorithm.fullReceive_not_stoppingState _ h', maximalMatching_receive]
  aesop

lemma nextVector_snd_fst_black (curr next : V → State) (v : V) (M X : Finset ℕ)
    (hnext : next = maximalMatching.nextVector N curr)
    (h : (curr v).2.1 = .black M X) :
    ∃ M' X', (next v).2.1 = .black M' X' := by
  subst hnext
  by_cases h' : curr v ∈ maximalMatching.stoppingStates
  · rw [Algorithm.nextVector, Algorithm.fullReceive_stoppingState _ h', h]
    simp
  rw [Algorithm.nextVector, Algorithm.fullReceive_not_stoppingState _ h', maximalMatching_receive]
  aesop

lemma remains_white (f : V → Bool) (t : ℕ) (v : V) (h : f v = false) :
    (maximalMatching.rounds N f t v).2.1 = .white := by
  induction t with
  | zero => rw [Algorithm.rounds_zero, initialVector', h, cond_false]
  | succ t ih => exact nextVector_snd_fst_white N _ _ _ (Algorithm.rounds_succ _ _) ih

lemma remains_black (f : V → Bool) (t : ℕ) (v : V) (h : f v = true) :
    ∃ M X, (maximalMatching.rounds N f t v).2.1 = .black M X := by
  induction t with
  | zero =>
      refine ⟨∅, Finset.range (N.degree v), ?_⟩
      rw [Algorithm.rounds_zero, initialVector', h, cond_true]
  | succ t ih =>
      obtain ⟨M, X, ih⟩ := ih
      exact nextVector_snd_fst_black N _ _ _ M X (Algorithm.rounds_succ _ _) ih

lemma next_monotonicity (curr next : V → State) (v : V) (M X : Finset ℕ)
    (hnext : next = maximalMatching.nextVector N curr)
    (hv_col : (curr v).2.1 = .black M X) :
    ∃ M' X', (next v).2.1 = .black M' X' ∧ M ⊆ M' ∧ X' ⊆ X := by
  subst hnext
  by_cases h' : curr v ∈ maximalMatching.stoppingStates
  · rw [Algorithm.nextVector, Algorithm.fullReceive_stoppingState _ h']
    exact ⟨_, _, hv_col, Finset.Subset.refl _, Finset.Subset.refl _⟩
  rw [Algorithm.nextVector, Algorithm.fullReceive_not_stoppingState _ h', maximalMatching_receive]
  rw [hv_col]
  split
  case neg.inr => use M, X; aesop
  case neg.inl =>
    split
    case h_1 hc _ => tauto
    case h_2 hc _ => tauto
    case h_3 hc _ =>
      cases hc
      exact ⟨_, _, rfl, Finset.subset_union_left _ _, Finset.sdiff_subset _ _⟩
    case h_4 => use M, X

lemma sets_changing (f : V → Bool) (t₁ t₂ : ℕ) (ht : t₁ ≤ t₂) (v : V) (M X : Finset ℕ)
    (h : (maximalMatching.rounds N f t₁ v).2.1 = .black M X) :
    ∃ M' X', (maximalMatching.rounds N f t₂ v).2.1 = .black M' X' ∧ M ⊆ M' ∧ X' ⊆ X := by
  induction t₂, ht using Nat.le_induction
  case base => use M, X
  case succ t₂ _ ih =>
    obtain ⟨M, X, h, hM, hX⟩ := ih
    obtain ⟨M', X', h', hM', hX'⟩ := next_monotonicity N _ _ v M X (Algorithm.rounds_succ _ _) h
    use M', X', h'
    exact ⟨hM.trans hM', hX'.trans hX⟩

section eg

def exampleGraph_adj : Fin 2 × Fin 4 → Fin 2 × Fin 4 → Prop
  | ⟨0, 0⟩, i => i = (1, 0) ∨ i = (1, 2)
  | ⟨0, 1⟩, i => i = (1, 0) ∨ i = (1, 1) ∨ i = (1, 3)
  | ⟨0, 2⟩, i => i = (1, 2)
  | ⟨0, 3⟩, i => i = (1, 2) ∨ i = (1, 3)
  | ⟨1, 0⟩, i => i = (0, 0) ∨ i = (0, 1)
  | ⟨1, 1⟩, i => i = (0, 1)
  | ⟨1, 2⟩, i => i = (0, 0) ∨ i = (0, 2) ∨ i = (0, 3)
  | ⟨1, 3⟩, i => i = (0, 1) ∨ i = (0, 3)

instance : DecidableRel exampleGraph_adj
  | ⟨0, 0⟩, _ => inferInstanceAs (Decidable (_ ∨ _))
  | ⟨0, 1⟩, _ => inferInstanceAs (Decidable (_ ∨ _))
  | ⟨0, 2⟩, _ => inferInstanceAs (Decidable (_ = _))
  | ⟨0, 3⟩, _ => inferInstanceAs (Decidable (_ ∨ _))
  | ⟨1, 0⟩, _ => inferInstanceAs (Decidable (_ ∨ _))
  | ⟨1, 1⟩, _ => inferInstanceAs (Decidable (_ = _))
  | ⟨1, 2⟩, _ => inferInstanceAs (Decidable (_ ∨ _))
  | ⟨1, 3⟩, _ => inferInstanceAs (Decidable (_ ∨ _))

def bij_to_equiv {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (f : α → β)
    (h : Function.Bijective f) : α ≃ β where
  toFun := f
  invFun := fun b => Finset.univ.choose _ <| by simpa using h.existsUnique b
  left_inv := by
    intro a
    exact h.injective (Finset.choose_property (fun b => f b = f a) _ _)
  right_inv := fun b => Finset.choose_property (fun a => f a = b) Finset.univ _

-- def numbering (v : Fin 2 × Fin 4) :

def exampleGraph : SimpleGraph (Fin 2 × Fin 4) where
  Adj := exampleGraph_adj
  symm := by rw [Symmetric]; decide
  loopless := by rw [Irreflexive]; decide

instance : DecidableRel exampleGraph.Adj := inferInstanceAs (DecidableRel exampleGraph_adj)

def exampleNumbering : (v : Fin 2 × Fin 4) →
    exampleGraph.neighborSet v ≃ Fin (exampleGraph.degree v)
  | ⟨0, 0⟩ => Equiv.symm <| bij_to_equiv
                (![⟨(1, 0), by decide⟩, ⟨(1, 2), by decide⟩]) (by decide)
  | ⟨0, 1⟩ => Equiv.symm <| bij_to_equiv
                (![⟨(1, 0), by decide⟩, ⟨(1, 1), by decide⟩, ⟨(1, 3), by decide⟩]) (by decide)
  | ⟨0, 2⟩ => Equiv.symm <| bij_to_equiv
                (![⟨(1, 2), by decide⟩]) (by decide)
  | ⟨0, 3⟩ => Equiv.symm <| bij_to_equiv
                (![⟨(1, 2), by decide⟩, ⟨(1, 3), by decide⟩]) (by decide)
  | ⟨1, 0⟩ => Equiv.symm <| bij_to_equiv
                (![⟨(0, 1), by decide⟩, ⟨(0, 0), by decide⟩]) (by decide)
  | ⟨1, 1⟩ => Equiv.symm <| bij_to_equiv
                (![⟨(0, 1), by decide⟩]) (by decide)
  | ⟨1, 2⟩ => Equiv.symm <| bij_to_equiv
                (![⟨(0, 0), by decide⟩, ⟨(0, 2), by decide⟩, ⟨(0, 3), by decide⟩]) (by decide)
  | ⟨1, 3⟩ => Equiv.symm <| bij_to_equiv
                (![⟨(0, 1), by decide⟩, ⟨(0, 3), by decide⟩]) (by decide)

def exampleNetwork : PortNumbered (Fin 2 × Fin 4) where
  toSimpleGraph := exampleGraph
  numbering := exampleNumbering

def test : ℕ → Fin 2 × Fin 4 → State :=
  maximalMatching.rounds exampleNetwork (fun x => x.1 = 1)

def showEdgeState : EdgeState → Lean.Format
  | .UR => "UR"
  | .US => "US"
  | .MR i => "MR " ++ repr i
  | .MS i => "MS " ++ repr i

def showState : State → Lean.Format
  | ⟨r, .white, s⟩ => repr r ++ " white " ++ showEdgeState s
  | ⟨r, .black M X, s⟩ => repr r ++ " black M=" ++ repr (M.sort (· ≤ ·)) ++ " W=" ++ repr (X.sort (· ≤ ·)) ++ " " ++ showEdgeState s

def allVerts : List (Fin 2 × Fin 4) :=
  [⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 3⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 3⟩]

#check Complex.log

#eval showState <| test 0 <| ⟨0, 0⟩
#eval showState <| test 1 <| ⟨0, 0⟩
#eval showState <| test 2 <| ⟨0, 0⟩
#eval showState <| test 3 <| ⟨0, 0⟩
#eval showState <| test 4 <| ⟨0, 0⟩
#eval showState <| test 5 <| ⟨0, 0⟩

#eval maximalMatching.send 2 (test 0 ⟨0, 0⟩)
#eval maximalMatching.send 2 (test 1 ⟨0, 0⟩)
#eval maximalMatching.send 2 (test 2 ⟨0, 0⟩)
#eval maximalMatching.send 2 (test 3 ⟨0, 0⟩)
#eval maximalMatching.send 2 (test 4 ⟨0, 0⟩)
#eval maximalMatching.send 2 (test 5 ⟨0, 0⟩)

-- #eval (showState ∘ test 0) <$> allVerts
-- #eval (showState ∘ test 1) <$> allVerts
-- #eval (showState ∘ test 2) <$> allVerts
-- #eval (showState ∘ test 3) <$> allVerts
-- #eval (showState ∘ test 4) <$> allVerts
-- #eval (showState ∘ test 5) <$> allVerts
-- #eval (showState ∘ test 6) <$> allVerts

end eg

lemma reversePort_toPort (v w : V) (h : N.Adj v w) :
    N.reversePort v (N.toPort v w h) = Fin.cast (by rw [N.ofPort_toPort]) (N.toPort w v h.symm) :=
  N.ofPort_injective _ <| by
    simp only [PortNumbered.ofPort_reversePort]
    rw [N.ofPort_cast]
    · simp
    · simp

lemma send_stopped (d : ℕ) (k : Fin d) :
    ∀ curr_v ∈ maximalMatching.stoppingStates,
      maximalMatching.send _ curr_v k = .Empty
  | (r, c, .US), _ => by aesop
  | (r, c, .MS _), _ => by aesop

-- def reversePort_equiv : N.neighborSet v ≃
lemma messageRecd_even_black
    (f : V → Bool) (hf : f ∈ (Problem.Colouring Bool).valid _ N)
    (curr : V → State) (t : ℕ) (ht : Even t)
    (hcurr : maximalMatching.rounds N f t = curr)
    (v : V) (hv : f v = true) (j : Fin (N.degree v)) :
    maximalMatching.messageRecd N curr v j =
      match (curr (N.ofPort v j)).2.2 with
      | .UR => if (N.reversePort v j : ℕ) = t / 2
                then .Proposal
                else .Empty
      | .MR _ => .Matched
      | .US => .Empty
      | .MS _ => .Empty := by
  by_cases h : curr (N.ofPort v j) ∈ maximalMatching.stoppingStates
  case pos =>
    rw [Algorithm.messageRecd, send_stopped _ _ _ h]
    rw [mem_stoppingStates_iff] at h
    rcases h with (h | ⟨i, h⟩)
    · rw [h]
    · rw [h]
  have correct_round_num : (curr (N.ofPort v j)).1 = t := by
    subst hcurr
    rwa [maximalMatching_round_count]
  have other_white : (curr (N.ofPort v j)).2.1 = .white := by
    subst hcurr
    exact remains_white N f _ _ (by simpa [hv] using hf v (N.ofPort v j) (by simp))
  rw [Algorithm.messageRecd, maximalMatching_send, correct_round_num, if_pos ht, other_white]
  split
  case neg.h_1 h =>
    rw [h]
    dsimp
    split
    · simp only [Fin.ext_iff]
    · dsimp
      rw [if_neg]
      intro h
      omega
  case neg.h_2 h => rw [h]
  case neg.h_3 h => rw [h]
  case neg.h_4 h => rw [h]

-- degree is 0
-- UR at t=0
-- US at t=1

-- degree is 1
-- UR at t=0
-- UR or MR at t=1
-- US or MS at t=2

lemma nextVector_white_MS {curr next : V → State} (v : V) (i : ℕ)
    (hnext : next = maximalMatching.nextVector N curr) (h : (curr v).2.2 = .MS i) :
    (next v).2.2 = .MS i := by
  subst hnext
  rw [Algorithm.nextVector_stopped, h]
  rw [mem_stoppingStates_iff]
  exact Or.inr ⟨i, h⟩

lemma nextVector_white_US {curr next : V → State} (v : V)
    (hnext : next = maximalMatching.nextVector N curr) (h : (curr v).2.2 = .US) :
    (next v).2.2 = .US := by
  subst hnext
  rw [Algorithm.nextVector_stopped, h]
  rw [mem_stoppingStates_iff]
  exact Or.inl h

lemma nextVector_white_MR {curr next : V → State} (v : V) (i : ℕ)
    (hnext : next = maximalMatching.nextVector N curr)
    (h : (curr v).2.1 = .white)
    (h' : (curr v).2.2 = .MR i) :
    (next v).2.2 = if Even (curr v).1 then .MS i else .MR i := by
  subst hnext
  have : curr v ∉ maximalMatching.stoppingStates := by
    rw [mem_stoppingStates_iff]
    simp [h']
  rw [Algorithm.nextVector, Algorithm.fullReceive_not_stoppingState _ this, maximalMatching_receive]
  simp only [h, h']
  split
  case inl h'' => rfl
  case inr h'' => rfl

-- we can make the result more precise but it's not necessary
lemma nextVector_white_UR_odd {curr next : V → State} (v : V)
    (hnext : next = maximalMatching.nextVector N curr)
    (h : ¬ Even (curr v).1) (h' : (curr v).2.1 = .white) (h'' : (curr v).2.2 = .UR) :
    (∃ i, (next v).2.2 = .MR i) ∨ (next v).2.2 = .UR := by
  subst hnext
  have : curr v ∉ maximalMatching.stoppingStates := by
    rw [mem_stoppingStates_iff]
    simp [h'']
  rw [Algorithm.nextVector, Algorithm.fullReceive_not_stoppingState _ this, maximalMatching_receive,
    if_neg h, h', h'']
  dsimp
  split <;> simp

lemma nextVector_white_UR_even {curr next : V → State} (v : V)
    (hnext : next = maximalMatching.nextVector N curr)
    (h : Even (curr v).1) (h' : (curr v).2.1 = .white) (h'' : (curr v).2.2 = .UR) :
    (next v).2.2 = if (curr v).1 / 2 < N.degree v then .UR else .US := by
  subst hnext
  have : curr v ∉ maximalMatching.stoppingStates := by
    rw [mem_stoppingStates_iff]
    simp [h'']
  rw [Algorithm.nextVector, Algorithm.fullReceive_not_stoppingState _ this, maximalMatching_receive,
    if_pos h, h', h'']
  dsimp
  split <;> simp

lemma not_US (f : V → Bool) (u : V) (hu : f u = false) (t : ℕ) (ht : t ≤ 2 * N.degree u) :
    (maximalMatching.rounds N f t u).2.2 ≠ .US := by
  induction t
  case zero =>
    rw [Algorithm.rounds_zero, initialVector', hu, cond_false]
    simp
  case succ t ih =>
    specialize ih ((Nat.lt_succ_self _).le.trans ht)
    have hw : (maximalMatching.rounds N f t u).2.1 = .white := remains_white N f _ _ hu
    match h : (maximalMatching.rounds N f t u).2.2, ih with
    | .MR i, _ =>
        rw [nextVector_white_MR _ _ _ (Algorithm.rounds_succ _ _) hw h]
        split <;> simp
    | .MS i, _ =>
        rw [nextVector_white_MS _ _ _ (Algorithm.rounds_succ _ _) h]
        simp
    | .UR, _ =>
        have not_stopped : maximalMatching.rounds N f t u ∉ maximalMatching.stoppingStates := by
          rw [mem_stoppingStates_iff]
          simp [h]
        have := maximalMatching_round_count N f t u not_stopped
        by_cases ht : Even (maximalMatching.rounds N f t u).1
        case neg =>
          rcases nextVector_white_UR_odd _ _ (Algorithm.rounds_succ _ _) ht hw h with ⟨i, h₁⟩ | h₁
          case inl => simp [h₁]
          case inr => simp [h₁]
        case pos =>
          rw [nextVector_white_UR_even _ _ (Algorithm.rounds_succ _ _) ht hw h]
          simp only [ne_eq, ite_eq_right_iff, imp_false, not_lt, not_le, gt_iff_lt]
          rw [this]
          omega

lemma white_stops (f : V → Bool) (u : V) (hu : f u = false) :
    (maximalMatching.rounds N f (2 * N.degree u + 1) u) ∈ maximalMatching.stoppingStates := by
  sorry


#exit


lemma invariant (f : V → Bool)
    (hf : f ∈ (Problem.Colouring Bool).valid _ N)
    (u v : V) (hu : f u = false) (hv : f v = true)
    (i : Fin (N.degree u)) (hui : N.ofPort u i = v)
    (j : Fin (N.degree v)) (hj : (j : ℕ) = N.reversePort u i) :
    ∃ M X : Finset ℕ,
      (maximalMatching.rounds N f (2 * i + 1) v).2.1 = .black M X ∧
      ((j : ℕ) ∉ X ∨ Finset.Nonempty M) := by
  have hvj : N.ofPort v j = u := by
    have : j = Fin.cast (by rw [hui]) (N.reversePort u i) := by
      ext1
      exact hj
    rw [this, N.ofPort_cast _ _ hui, N.ofPort_reversePort u i]
  have hvj' : (i : ℕ) = N.reversePort v j := by
    have : j = Fin.cast (by rw [hui]) (N.reversePort u i) := by
      ext1
      exact hj
    rw [this, N.reversePort_cast _ _ hui, Fin.coe_cast, N.coe_reversePort_reversePort u i]
  have hw : ∀ k : Fin (N.degree v), f (N.ofPort v k) = false := by
    rw [N.forall_ports]
    intro u hu
    simpa only [N.ofPort_toPort, hv, ne_eq, Bool.true_eq, Bool.not_eq_true] using hf _ _ hu
  let M : Finset ℕ := sorry
  let X : Finset ℕ := sorry
  use M, X
  rw [Algorithm.rounds_succ]



  -- cases h : (i : ℕ)
  -- case zero =>

    -- simp only [mul_zero, zero_add]
    -- let M : Finset ℕ := sorry
    -- let X : Finset ℕ := sorry
    -- use M, X
    -- rw [Algorithm.rounds_succ, Algorithm.rounds_zero]
    -- have j_sent :
    --     maximalMatching.messageRecd N (maximalMatching.initialVector N f) v j = .Proposal := by
    --   rw [messageRecd_even_black N f hf _ 0 (by simp) (Algorithm.rounds_zero _ _) _ hv,
    --     initialVector']
    --   simp [←hvj', h]
    -- have no_matched :
    --     ∀ k, maximalMatching.messageRecd N (maximalMatching.initialVector N f) v k ≠ .Matched := by
    --   intro k
    --   rw [messageRecd_even_black N f hf _ 0 (by simp) (Algorithm.rounds_zero _ _) _ hv,
    --     initialVector']
    --   dsimp
    --   split <;> simp

    -- rw [Algorithm.nextVector, Algorithm.fullReceive_not_stoppingState]
    -- swap
    -- · simp only [initialVector', hv, cond_true, Algorithm.mem_stoppingStates,
    --     maximalMatching_endState, Option.isSome_none, Bool.false_eq_true, not_false_eq_true]
    -- rw [maximalMatching_receive]
    -- -- rw [maximalMatching_receive]
    -- simp only [initialVector', even_zero, ↓reduceIte, Nat.zero_div, zero_add, hv, cond_true,
    --   Finset.empty_union]




  -- case succ => sorry


end MaximalBipartiteMatching

end sec_3_5
