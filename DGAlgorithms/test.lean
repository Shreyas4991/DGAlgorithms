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
  rw [Problem.colouring_subtype_iff, Algorithm.outputAt, coe_comp_outputs_apply]
  exact all_valid _ _ hf _

end ThreeColourPath

end sec_3_4

/--
The problem of returning a subset of the edges. Essentially this ensures that the encoding returned
by the algorithm does indeed encode a subset of the edges.

Most useful as a building block problem.
 -/
def Problem.EdgeSubset : Problem (Set ℕ) where
  valid V N :=
    {f | ∀ v : V,
      -- each edge label is a valid port number
      (∀ i, i ∈ f v → i < N.degree v) ∧
      -- edges are symmetric
      (∀ i : Fin (N.degree v),
        (i : ℕ) ∈ f v ↔ (N.reversePort v i : ℕ) ∈ f (N.ofPort v i))}

/--
Option ℕ encodes a matching on a PN network: none means no edge, some n means edge to the nth port.
-/
def Problem.Matching : Problem (Option ℕ) where
  valid V N := {f | (fun v => (f v).getM) ∈ EdgeSubset.1 V N}

def Problem.MaximalMatching : Problem (Option ℕ) where
  valid V N := Matching.valid V N ∩
    {f | ∀ v : V, f v = none → -- for every unmatched node
      ∀ i : Fin (N.degree v), -- and every outward port
        f (N.ofPort v i) ≠ none} -- the corresponding node is matched

section sec_3_5

namespace MaximalBipartiteMatching

inductive EdgeState where
  | UR
  | MR : ℕ → EdgeState
  | US
  | MS : ℕ → EdgeState
  deriving DecidableEq, Repr

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
      | true =>
          if d = 0
            then (0, .black ∅ ∅, .US)
            else (0, .black ∅ (Finset.range d), .UR)
      | false => (0, .white, .UR))
    (fun rcs => match rcs.2.2 with
      | .UR => none
      | .MR _ => none
      | .US => some none
      | .MS i => some (some i))
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

-- lemma initialVector (f : V → Bool) (v : V) :
--     (maximalMatching.initialVector N f v).1 = 0 := by

lemma initialVector_1 (f : V → Bool) (v : V) :
    (maximalMatching.initialVector N f v).1 = 0 := by
  rw [Algorithm.initialVector]
  aesop

lemma initialVector_2_1 (f : V → Bool) (v : V) :
    (maximalMatching.initialVector N f v).2.1 =
      cond (f v) (.black ∅ (Finset.range (N.degree v))) .white := by
  rw [Algorithm.initialVector]
  aesop

lemma initialVector_2_2 (f : V → Bool) (v : V) :
    (maximalMatching.initialVector N f v).2.2 =
      if f v = true ∧ N.degree v = 0 then .US else .UR := by
  rw [Algorithm.initialVector]
  aesop

-- lemma initialVector (f : V → Bool) (v : V) :
--     maximalMatching.initialVector N f v =
--       cond (f v) (0, .black ∅ (Finset.range (N.degree v)), .UR) (0, .white, .UR) := rfl

-- lemma initialVector' (f : V → Bool) (v : V) :
--     maximalMatching.initialVector N f v =
--       (0, cond (f v) (.black ∅ (Finset.range (N.degree v))) .white, .UR) := by
--   rw [initialVector]
--   match f v with
--   | true => rfl
--   | false => rfl

lemma mem_stoppingStates_iff (s : State) :
    s ∈ maximalMatching.stoppingStates ↔ s.2.2 = EdgeState.US ∨ ∃ i, s.2.2 = EdgeState.MS i := by
  rcases s with ⟨_, _, (_ | _ | _ | _)⟩ <;> simp

lemma not_mem_stoppingStates_iff (s : State) :
    s ∉ maximalMatching.stoppingStates ↔ s.2.2 = EdgeState.UR ∨ ∃ i, s.2.2 = EdgeState.MR i := by
  rcases s with ⟨_, _, (_ | _ | _ | _)⟩ <;> simp

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
  | zero => rw [Algorithm.rounds_zero, initialVector_1]
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
  | zero => rw [Algorithm.rounds_zero, initialVector_2_1, h, cond_false]
  | succ t ih => exact nextVector_snd_fst_white N _ _ _ (Algorithm.rounds_succ _ _) ih

lemma remains_black (f : V → Bool) (t : ℕ) (v : V) (h : f v = true) :
    ∃ M X, (maximalMatching.rounds N f t v).2.1 = .black M X := by
  induction t with
  | zero =>
      refine ⟨∅, Finset.range (N.degree v), ?_⟩
      rw [Algorithm.rounds_zero, initialVector_2_1, h, cond_true]
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
  case neg.isFalse => use M, X; aesop
  case neg.isTrue =>
    split
    case h_1 hc _ => tauto
    case h_2 hc _ => tauto
    case h_3 hc _ =>
      cases hc
      exact ⟨_, _, rfl, Finset.subset_union_left, Finset.sdiff_subset⟩
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

lemma X_range (f : V → Bool) (t : ℕ) (v : V) (hv : f v = true) :
    ∃ M X,
    (maximalMatching.rounds N f t v).2.1 = .black M X ∧ X ⊆ Finset.range (N.degree v) := by
  have := sets_changing N f 0 t (by simp) v ∅ (Finset.range (N.degree v)) ?_
  · simpa using this
  · rw [Algorithm.rounds_zero, initialVector_2_1, hv, cond_true]

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
    Fin (exampleGraph.degree v) ≃ exampleGraph.neighborSet v
  | ⟨0, 0⟩ => bij_to_equiv
                (![⟨(1, 0), by decide⟩, ⟨(1, 2), by decide⟩]) (by decide)
  | ⟨0, 1⟩ => bij_to_equiv
                (![⟨(1, 0), by decide⟩, ⟨(1, 1), by decide⟩, ⟨(1, 3), by decide⟩]) (by decide)
  | ⟨0, 2⟩ => bij_to_equiv
                (![⟨(1, 2), by decide⟩]) (by decide)
  | ⟨0, 3⟩ => bij_to_equiv
                (![⟨(1, 2), by decide⟩, ⟨(1, 3), by decide⟩]) (by decide)
  | ⟨1, 0⟩ => bij_to_equiv
                (![⟨(0, 1), by decide⟩, ⟨(0, 0), by decide⟩]) (by decide)
  | ⟨1, 1⟩ => bij_to_equiv
                (![⟨(0, 1), by decide⟩]) (by decide)
  | ⟨1, 2⟩ => bij_to_equiv
                (![⟨(0, 0), by decide⟩, ⟨(0, 2), by decide⟩, ⟨(0, 3), by decide⟩]) (by decide)
  | ⟨1, 3⟩ => bij_to_equiv
                (![⟨(0, 1), by decide⟩, ⟨(0, 3), by decide⟩]) (by decide)

def exampleNetwork : PortNumbered (Fin 2 × Fin 4) where
  toSimpleGraph := exampleGraph
  numbering v := (exampleNumbering v).symm

def test : ℕ → Fin 2 × Fin 4 → State :=
  maximalMatching.rounds exampleNetwork (fun x => x.1 = 1)

def showEdgeState : EdgeState → Lean.Format
  | .UR => "UR"
  | .US => "US"
  | .MR i => "MR " ++ repr i
  | .MS i => "MS " ++ repr i

def showState : State → Lean.Format
  | ⟨r, .white, s⟩ => repr r ++ " white " ++ showEdgeState s
  | ⟨r, .black M X, s⟩ => s!"{r} black M={M.sort (· ≤ ·)} X={X.sort (· ≤ ·)} {showEdgeState s}"

def allVerts : List (Fin 2 × Fin 4) :=
  [⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 3⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 3⟩]

end eg

lemma reversePort_toPort (v w : V) (h : N.Adj v w) :
    N.reversePort v (N.toPort v w h) = Fin.cast (by rw [N.ofPort_toPort]) (N.toPort w v h.symm) :=
  N.ofPort_injective _ <| by
    simp only [PortNumbered.ofPort_reversePort]
    rw [N.ofPort_cast]
    · simp
    · simp

lemma reversePort_of_ofPort {u v : V} {i : Fin (N.degree u)} {j : Fin (N.degree v)}
    (h : N.ofPort u i = v) (h' : N.ofPort v j = u) :
    (N.reversePort u i : ℕ) = j := by
  cases h
  rw [←Fin.ext_iff]
  refine N.ofPort_injective _ ?_
  rw [PortNumbered.ofPort_reversePort, h']

lemma ofPort_of_reversePort {u v : V} {i : Fin (N.degree u)} {j : Fin (N.degree v)}
    (h : N.ofPort u i = v) (h' : (N.reversePort u i : ℕ) = j) :
    N.ofPort v j = u := by
  cases h
  rw [←Fin.ext_iff] at h'
  cases h'
  simp

lemma reversePort_eq_iff {u v : V} {i : Fin (N.degree u)} {j : Fin (N.degree v)}
    (h : N.ofPort u i = v) :
    (N.reversePort u i : ℕ) = j ↔ N.ofPort v j = u :=
  ⟨ofPort_of_reversePort _ h, reversePort_of_ofPort _ h⟩

lemma send_stopped (d : ℕ) (k : Fin d) :
    ∀ curr_v ∈ maximalMatching.stoppingStates,
      maximalMatching.send _ curr_v k = .Empty
  | (r, c, .US), _ => by aesop
  | (r, c, .MS _), _ => by aesop

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

lemma messageRecd_odd_white
    (f : V → Bool) (hf : f ∈ (Problem.Colouring Bool).valid _ N)
    (curr : V → State) (t : ℕ) (ht : ¬Even t)
    (hcurr : maximalMatching.rounds N f t = curr)
    (v : V) (hv : f v = false) (j : Fin (N.degree v)) :
    maximalMatching.messageRecd N curr v j =
      match (curr (N.ofPort v j)).2.2 with
      | .UR =>
          match (curr (N.ofPort v j)).2.1 with
          | .black M _ =>
              if ∃ h : M.Nonempty, N.reversePort v j = Finset.min' M h
                then .Accept
                else .Empty
          | .white => .Empty -- case will never happen
      | .MR _ => .Empty
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
  have other_white : ∃ M X, (curr (N.ofPort v j)).2.1 = .black M X := by
    subst hcurr
    exact remains_black N f _ _ (by simpa [hv] using hf v (N.ofPort v j) (by simp))
  obtain ⟨M, X, hMX⟩ := other_white
  rw [Algorithm.messageRecd, maximalMatching_send, correct_round_num, if_neg ht, hMX]
  match (curr (N.ofPort v j)).2.2 with
  | .US => simp
  | .MS _ => simp
  | .UR =>
      dsimp
      by_cases hM : M.Nonempty
      case neg => simp [hM]
      case pos =>
        simp only [hM, ↓reduceDite, exists_true_left]
  | .MR _ => simp

/-- Change in a MS node. -/
lemma nextVector_MS {curr next : V → State} (v : V) (i : ℕ)
    (hnext : next = maximalMatching.nextVector N curr) (h : (curr v).2.2 = .MS i) :
    (next v).2.2 = .MS i := by
  subst hnext
  rw [Algorithm.nextVector_stopped, h]
  rw [mem_stoppingStates_iff]
  exact Or.inr ⟨i, h⟩

/-- Change in a US node. -/
lemma nextVector_US {curr next : V → State} (v : V)
    (hnext : next = maximalMatching.nextVector N curr) (h : (curr v).2.2 = .US) :
    (next v).2.2 = .US := by
  subst hnext
  rw [Algorithm.nextVector_stopped, h]
  rw [mem_stoppingStates_iff]
  exact Or.inl h

/-- Change in a white MR node. -/
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
  case isTrue h'' => rfl
  case isFalse h'' => rfl

/-- Change in a white UR node at odd time. -/
lemma nextVector_white_UR_odd {curr next : V → State} (v : V)
    (hnext : next = maximalMatching.nextVector N curr)
    (h : ¬ Even (curr v).1) (h' : (curr v).2.1 = .white) (h'' : (curr v).2.2 = .UR) :
    (∃ i, (next v).2.2 = .MR i) ∨ (next v).2.2 = .UR := by
  subst hnext
  have : curr v ∉ maximalMatching.stoppingStates := by
    rw [mem_stoppingStates_iff]
    simp [h'']
  rw [Algorithm.nextVector, Algorithm.fullReceive_not_stoppingState _ this, maximalMatching_receive,
    if_neg h, h']
  simp only [h'']
  split <;> simp

/-- Change in a white UR node at even time.  -/
lemma nextVector_white_UR_even {curr next : V → State} (v : V)
    (hnext : next = maximalMatching.nextVector N curr)
    (h : Even (curr v).1) (h' : (curr v).2.1 = .white) (h'' : (curr v).2.2 = .UR) :
    (next v).2.2 = if (curr v).1 / 2 < N.degree v then .UR else .US := by
  subst hnext
  have : curr v ∉ maximalMatching.stoppingStates := by
    rw [mem_stoppingStates_iff]
    simp [h'']
  rw [Algorithm.nextVector, Algorithm.fullReceive_not_stoppingState _ this, maximalMatching_receive,
    if_pos h, h']
  simp only [h'']
  split <;> simp

lemma nextVector_black_UR_even {curr next : V → State} (v : V)
    (hnext : next = maximalMatching.nextVector N curr) {M X : Finset ℕ}
    (h : Even (curr v).1) (h' : (curr v).2.1 = .black M X) (h'' : (curr v).2.2 = .UR) :
    (next v).2.2 = .UR := by
  subst hnext
  have : curr v ∉ maximalMatching.stoppingStates := by
    rw [mem_stoppingStates_iff]
    simp [h'']
  rw [Algorithm.nextVector, Algorithm.fullReceive_not_stoppingState _ this,
    maximalMatching_receive, if_pos h, h']
  simp only [h'']

lemma nextVector_black_UR_odd_nonemptyM {curr next : V → State} (v : V)
    (hnext : next = maximalMatching.nextVector N curr) {M X : Finset ℕ}
    (h : ¬ Even (curr v).1) (h' : (curr v).2.1 = .black M X) (h'' : (curr v).2.2 = .UR)
    (hM : M.Nonempty) : (next v).2.2 = .MS (M.min' hM) := by
  subst hnext
  have : curr v ∉ maximalMatching.stoppingStates := by
    rw [mem_stoppingStates_iff]
    simp [h'']
  rw [Algorithm.nextVector, Algorithm.fullReceive_not_stoppingState _ this,
    maximalMatching_receive, if_neg h, h']
  simp only [h'']
  rw [dif_pos hM]

lemma nextVector_black_UR_odd_emptyX {curr next : V → State} (v : V)
    (hnext : next = maximalMatching.nextVector N curr) {M X : Finset ℕ}
    (h : ¬ Even (curr v).1) (h' : (curr v).2.1 = .black M X) (h'' : (curr v).2.2 = .UR)
    (hM : ¬ M.Nonempty) (hX : X = ∅) : (next v).2.2 = .US := by
  subst hnext
  have : curr v ∉ maximalMatching.stoppingStates := by
    rw [mem_stoppingStates_iff]
    simp [h'']
  rw [Algorithm.nextVector, Algorithm.fullReceive_not_stoppingState _ this,
    maximalMatching_receive, if_neg h, h']
  simp only [h'']
  rw [dif_neg hM, if_pos hX]

lemma nextVector_black_UR_odd_nonemptyX {curr next : V → State} (v : V)
    (hnext : next = maximalMatching.nextVector N curr) {M X : Finset ℕ}
    (h : ¬ Even (curr v).1) (h' : (curr v).2.1 = .black M X) (h'' : (curr v).2.2 = .UR)
    (hM : ¬M.Nonempty) (hX : X.Nonempty) : (next v).2.2 = .UR := by
  subst hnext
  have : curr v ∉ maximalMatching.stoppingStates := by
    rw [mem_stoppingStates_iff]
    simp [h'']
  rw [Algorithm.nextVector, Algorithm.fullReceive_not_stoppingState _ this,
    maximalMatching_receive, if_neg h, h']
  simp only [h'']
  rw [dif_neg hM, if_neg hX.ne_empty]

lemma nextVector_black_not_MR {curr next : V → State} (v : V)
    (hnext : next = maximalMatching.nextVector N curr) {M X : Finset ℕ}
    (h : (curr v).2.1 = .black M X) (h' : ¬ (∃ i, (curr v).2.2 = .MR i)) :
    ¬ (∃ i, (next v).2.2 = .MR i) := by
  rintro ⟨i, hi⟩
  subst hnext
  wlog h'' : curr v ∉ maximalMatching.stoppingStates
  case inr =>
    rw [not_not] at h''
    rw [Algorithm.nextVector_stopped _ _ _ h''] at hi
    rw [mem_stoppingStates_iff, hi] at h''
    simp only [exists_const, or_self] at h''
  have h''' := h''
  simp only [not_mem_stoppingStates_iff, h', or_false] at h''
  by_cases ht : Even (curr v).1
  case pos =>
    rw [nextVector_black_UR_even N v rfl ht h h''] at hi
    cases hi
  case neg =>
    by_cases hM : M.Nonempty
    case pos =>
      rw [nextVector_black_UR_odd_nonemptyM N v rfl ht h h'' hM] at hi
      cases hi
    case neg =>
      cases Finset.eq_empty_or_nonempty X
      case inl hX =>
        rw [nextVector_black_UR_odd_emptyX N v rfl ht h h'' hM hX] at hi
        cases hi
      case inr hX =>
        rw [nextVector_black_UR_odd_nonemptyX N v rfl ht h h'' hM hX] at hi
        cases hi

lemma black_M_bound_aux {curr next : V → State} (v : V)
    (hnext : next = maximalMatching.nextVector N curr) {M X : Finset ℕ}
    (h : (curr v).2.1 = .black M X) (h' : M ⊆ Finset.range (N.degree v)) :
    ∃ M' X', (next v).2.1 = .black M' X' ∧ M' ⊆ Finset.range (N.degree v) := by
  subst hnext
  by_cases h₂ : curr v ∈ maximalMatching.stoppingStates
  case pos =>
    rw [Algorithm.nextVector, Algorithm.fullReceive_stoppingState _ h₂, h]
    simp [h']
  rw [Algorithm.nextVector, Algorithm.fullReceive_not_stoppingState _ h₂,
    maximalMatching_receive, h]
  split
  case neg.isFalse => aesop
  case neg.isTrue =>
    split
    case h_1 => aesop
    case h_2 => aesop
    case h_3 hc _ =>
      cases hc
      simp only [ColourState.black.injEq, exists_and_right, exists_and_left, exists_eq', and_true,
        exists_eq_left']
      simp only [Finset.union_subset_iff, h', true_and]
      rw [Finset.subset_iff]
      simp
    case h_4 => aesop

/-- A black node is never in the state MR. -/
lemma black_not_MR (f : V → Bool) (u : V) (hu : f u = true) (t : ℕ)
    (curr : V → State) (hcurr : maximalMatching.rounds N f t = curr) :
    ¬ ∃ i, (curr u).2.2 = .MR i := by
  subst hcurr
  induction t with
  | zero =>
      rw [Algorithm.rounds_zero, initialVector_2_2]
      aesop
  | succ t ih =>
      obtain ⟨M, X, hMX⟩ := remains_black N f t u hu
      exact nextVector_black_not_MR N u (Algorithm.rounds_succ _ N) hMX ih

/-- A white node is not in the state MR at odd time -/
lemma white_odd_not_MR (f : V → Bool) (u : V) (hu : f u = false) (t : ℕ) (ht : ¬Even t)
    (curr : V → State) (hcurr : maximalMatching.rounds N f t = curr) :
    ¬ ∃ k, (curr u).2.2 = .MR k := by
  rw [←Nat.odd_iff_not_even] at ht
  obtain ⟨t, rfl⟩ := ht
  subst hcurr
  match h : (maximalMatching.rounds N f (2 * t) u).2.2 with
  | .MS j => simp [nextVector_MS N u j (Algorithm.rounds_succ _ _) h]
  | .US => simp [nextVector_US N u (Algorithm.rounds_succ _ _) h]
  | .UR =>
      rw [nextVector_white_UR_even N u (Algorithm.rounds_succ _ _) ?g1
        (remains_white N f (2 * t) _ hu) h]
      case g1 =>
        rw [maximalMatching_round_count]
        · simp
        · rw [not_mem_stoppingStates_iff, h]
          simp
      split <;> simp
  | .MR j =>
      rw [nextVector_white_MR N u j (Algorithm.rounds_succ _ _) (remains_white _ _ _ _ hu) h,
        maximalMatching_round_count, if_pos]
      · simp
      · simp
      · rw [not_mem_stoppingStates_iff, h]
        simp

/-- If a node is in state UR, its previous state was UR. -/
lemma prevVector_UR (f : V → Bool) (v : V) (t : ℕ)
    (h : (maximalMatching.rounds N f (t + 1) v).2.2 = .UR) :
    (maximalMatching.rounds N f t v).2.2 = .UR := by
  match h' : (maximalMatching.rounds N f t v).2.2 with
  | .UR => rfl
  | .US => simp [nextVector_US N v (Algorithm.rounds_succ _ _) h'] at h
  | .MS i => simp [nextVector_MS N v _ (Algorithm.rounds_succ _ _) h'] at h
  | .MR i =>
      match hv : f v with
      | true => cases black_not_MR N f v hv t _ rfl ⟨_, h'⟩
      | false =>
          simp [nextVector_white_MR N _ _ (Algorithm.rounds_succ _ _)
            (remains_white N f t v hv) h', ite_eq_iff] at h

/-- If a node is in state MR, its previous state was UR. -/
lemma prevVector_MR (f : V → Bool) (v : V) (t : ℕ)
    (h : (maximalMatching.rounds N f (t + 1) v).2.2 = .MR j) :
    (maximalMatching.rounds N f t v).2.2 = .UR := by
  match h' : (maximalMatching.rounds N f t v).2.2 with
  | .UR => rfl
  | .US =>
      rw [nextVector_US N v (Algorithm.rounds_succ _ _) h'] at h
      simp at h
  | .MS i =>
      rw [nextVector_MS N v _ (Algorithm.rounds_succ _ _) h'] at h
      simp at h
  | .MR i =>
      have hv : f v = false := by
        by_contra!
        simp only [ne_eq, Bool.not_eq_false] at this
        exact black_not_MR N f v this t _ rfl ⟨_, h'⟩
      exfalso
      by_cases ht : Even t
      case pos =>
        exact white_odd_not_MR N f v hv (t + 1) (by simp [parity_simps, ht]) _ rfl ⟨_, h⟩
      case neg =>
        exact white_odd_not_MR N f v hv t ht _ rfl ⟨_, h'⟩

/-- A black node with state UR at even time has M = ∅. -/
lemma black_UR_even_has_M_empty (f : V → Bool) (u : V) (hu : f u = true) (t : ℕ) (ht : Even t)
    (curr : V → State) (hcurr : maximalMatching.rounds N f t = curr)
    (hstate : (curr u).2.2 = .UR) :
    ∃ X, (curr u).2.1 = .black ∅ X := by
  replace ht : t = 0 ∨ ∃ i, t = 2 * i + 2 := by
    obtain ⟨i, rfl⟩ := ht
    cases i
    case zero => simp
    case succ i => exact Or.inr ⟨i, by omega⟩
  obtain (rfl | ⟨i, rfl⟩) := ht
  case inl =>
    subst hcurr
    rw [Algorithm.rounds_zero, initialVector_2_1, hu, cond_true]
    simp
  case inr =>
    have h₂ : maximalMatching.rounds N f (2 * i + 2) u ∉ maximalMatching.stoppingStates := by
      rw [hcurr, not_mem_stoppingStates_iff, hstate]
      simp
    have h₁ : maximalMatching.rounds N f (2 * i + 1) u ∉ maximalMatching.stoppingStates := by
      contrapose! h₂
      rwa [Algorithm.rounds_succ, Algorithm.nextVector_stopped _ _ _ h₂]
    have h₀ := h₁
    rw [not_mem_stoppingStates_iff] at h₁
    obtain (h₁ | h₁) := h₁
    case inr =>
      cases black_not_MR N f u hu (2 * i + 1) _ rfl h₁
    case inl =>
      have h₃ : (maximalMatching.rounds N f (2 * i + 1) u).1 = 2 * i + 1 := by
        rw [maximalMatching_round_count _ _ _ _ h₀]
      subst hcurr
      obtain ⟨M, X, hMX⟩ := remains_black N f (2 * i + 1) _ hu
      rw [Algorithm.rounds_succ, Algorithm.nextVector, Algorithm.fullReceive_not_stoppingState _ h₀,
        maximalMatching_receive, h₃, if_neg (by simp [parity_simps]), hMX] at hstate ⊢
      simp only [h₁] at hstate ⊢
      split
      case isTrue h =>
        rw [dif_pos h] at hstate
        cases hstate
      case isFalse h =>
        rw [dif_neg h] at hstate
        simp only [Finset.not_nonempty_iff_eq_empty] at h
        simp only [ite_eq_right_iff, imp_false] at hstate
        exact ⟨X, by simp [h]⟩

/-- A black node with state UR at odd time has known M value. -/
lemma black_UR_odd_M_value (f : V → Bool) (hf : f ∈ (Problem.Colouring Bool).valid _ N)
    (u : V) (hu : f u = true) (t : ℕ) (ht : ¬Even t)
    (curr : V → State) (hcurr : maximalMatching.rounds N f t = curr)
    (hstate : (curr u).2.2 = .UR) :
    ∃ M X, (curr u).2.1 = .black M X ∧
        M ⊆ (Finset.univ.filter fun i => (N.reversePort u i : ℕ) = (t - 1) / 2).map
          Fin.valEmbedding := by
  rw [←Nat.odd_iff_not_even] at ht
  obtain ⟨t, rfl⟩ := ht
  let old := maximalMatching.rounds N f (2 * t)
  have h₁ : (old u).2.2 = .UR := by
    match h : (old u).2.2 with
    | .UR => rfl
    | .US =>
        subst hcurr
        rw [nextVector_US N u (Algorithm.rounds_succ _ _) h] at hstate
        cases hstate
    | .MS j =>
        subst hcurr
        rw [nextVector_MS N u _ (Algorithm.rounds_succ _ _) h] at hstate
        cases hstate
    | .MR j => cases black_not_MR N f u hu _ old rfl ⟨_, h⟩
  obtain ⟨X, hX⟩ := black_UR_even_has_M_empty N f u hu (2 * t) (by simp) old rfl h₁
  have h₃ : old u ∉ maximalMatching.stoppingStates := by
    rw [not_mem_stoppingStates_iff]
    simp [h₁]
  have h₂ : Even (old u).1 := by
    rw [maximalMatching_round_count _ _ _ _ h₃]
    simp
  subst hcurr
  rw [Algorithm.rounds_succ, Algorithm.nextVector, Algorithm.fullReceive_not_stoppingState _ h₃,
    maximalMatching_receive, if_pos h₂, hX]
  simp only [Finset.empty_union, ColourState.black.injEq, add_tsub_cancel_right, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀, exists_and_right, exists_and_left,
    exists_eq', and_true, exists_eq_left', Finset.map_subset_map, h₁]
  refine Finset.monotone_filter_right _ fun i hi => ?_
  rw [messageRecd_even_black N f hf old (2 * t) (by simp) rfl _ hu] at hi
  split at hi
  case h_1 => simpa using hi
  case h_2 => simp at hi
  case h_3 => simp at hi
  case h_4 => simp at hi

/-- If a white node is in state MR at some time, its value is known. -/
lemma white_even_MR_val (f : V → Bool)
    (hf : f ∈ (Problem.Colouring Bool).valid _ N)
    (u : V) (hu : f u = false) (t k : ℕ)
    (curr : V → State) (hcurr : maximalMatching.rounds N f t = curr)
    (hstate : (curr u).2.2 = .MR k) :
    k = t / 2 - 1 ∧ k < N.degree u := by
  have ht : Even t := by
    by_contra ht
    exact white_odd_not_MR N f u hu t ht curr hcurr ⟨_, hstate⟩
  have ht' : t ≠ 0 := by
    subst hcurr
    rintro rfl
    rw [Algorithm.rounds_zero, initialVector_2_2] at hstate
    aesop
  obtain ⟨t, rfl⟩ : ∃ i, t = 2 * i + 2 := by
    obtain ⟨i, rfl⟩ := ht
    cases i
    case zero => cases ht' rfl
    case succ i => exact ⟨i, by omega⟩
  clear ht ht'
  simp only [Nat.ofNat_pos, Nat.add_div_right, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    mul_div_cancel_left₀, Nat.succ_eq_add_one, add_tsub_cancel_right]
  let old := maximalMatching.rounds N f (2 * t + 1)
  have h₀ : (old u).2.2 = .UR := by
    match h : (old u).2.2 with
    | .UR => rfl
    | .US =>
        subst hcurr
        rw [nextVector_US N u (Algorithm.rounds_succ _ _) h] at hstate
        cases hstate
    | .MS j =>
        subst hcurr
        rw [nextVector_MS N u j (Algorithm.rounds_succ _ _) h] at hstate
        cases hstate
    | .MR j =>
        cases white_odd_not_MR N f u hu (2 * t + 1) (by simp [parity_simps]) old rfl ⟨_, h⟩
  have : old u ∉ maximalMatching.stoppingStates := by
    rw [not_mem_stoppingStates_iff]
    simp [h₀]
  have h₁ : (old u).1 = 2 * t + 1 := by rw [maximalMatching_round_count _ _ _ _ this]
  have h₂ : (old u).2.1 = .white := remains_white _ _ _ _ hu
  have h₃ : ¬ Even (2 * t + 1) := by simp [parity_simps]
  subst hcurr
  have h₄ : ∀ z ∈ Finset.univ.filter (fun x => maximalMatching.messageRecd N old u x = Msg.Accept),
      z = t := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro z hz
    rw [messageRecd_odd_white N f hf old _ h₃ rfl u hu z] at hz
    split at hz
    case h_2 => cases hz
    case h_3 => cases hz
    case h_4 => cases hz
    case h_1 hv₁ =>
      split at hz
      case h_2 => cases hz
      case h_1 M X hv₂ =>
        simp only [ite_eq_left_iff, not_exists, imp_false, not_forall, Decidable.not_not] at hz
        obtain ⟨hM, h⟩ := hz
        have : f (N.ofPort u z) = true := by simpa [hu] using hf u (N.ofPort u z)
        obtain ⟨M, X, hMX, hM'⟩ := black_UR_odd_M_value N f hf (N.ofPort u z) this _ h₃ old rfl hv₁
        simp only [add_tsub_cancel_right, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          mul_div_cancel_left₀] at hM'
        rw [hMX] at hv₂
        cases hv₂
        have : (N.reversePort u z : ℕ) ∈ M := by
          rw [h]
          exact Finset.min'_mem _ _
        have : Fin.valEmbedding _ ∈ _ := hM' this
        rw [Finset.mem_map'] at this
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        rw [PortNumbered.coe_reversePort_reversePort] at this
        exact this
  rw [Algorithm.rounds_succ, Algorithm.nextVector, Algorithm.fullReceive_not_stoppingState _ this,
    maximalMatching_receive, h₁, if_neg h₃, h₂] at hstate
  simp only [h₀] at hstate
  split at hstate
  case isFalse => trivial
  case isTrue h =>
    simp only [EdgeState.MR.injEq] at hstate
    set Q := Finset.univ.filter (fun x => maximalMatching.messageRecd N old u x = Msg.Accept)
    change Q.min' h = k at hstate
    have : Q.min' h = t := h₄ _ (Finset.min'_mem _ _)
    rw [←hstate, ←this]
    simp

/-- If the round number is not more than twice the degree of a white node, it cannot have moved
to state US.  -/
lemma white_not_US (f : V → Bool) (u : V) (hu : f u = false) (t : ℕ) (ht : t ≤ 2 * N.degree u) :
    (maximalMatching.rounds N f t u).2.2 ≠ .US := by
  induction t
  case zero =>
    rw [Algorithm.rounds_zero, initialVector_2_2, hu]
    simp
  case succ t ih =>
    specialize ih ((Nat.lt_succ_self _).le.trans ht)
    have hw : (maximalMatching.rounds N f t u).2.1 = .white := remains_white N f _ _ hu
    match h : (maximalMatching.rounds N f t u).2.2, ih with
    | .MR i, _ =>
        rw [nextVector_white_MR _ _ _ (Algorithm.rounds_succ _ _) hw h]
        split <;> simp
    | .MS i, _ =>
        rw [nextVector_MS _ _ _ (Algorithm.rounds_succ _ _) h]
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

lemma black_M_bound (f : V → Bool) (t : ℕ) (u : V) (hu : f u = true) :
    ∃ M X, (maximalMatching.rounds N f t u).2.1 = .black M X ∧ M ⊆ Finset.range (N.degree u) := by
  induction t with
  | zero =>
      rw [Algorithm.rounds_zero, initialVector_2_1, hu, cond_true]
      simp
  | succ t ih =>
      obtain ⟨M, X, hMX, hM⟩ := ih
      exact black_M_bound_aux N u (Algorithm.rounds_succ _ N) hMX hM

lemma black_MS_bound (f : V → Bool)
    (u : V) (hu : f u = true) (t k : ℕ)
    (curr : V → State) (hcurr : maximalMatching.rounds N f t = curr)
    (hstate : (curr u).2.2 = .MS k) :
    k < N.degree u := by
  subst hcurr
  induction t
  case zero =>
    rw [Algorithm.rounds_zero, initialVector_2_2] at hstate
    aesop
  case succ t ih =>
    match h : (maximalMatching.rounds N f t u).2.2 with
    | .US =>
        rw [nextVector_US N u (Algorithm.rounds_succ _ _) h] at hstate
        cases hstate
    | .MS l =>
        rw [nextVector_MS N u _ (Algorithm.rounds_succ _ _) h] at hstate
        cases hstate
        exact ih h
    | .MR l => cases black_not_MR N f u hu _ _ rfl ⟨_, h⟩
    | .UR =>
        obtain ⟨M, X, hMX, hMd⟩ := black_M_bound N f t u hu
        by_cases ht : Even (maximalMatching.rounds N f t u).1
        case pos =>
          rw [nextVector_black_UR_even N u (Algorithm.rounds_succ _ _) ht hMX h] at hstate
          cases hstate
        case neg =>
          by_cases hM : M.Nonempty
          case pos =>
            rw [nextVector_black_UR_odd_nonemptyM N u (Algorithm.rounds_succ _ _) ht hMX h hM]
              at hstate
            cases hstate
            simpa using hMd (Finset.min'_mem M hM)
          case neg =>
            cases Finset.eq_empty_or_nonempty X
            case inl hX =>
              rw [nextVector_black_UR_odd_emptyX N u (Algorithm.rounds_succ _ _) ht hMX h hM hX]
                at hstate
              cases hstate
            case inr hX =>
              rw [nextVector_black_UR_odd_nonemptyX N u (Algorithm.rounds_succ _ _) ht hMX h hM hX]
                at hstate
              cases hstate

lemma white_MS_bound (f : V → Bool) (hf : f ∈ (Problem.Colouring Bool).valid _ N)
    (u : V) (hu : f u = false) (t k : ℕ)
    (curr : V → State) (hcurr : maximalMatching.rounds N f t = curr)
    (hstate : (curr u).2.2 = .MS k) :
    k < N.degree u := by
  subst hcurr
  induction t
  case zero =>
    rw [Algorithm.rounds_zero, initialVector_2_2] at hstate
    simp [hu] at hstate
  case succ t ih =>
    match h : (maximalMatching.rounds N f t u).2.2 with
    | .US =>
        rw [nextVector_US N u (Algorithm.rounds_succ _ _) h] at hstate
        cases hstate
    | .MS l =>
        rw [nextVector_MS N u _ (Algorithm.rounds_succ _ _) h] at hstate
        cases hstate
        exact ih h
    | .UR =>
        by_cases ht : Even (maximalMatching.rounds N f t u).1
        case pos =>
          rw [nextVector_white_UR_even N u (Algorithm.rounds_succ _ _) ht
            (remains_white _ _ _ _ hu) h] at hstate
          aesop
        case neg =>
          have := nextVector_white_UR_odd N u (Algorithm.rounds_succ _ _) ht
            (remains_white _ _ _ _ hu) h
          aesop
    | .MR l =>
        rw [nextVector_white_MR N u l (Algorithm.rounds_succ _ _)
          (remains_white _ _ _ _ hu) h] at hstate
        have : l = k := by aesop
        cases this
        exact (white_even_MR_val N f hf u hu _ _ _ rfl h).2

lemma MS_bound (f : V → Bool) (hf : f ∈ (Problem.Colouring Bool).valid _ N) (u : V) (t k : ℕ)
    (curr : V → State) (hcurr : maximalMatching.rounds N f t = curr)
    (hstate : (curr u).2.2 = .MS k) :
    k < N.degree u :=
  match h : f u with
  | true => black_MS_bound N f u h _ _ curr hcurr hstate
  | false => white_MS_bound N f hf u h _ _ curr hcurr hstate

/-- There are cases where this is the first time the node stops. -/
lemma white_stops (f : V → Bool) (u : V) (hu : f u = false) :
    maximalMatching.rounds N f (2 * N.degree u + 1) u ∈ maximalMatching.stoppingStates := by
  wlog h : maximalMatching.rounds N f (2 * N.degree u) u ∉ maximalMatching.stoppingStates
  · rw [not_not] at h
    rwa [Algorithm.rounds_succ, Algorithm.nextVector_stopped _ _ _ h]
  have h' := h
  rw [not_mem_stoppingStates_iff] at h
  rcases h with (h | ⟨i, h⟩)
  case inr =>
    rw [mem_stoppingStates_iff]
    refine Or.inr ⟨i, ?_⟩
    rw [nextVector_white_MR N u i (Algorithm.rounds_succ _ _) (remains_white N f _ u hu) h,
      maximalMatching_round_count _ _ _ _ h']
    simp
  case inl =>
    rw [mem_stoppingStates_iff]
    left
    rw [nextVector_white_UR_even N u (Algorithm.rounds_succ _ _) _ (remains_white N f _ u hu) h,
      if_neg]
    · rw [maximalMatching_round_count _ _ _ _ h']
      simp
    · rw [maximalMatching_round_count _ _ _ _ h']
      simp

/-- If white u has reached state MS and adjacent black v is in UR, then the port from v to u has
been removed from v's X. -/
lemma sends_on_match (f : V → Bool)
    (hf : f ∈ (Problem.Colouring Bool).valid _ N)
    (u v : V) (hu : f u = false) (hv : f v = true)
    (j : Fin (N.degree v)) (hvj : N.ofPort v j = u)
    (k : ℕ) (t : ℕ)
    (hv' : (maximalMatching.rounds N f t v).2.2 = .UR)
    (h : (maximalMatching.rounds N f t u).2.2 = .MS k) :
    ∃ M X, (j : ℕ) ∉ X ∧ (maximalMatching.rounds N f t v).2.1 = .black M X := by
  induction t
  case zero => simp [Algorithm.rounds_zero, initialVector_2_2, hu] at h
  case succ t ih =>
    have h' : maximalMatching.rounds N f t v ∉ maximalMatching.stoppingStates := by
      have : (maximalMatching.rounds N f (t + 1) v) ∉ maximalMatching.stoppingStates := by
        rw [not_mem_stoppingStates_iff, hv']
        simp
      contrapose! this
      rwa [Algorithm.rounds_succ, Algorithm.nextVector_stopped]
      exact this
    have h₀ : (maximalMatching.rounds N f t v).2.2 = .UR := by
      rw [not_mem_stoppingStates_iff] at h'
      exact h'.resolve_right (black_not_MR N f v hv t _ rfl)
    wlog h₁ : (maximalMatching.rounds N f t u).2.2 ≠ EdgeState.MS k generalizing
    case inr =>
      rw [not_not] at h₁
      obtain ⟨M, X, hj, h₂⟩ := ih h₀ h₁
      obtain ⟨M', X', h₃, _, hX⟩ := next_monotonicity N (maximalMatching.rounds N f t)
        (maximalMatching.rounds N f (t + 1)) v M X (Algorithm.rounds_succ _ _) h₂
      refine ⟨M', X', ?_, h₃⟩
      contrapose! hj
      exact hX hj
    have hw := remains_white N f t u hu
    have h₂ : (maximalMatching.rounds N f t u).2.2 = EdgeState.MR k ∧ Even t := by
      match h₃ : (maximalMatching.rounds N f t u).2.2 with
      | .MS k' =>
          rw [nextVector_MS N u _ (Algorithm.rounds_succ _ _) h₃] at h
          cases h
          cases h₁ h₃
      | .US =>
          rw [nextVector_US N u (Algorithm.rounds_succ _ _) h₃] at h
          cases h
      | .UR =>
          by_cases Even (maximalMatching.rounds N f t u).1
          case pos h₄ =>
            rw [nextVector_white_UR_even N u (Algorithm.rounds_succ _ _) h₄ hw h₃] at h
            split at h <;> trivial
          case neg h₄ =>
            have := nextVector_white_UR_odd N u (Algorithm.rounds_succ _ _) h₄ hw h₃
            simp [h] at this
      | .MR k' =>
          rw [nextVector_white_MR N u k' (Algorithm.rounds_succ _ _) hw h₃] at h
          split at h
          case isTrue h' =>
            cases h
            refine ⟨rfl, ?_⟩
            rwa [maximalMatching_round_count] at h'
            rw [not_mem_stoppingStates_iff, h₃]
            simp
          case isFalse => cases h
    obtain ⟨h₂, h₃⟩ := h₂
    have h₄ := messageRecd_even_black N f hf _ t h₃ rfl v hv j
    simp only [hvj, h₂] at h₄
    obtain ⟨M, X, hMX⟩ := remains_black N f t v hv
    rw [Algorithm.rounds_succ, Algorithm.nextVector, Algorithm.fullReceive_not_stoppingState _ h',
      maximalMatching_receive, maximalMatching_round_count _ _ _ _ h', if_pos h₃, hMX]
    simp only [h₀, ColourState.black.injEq, exists_eq_right_right', Finset.mem_sdiff, and_true,
      Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply, not_and,
      not_exists, not_forall, Classical.not_imp, Decidable.not_not, exists_and_left, exists_eq']
    intro
    use j

/-- If white u hasn't reached MR or MS, then adjacent black v keeps it in its X. -/
lemma not_send_on_no_match (f : V → Bool)
    (hf : f ∈ (Problem.Colouring Bool).valid _ N)
    (u v : V) (hu : f u = false) (hv : f v = true)
    (j : Fin (N.degree v)) (hvj : N.ofPort v j = u) (t : ℕ)
    (hv' : (maximalMatching.rounds N f t v).2.2 = .UR)
    (h₁ : ∀ i, (maximalMatching.rounds N f t u).2.2 ≠ EdgeState.MS i)
    (h₂ : ∀ i, (maximalMatching.rounds N f t u).2.2 ≠ EdgeState.MR i) :
    ∃ M X, (j : ℕ) ∈ X ∧ (maximalMatching.rounds N f t v).2.1 = .black M X := by
  induction t
  case zero => simp [Algorithm.rounds_zero, initialVector_2_2, initialVector_2_1, hv] at hv' ⊢
  case succ t ih =>
    have h₀ := prevVector_UR _ _ _ _ hv'
    have h₁' : ∀ (i : ℕ), (maximalMatching.rounds N f t u).2.2 ≠ EdgeState.MS i := by
      intro i
      intro hi
      simp [nextVector_MS N u i (Algorithm.rounds_succ _ _) hi] at h₁
    have h₂' : ∀ (i : ℕ), (maximalMatching.rounds N f t u).2.2 ≠ EdgeState.MR i := by
      intro i hi
      have ht : Even t := by
        by_contra ht
        exact white_odd_not_MR N f u hu t ht _ rfl ⟨_, hi⟩
      rw [nextVector_white_MR N u i (Algorithm.rounds_succ _ _) (remains_white _ _ _ _ hu) hi,
        if_pos] at h₁
      case hc =>
        rwa [maximalMatching_round_count]
        simp [hi]
      simp at h₁
    obtain ⟨M, X, hjX, hMX⟩ := ih (prevVector_UR _ _ _ _ hv') h₁' h₂'
    have h₄ : maximalMatching.rounds N f t v ∉ maximalMatching.stoppingStates := by
      rw [not_mem_stoppingStates_iff]
      simp [h₀]
    rw [Algorithm.rounds_succ, Algorithm.nextVector, Algorithm.fullReceive_not_stoppingState _ h₄,
      maximalMatching_receive, maximalMatching_round_count _ _ _ _ h₄, hMX] at hv' ⊢
    simp only [h₀] at hv' ⊢
    by_cases ht : Even t
    case neg =>
      rw [if_neg ht] at hv' ⊢
      by_cases hM : M.Nonempty
      case pos => simp [dif_pos hM] at hv'
      case neg => simp [dif_neg hM, hjX]
    case pos =>
      clear hv'
      rw [if_pos ht]
      simp only [ColourState.black.injEq, exists_eq_right_right', Finset.mem_sdiff, hjX,
        Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
        not_exists, not_and, exists_and_left, exists_eq', and_true, Fin.val_eq_val]
      rintro j hj rfl
      simp only [messageRecd_even_black N f hf _ t ht rfl v hv j, hvj] at hj
      split at hj
      case h_1 => simp [ite_eq_iff] at hj
      case h_2 h => exact h₂' _ h
      case h_3 => cases hj
      case h_4 => cases hj

lemma invariant (f : V → Bool) (hf : f ∈ (Problem.Colouring Bool).valid _ N)
    (u v : V) (hu : f u = false) (hv : f v = true)
    (i : Fin (N.degree u)) (hui : N.ofPort u i = v) (j : Fin (N.degree v)) (hvj : N.ofPort v j = u)
    (hv' : (maximalMatching.rounds N f (2 * i + 1) v).2.2 = .UR) :
    ∃ M X : Finset ℕ,
      ((j : ℕ) ∉ X ∨ Finset.Nonempty M) ∧
      (maximalMatching.rounds N f (2 * i + 1) v).2.1 = .black M X := by
  wlog h₁ : ¬∃ k, (maximalMatching.rounds N f (2 * i) u).2.2 = EdgeState.MS k generalizing
  case inr =>
    rw [not_not] at h₁
    obtain ⟨k, hk⟩ := h₁
    have hk' : (maximalMatching.rounds N f (2 * i + 1) u).2.2 = .MS k := by
      rwa [Algorithm.rounds_succ, Algorithm.nextVector_stopped]
      rw [mem_stoppingStates_iff, hk]
      simp
    obtain ⟨M, X, hj, hMX⟩ := sends_on_match N f hf u v hu hv j hvj k (2 * i + 1) hv' hk'
    exact ⟨M, X, Or.inl hj, hMX⟩
  have h₅ : maximalMatching.rounds N f (2 * i) v ∉ maximalMatching.stoppingStates := by
    have : maximalMatching.rounds N f (2 * i + 1) v ∉ maximalMatching.stoppingStates := by
      rw [not_mem_stoppingStates_iff, hv']
      simp
    contrapose! this
    rwa [Algorithm.rounds_succ, Algorithm.nextVector_stopped _ _ _ this]
  have h₆ : (maximalMatching.rounds N f (2 * i) v).2.2 = .UR := by
    rw [not_mem_stoppingStates_iff] at h₅
    exact h₅.resolve_right (black_not_MR N f v hv (2 * i) _ rfl)
  have h₂ := white_not_US N f u hu (2 * i) (by omega)
  match h₃ : (maximalMatching.rounds N f (2 * ↑i) u).2.2 with
  | .US => cases h₂ h₃
  | .MS k => cases h₁ ⟨_, h₃⟩
  | .UR =>
      have h₇ : (N.reversePort v j : ℕ) = (i : ℕ) := reversePort_of_ofPort _ hvj hui
      have := messageRecd_even_black N f hf _ (2 * i) (by simp) rfl v hv j
      simp only [hvj, h₃, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀,
        ne_eq, if_pos h₇] at this
      obtain ⟨M, X, hMX⟩ := remains_black N f (2 * i) v hv
      rw [Algorithm.rounds_succ, Algorithm.nextVector, Algorithm.fullReceive_not_stoppingState _ h₅,
        maximalMatching_receive, maximalMatching_round_count _ _ _ _ h₅, hMX, if_pos]
      case hc => simp
      simp only [ColourState.black.injEq, exists_eq_right_right', Finset.mem_sdiff, Finset.mem_map,
        Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply, not_exists, not_and,
        not_forall, Classical.not_imp, Decidable.not_not, exists_eq_right', h₆]
      right
      refine Finset.Nonempty.inr ?_
      simp only [Finset.map_nonempty, Finset.filter_nonempty_iff]
      exact ⟨j, by simp, this⟩
  | .MR k =>
      have := messageRecd_even_black N f hf _ (2 * i) (by simp) rfl v hv j
      simp only [hvj, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀,
        h₃] at this
      obtain ⟨M, X, hMX⟩ := remains_black N f (2 * i) v hv
      rw [Algorithm.rounds_succ, Algorithm.nextVector, Algorithm.fullReceive_not_stoppingState _ h₅,
        maximalMatching_receive, maximalMatching_round_count _ _ _ _ h₅, hMX, if_pos]
      case hc => simp
      simp only [ColourState.black.injEq, exists_eq_right_right', Finset.mem_sdiff, Finset.mem_map,
        Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply, not_exists, not_and,
        not_forall, Classical.not_imp, Decidable.not_not, exists_eq_right', h₆]
      left
      intro
      use j

/-- If a black node reaches US on time t+1, then its X must have been empty at time t.  -/
lemma black_US_empty_X (f : V → Bool) (t : ℕ) (v : V) (hv : f v = true)
    (h : (maximalMatching.rounds N f t v).2.2 = .US) :
    (maximalMatching.rounds N f t v).2.1 = .black ∅ ∅ := by
  induction t
  case zero =>
    simpa [Algorithm.rounds_zero, initialVector_2_1, hv, initialVector_2_2] using h
  case succ t ih =>
    match h₁ : (maximalMatching.rounds N f t v).2.2 with
    | .US =>
        obtain hM := ih h₁
        rw [Algorithm.rounds_succ, Algorithm.nextVector_stopped, hM]
        simp [h₁]
    | .MS k => simp only [nextVector_MS N v k (Algorithm.rounds_succ _ _) h₁] at h
    | .MR k => cases black_not_MR N f v hv _ _ rfl ⟨_, h₁⟩
    | .UR =>
        clear ih
        obtain ⟨M, X, hMX⟩ := remains_black N f t v hv
        have ht : ¬ Even (maximalMatching.rounds N f t v).1 := by
          intro ht
          simp only [nextVector_black_UR_even N v (Algorithm.rounds_succ _ _) ht hMX h₁] at h
        have hM : ¬M.Nonempty := by
          intro hM
          simp only [nextVector_black_UR_odd_nonemptyM N v (Algorithm.rounds_succ _ _) ht hMX
            h₁ hM] at h
        have hX : ¬X.Nonempty := by
          intro hX
          rw [nextVector_black_UR_odd_nonemptyX N v (Algorithm.rounds_succ _ _) ht hMX
            h₁ hM hX] at h
          simp at h
        rw [Algorithm.rounds_succ, Algorithm.nextVector,
          Algorithm.fullReceive_not_stoppingState _ (by simp [h₁]),
          maximalMatching_receive, if_neg ht, hMX]
        simp [h₁, hM, ←Finset.not_nonempty_iff_eq_empty, hX]

lemma black_stops [Fintype V] [DecidableRel N.Adj]
    (f : V → Bool) (hf : f ∈ (Problem.Colouring Bool).valid _ N)
    (t : ℕ) (hΔ : N.maxDegree ≤ t) (ht : 0 < t)
    (v : V) (hv : f v = true) :
    maximalMatching.rounds N f (2 * t) v ∈ maximalMatching.stoppingStates := by
  cases t
  case zero => cases ht
  rename_i t
  rw [mul_add, mul_one] -- mul_add_one doesn't work here
  wlog h₀ : maximalMatching.rounds N f (2 * t + 1) v ∉ maximalMatching.stoppingStates generalizing
  · rw [not_not] at h₀
    rwa [Algorithm.rounds_succ, Algorithm.nextVector_stopped _ _ _ h₀]
  have h₁ : (maximalMatching.rounds N f (2 * t + 1) v).2.2 = .UR := by
    rw [not_mem_stoppingStates_iff] at h₀
    exact h₀.resolve_right (black_not_MR N f v hv (2 * t + 1) _ rfl)
  have h₂ : (maximalMatching.rounds N f (2 * t + 1) v).1 = 2 * t + 1 := by
    rw [maximalMatching_round_count _ _ _ _ h₀]
  obtain ⟨M, X, hMX⟩ := remains_black N f (2 * t + 1) v hv
  by_cases M.Nonempty
  case pos hM =>
    rw [mem_stoppingStates_iff]
    right
    rw [nextVector_black_UR_odd_nonemptyM N v (Algorithm.rounds_succ _ _) _ hMX h₁ hM]
    · simp
    · simp [h₂, parity_simps]
  case neg hM =>
    rcases X.eq_empty_or_nonempty with rfl | hX
    case inl =>
      rw [mem_stoppingStates_iff]
      left
      rw [nextVector_black_UR_odd_emptyX N v (Algorithm.rounds_succ _ _) _ hMX h₁ hM rfl]
      simp [h₂, parity_simps]
    case inr =>
      obtain ⟨j', hj⟩ := hX
      obtain ⟨M', X', hX, h⟩ := X_range N f (2 * t + 1) v hv
      rw [hMX] at hX
      cases hX
      have hj' : j' < N.degree v := Finset.mem_range.1 (h hj)
      set j : Fin (N.degree v) := ⟨j', hj'⟩
      have : (j : ℕ) = j' := rfl
      clear_value j
      cases this
      let u := N.ofPort _ j
      let i := N.reversePort v j
      have hui :  N.ofPort u i = v := by simp [u, i]
      have : i ≤ t := by
        rw [←Nat.lt_add_one_iff]
        calc i < N.degree (N.ofPort v j) := i.isLt
          _ ≤ N.maxDegree := by
            convert N.degree_le_maxDegree _
          _ ≤ t + 1 := hΔ
      have : (maximalMatching.rounds N f (2 * ↑i + 1) v).2.2 = EdgeState.UR := by
        have : maximalMatching.rounds N f (2 * ↑i + 1) v ∉ maximalMatching.stoppingStates := by
          contrapose! h₀
          refine maximalMatching.rounds_mem_stoppingStates N _ ?_ _ h₀
          omega
        rw [not_mem_stoppingStates_iff] at this
        exact this.resolve_right (black_not_MR N f v hv _ _ rfl)
      have hu : f u = false := by simpa [hv] using hf v u (N.ofPort_adj _)
      obtain ⟨M', X', h, hMX'⟩ := invariant N f hf u v hu hv i hui j rfl this
      have := sets_changing N f (2 * i + 1) (2 * t + 1) (by omega) _ _ _ hMX'
      simp only [hMX, ColourState.black.injEq] at this
      obtain ⟨_, _, ⟨rfl, rfl⟩, hM', hX⟩ := this
      exfalso
      cases h
      case inl h => exact h (hX hj)
      case inr h => exact hM (h.mono hM')

lemma stoppedBy_maxDegree_zero [Fintype V] [DecidableRel N.Adj]
    (f : V → Bool) (h : N.maxDegree = 0) :
    maximalMatching.stoppedBy N f 1 := by
  intro v
  have h₁ : N.degree v = 0 := by
    have := N.degree_le_maxDegree v
    rw [h, nonpos_iff_eq_zero] at this
    convert this
  cases hv : f v with
  | false =>
      have := white_stops N f v hv
      rw [h₁, mul_zero, zero_add] at this
      exact Algorithm.rounds_mem_stoppingStates _ N _ (by omega) _ this
  | true =>
      have : maximalMatching.rounds N f 0 v ∈ maximalMatching.stoppingStates := by
        rw [mem_stoppingStates_iff, Algorithm.rounds_zero, initialVector_2_2, hv, h₁]
        simp
      exact Algorithm.rounds_mem_stoppingStates _ _ _ (by simp) _ this

lemma stoppedBy [Fintype V] [DecidableRel N.Adj]
    (f : V → Bool) (hf : f ∈ (Problem.Colouring Bool).valid V N) :
    maximalMatching.stoppedBy N f (2 * N.maxDegree + 1) := by
  intro v
  cases hv : f v with
  | false =>
      refine Algorithm.rounds_mem_stoppingStates _ _ _ ?_ _ (white_stops N f v hv)
      simp only [add_le_add_iff_right, gt_iff_lt, Nat.ofNat_pos, mul_le_mul_left]
      convert N.degree_le_maxDegree _
  | true =>
      rcases N.maxDegree.eq_zero_or_pos with h | h
      case inl =>
        rw [h, mul_zero, zero_add]
        exact stoppedBy_maxDegree_zero N f h _
      case inr =>
        exact Algorithm.rounds_mem_stoppingStates _ _ _ (by simp) _
          (black_stops N f hf _ le_rfl h v hv)

@[simp] lemma Set.failure_def {α : Type*} : (failure : Set α) = ∅ := rfl

@[simp]
lemma Option.getM_set_iff {x : α} {y : Option α} : x ∈ (y.getM : Set α) ↔ x ∈ y := by
  simp only [Option.getM, Option.mem_def, Set.pure_def, Set.failure_def]
  split
  case h_1 => simp
  case h_2 => simp [Eq.comm]

lemma outputAt_eq_some_iff {f : V → Bool} {t : ℕ} {h : maximalMatching.stoppedBy N f t} {v : V}
    {i : ℕ} :
    maximalMatching.outputAt N f t h v = some i ↔ (maximalMatching.rounds N f t v).2.2 = .MS i := by
  specialize h v
  change Option.get _ h = _ ↔ _
  match h' : (maximalMatching.rounds N f t v).2.2 with
    | .MR j | .UR => simp [mem_stoppingStates_iff, h'] at h
    | .US => simp [h']
    | .MS j => simp [h']

lemma outputAt_eq_none_iff {f : V → Bool} {t : ℕ} {h : maximalMatching.stoppedBy N f t} {v : V} :
    maximalMatching.outputAt N f t h v = none ↔ (maximalMatching.rounds N f t v).2.2 = .US := by
  specialize h v
  change Option.get _ h = _ ↔ _
  match h' : (maximalMatching.rounds N f t v).2.2 with
    | .MR j | .UR => simp [mem_stoppingStates_iff, h'] at h
    | .US => simp [h']
    | .MS j => simp [h']

theorem same_matches_wb (f : V → Bool)
    (hf : f ∈ (Problem.Colouring Bool).valid V N) (t : ℕ)
    (u v : V) (i : Fin (N.degree u)) (j : Fin (N.degree v))
    (hvj : N.ofPort v j = u) (hui : N.ofPort u i = v)
    (hv : f v = false) (h : (maximalMatching.rounds N f t v).2.2 = EdgeState.MS j) :
    (maximalMatching.rounds N f t u).2.2 = EdgeState.MS i := by
  induction t with
  | zero => simp [Algorithm.rounds_zero, initialVector_2_2, hv] at h
  | succ t ih =>
      match hv' : (maximalMatching.rounds N f t v).2.2 with
      | .US =>
          rw [nextVector_US N _ (Algorithm.rounds_succ _ _) hv'] at h
          cases h
      | .MS j' =>
          rw [nextVector_MS N _ _ (Algorithm.rounds_succ _ _) hv'] at h
          cases h
          rw [nextVector_MS N _ _ (Algorithm.rounds_succ _ _) (ih hv')]
      | .UR =>
          by_cases Even (maximalMatching.rounds N f t v).1
          case pos h' =>
            rw [nextVector_white_UR_even N _ (Algorithm.rounds_succ _ _) h'
              (remains_white _ _ _ _ hv) hv'] at h
            aesop
          case neg h' =>
            have := nextVector_white_UR_odd N _ (Algorithm.rounds_succ _ _) h'
              (remains_white _ _ _ _ hv) hv'
            aesop
      | .MR j' =>
          have : Even (maximalMatching.rounds N f t v).1 ∧ j = j' := by
            rw [nextVector_white_MR N v _ (Algorithm.rounds_succ _ _)
              (remains_white _ _ _ _ hv) hv'] at h
            aesop
          obtain ⟨ht, rfl⟩ := this
          cases t
          case zero =>
            simp [Algorithm.rounds_zero, initialVector_2_2] at hv'
            aesop
          rename_i t
          rw [maximalMatching_round_count] at ht
          case h =>
            rw [not_mem_stoppingStates_iff, hv']
            simp
          simp only [Nat.even_add_one] at ht
          have hv'' := prevVector_MR N f v t hv'
          have hu : f u = true := by simpa [hv] using hf v u (hvj ▸ N.ofPort_adj _)
          have h₂ : maximalMatching.rounds N f t v ∉ maximalMatching.stoppingStates := by
            rw [not_mem_stoppingStates_iff, hv'']
            simp
          rw [maximalMatching.rounds_succ, Algorithm.nextVector,
            Algorithm.fullReceive_not_stoppingState _ h₂, maximalMatching_receive,
            maximalMatching_round_count N f t v h₂, if_neg ht, remains_white N f t v hv] at hv'
          simp only [hv''] at hv'
          split at hv'
          case isFalse => cases hv'
          case isTrue h₃ =>
            simp only [EdgeState.MR.injEq, Fin.val_eq_val] at hv'
            have h₄ : j ∈ Finset.univ.filter
                fun x => maximalMatching.messageRecd N (maximalMatching.rounds N f t) v x =
                  Msg.Accept := by
              rw [←hv']
              exact Finset.min'_mem _ _
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₄
            have h₅ : (maximalMatching.rounds N f t u).2.2 = .UR := by
              rw [messageRecd_odd_white N f hf _ _ ht rfl _ hv] at h₄
              split at h₄
              case h_1 h => rwa [hvj] at h
              case h_2 => cases h₄
              case h_3 => cases h₄
              case h_4 => cases h₄
            obtain ⟨M, X, hMX⟩ := remains_black N f t u hu
            simp only [messageRecd_odd_white N f hf _ _ ht rfl _ hv, hvj, h₅, hMX] at h₄
            simp only [ite_eq_left_iff, not_exists, imp_false, not_forall, Decidable.not_not] at h₄
            obtain ⟨hM, hi⟩ := h₄
            rw [reversePort_of_ofPort _ hvj hui] at hi
            have h₇ : maximalMatching.rounds N f t u ∉ maximalMatching.stoppingStates := by
              rw [not_mem_stoppingStates_iff, h₅]
              simp
            have' h₆ := nextVector_black_UR_odd_nonemptyM N u (Algorithm.rounds_succ _ _)
              (by rwa [maximalMatching_round_count _ _ _ _ h₇]) hMX h₅ hM
            rw [←hi] at h₆
            rw [nextVector_MS N u _ (Algorithm.rounds_succ _ _) h₆]

theorem same_matches_bw_aux (f : V → Bool)
    (hf : f ∈ (Problem.Colouring Bool).valid V N) (t : ℕ)
    (u v : V) (i : Fin (N.degree u)) (j : Fin (N.degree v))
    (hvj : N.ofPort v j = u) (hui : N.ofPort u i = v)
    (hv : f v = false)
    (h : (maximalMatching.rounds N f t u).2.2 = EdgeState.MS i) :
    (maximalMatching.rounds N f t v).2.2 = EdgeState.MR j ∨
    (maximalMatching.rounds N f t v).2.2 = EdgeState.MS j := by
  have hu : f u = true := by simpa [hv] using hf v u (hvj ▸ N.ofPort_adj _)
  induction t with
  | zero =>
      simp [Algorithm.rounds_zero, initialVector_2_2, hu, ite_eq_iff] at h
  | succ t ih =>
       match hv' : (maximalMatching.rounds N f t u).2.2 with
       | .US => simp [nextVector_US N _ (Algorithm.rounds_succ _ _) hv'] at h
       | .MR i' => cases black_not_MR N f u hu t _ rfl ⟨_, hv'⟩
       | .MS i' =>
            simp only [nextVector_MS N _ _ (Algorithm.rounds_succ _ _) hv'] at h
            cases h
            cases ih hv' with
            | inl h =>
                rw [nextVector_white_MR N v _ (Algorithm.rounds_succ _ _)
                  (remains_white _ _ _ _ hv) h]
                simp [em']
            | inr h =>
                right
                rw [nextVector_MS N v _ (Algorithm.rounds_succ _ _) h]
       | .UR =>
            have h₁ : maximalMatching.rounds N f t u ∉ maximalMatching.stoppingStates := by
              simp [not_mem_stoppingStates_iff, hv']
            obtain ⟨M, X, hM⟩ := remains_black N f t u hu
            rw [maximalMatching.rounds_succ, Algorithm.nextVector,
              Algorithm.fullReceive_not_stoppingState _ h₁, maximalMatching_receive,
              maximalMatching_round_count _ _ _ _ h₁, hM] at h
            simp only [hv'] at h
            have h₂ : ¬ Even t := by
              intro h₂
              rw [if_pos h₂] at h
              simp only at h
            have h₃ : M.Nonempty := by
              by_contra! h₃
              rw [if_neg h₂, dif_neg h₃] at h
              dsimp at h
              simp [ite_eq_iff] at h
            simp only [if_neg h₂, dif_pos h₃, EdgeState.MS.injEq] at h
            cases t
            case zero => simp at h₂
            rename_i t
            simp only [Nat.even_add_one, Decidable.not_not] at h₂
            have h₅ := prevVector_UR N f u _ hv'
            obtain ⟨X', hX'⟩ := black_UR_even_has_M_empty N f u hu t h₂ _ rfl h₅
            have h₄ : maximalMatching.rounds N f t u ∉ maximalMatching.stoppingStates := by
              simp [h₅]
            have hMX' := hM
            rw [maximalMatching.rounds_succ, Algorithm.nextVector,
              Algorithm.fullReceive_not_stoppingState _ h₄, maximalMatching_receive,
              maximalMatching_round_count _ _ _ _ h₄, if_pos h₂, hX'] at hM
            simp only [h₅, Finset.empty_union] at hM
            simp only [ColourState.black.injEq] at hM
            replace hM := hM.1
            have h₆ : Fin.valEmbedding i ∈ M := by
              simp only [Fin.valEmbedding_apply]
              rw [←h]
              exact Finset.min'_mem _ _
            have h₈ := h₆
            simp only [Finset.mem_map', Finset.mem_filter, Finset.mem_univ, true_and, ←hM] at h₆
            have h₇ : (maximalMatching.rounds N f t v).2.2 = .UR := by
              rw [messageRecd_even_black N f hf _ t h₂ rfl u hu i] at h₆
              simp only [hui] at h₆
              split at h₆
              case h_1 => assumption
              case h_2 => cases h₆
              case h_3 => cases h₆
              case h_4 => cases h₆
            obtain ⟨M', X', heq, hMX''⟩ := black_UR_odd_M_value N f hf u hu (t + 1)
              (by simp [parity_simps, *]) _ rfl hv'
            simp only [add_tsub_cancel_right] at hMX''
            simp only [hMX'] at heq
            cases heq
            have h₉ : (j : ℕ) = t / 2 := by
              have := hMX'' h₈
              simp only [Finset.mem_map', Finset.mem_filter, Finset.mem_univ, true_and] at this
              rw [reversePort_of_ofPort _ hui hvj] at this
              exact this
            have h₁₀ : (maximalMatching.rounds N f (t + 1) v).2.2 = .UR := by
              have : (maximalMatching.rounds N f t v).1 = t := by
                rw [maximalMatching_round_count]
                simp [h₇]
              rw [nextVector_white_UR_even N v (Algorithm.rounds_succ _ _) (this.symm ▸ h₂)
                (remains_white _ _ _ _ hv) h₇, this, ←h₉, if_pos]
              exact Fin.isLt _
            have h₁₁ := messageRecd_odd_white N f hf _ (t + 1) (by simp [parity_simps, *]) rfl v
              hv j
            simp only [hvj, hv', hMX', h₃, exists_true_left, reversePort_of_ofPort _ hvj hui, h,
              reduceIte] at h₁₁
            have : ∃ j', (maximalMatching.rounds N f (t + 2) v).2.2 = .MR j' := by
              have : maximalMatching.rounds N f (t + 1) v ∉ maximalMatching.stoppingStates := by
                rw [not_mem_stoppingStates_iff, h₁₀]
                simp
              rw [Algorithm.rounds_succ, Algorithm.nextVector,
                Algorithm.fullReceive_not_stoppingState _ this, maximalMatching_receive,
                maximalMatching_round_count _ _ _ _ this, if_neg (by simp [parity_simps, *]),
                remains_white _ _ _ _ hv]
              simp only [h₁₀]
              rw [dif_pos ⟨j, by simp [h₁₁]⟩]
              simp
            obtain ⟨j', hj'⟩ := this
            have := white_even_MR_val N f hf v hv (t + 2) j' _ rfl hj'
            simp only [Nat.ofNat_pos, Nat.add_div_right, Nat.succ_eq_add_one,
              add_tsub_cancel_right] at this
            left
            rw [hj', this.1, h₉]

theorem same_matches_bw (f : V → Bool)
    (hf : f ∈ (Problem.Colouring Bool).valid V N) (t : ℕ) (ht : maximalMatching.stoppedBy N f t)
    (u v : V) (i : Fin (N.degree u)) (j : Fin (N.degree v))
    (hvj : N.ofPort v j = u) (hui : N.ofPort u i = v)
    (hv : f v = false)
    (h : (maximalMatching.rounds N f t u).2.2 = EdgeState.MS i) :
    (maximalMatching.rounds N f t v).2.2 = EdgeState.MS j := by
  refine (same_matches_bw_aux N f hf t u v i j hvj hui hv h).resolve_left ?_
  intro h'
  simpa [mem_stoppingStates_iff, h'] using ht v

theorem same_matches (f : V → Bool)
    (hf : f ∈ (Problem.Colouring Bool).valid V N) (t : ℕ) (h : maximalMatching.stoppedBy N f t)
    (u v : V) (i : Fin (N.degree u)) (j : Fin (N.degree v))
    (hvj : N.ofPort v j = u) (hui : N.ofPort u i = v)
    (hv : f v = false) :
    (maximalMatching.rounds N f t v).2.2 = EdgeState.MS j ↔
      (maximalMatching.rounds N f t u).2.2 = EdgeState.MS i :=
  ⟨same_matches_wb _ _ hf _ _ _ _ _ hvj hui hv,
   same_matches_bw _ _ hf _ h _ _ _ _ hvj hui hv⟩

lemma encodes_matching (f : V → Bool) (hf : f ∈ (Problem.Colouring Bool).valid V N) (t : ℕ)
    (h : maximalMatching.stoppedBy N f t) :
    maximalMatching.outputAt N f t h ∈ Problem.Matching.valid V N := by
  dsimp [Problem.Matching, Problem.EdgeSubset]
  intro v
  constructor
  case left =>
    intro i hi
    have : (maximalMatching.rounds N f t v).2.2 = .MS i := by
      simp only [Option.getM_set_iff, Option.mem_def] at hi
      rw [outputAt_eq_some_iff] at hi
      exact hi
    exact MS_bound N f hf _ _ _ _ rfl this
  case right =>
    intro j
    simp only [Option.getM_set_iff, Option.mem_def, outputAt_eq_some_iff]
    set u : V := N.ofPort v j
    set i : Fin (N.degree u) := N.reversePort v j
    have hui : N.ofPort u i = v := by simp [u, i]
    change (maximalMatching.rounds _ _ _ v).2.2 = _ ↔
           (maximalMatching.rounds _ _ _ u).2.2 = _
    wlog hv : f v = false generalizing u v
    case inr =>
      have hu : f u = false := by simpa [u, hv] using hf v u (N.ofPort_adj _)
      rw [this u i (by simp) hu, reversePort_of_ofPort _ hui rfl, hui]
    exact same_matches N f hf _ h _ _ _ _ rfl hui hv

theorem adj_not_US (f : V → Bool)
    (hf : f ∈ (Problem.Colouring Bool).valid V N) (t : ℕ)
    (u v : V) (i : Fin (N.degree u)) (j : Fin (N.degree v))
    (hvj : N.ofPort v j = u) (hui : N.ofPort u i = v)
    (hv : f v = false)
    (hun : (maximalMatching.rounds N f t u).2.2 = .US)
    (hvn : (maximalMatching.rounds N f t v).2.2 = .US) : False := by
  have hu : f u = true := by simpa [hv] using hf v u (hvj ▸ N.ofPort_adj _)
  have ht : 2 * N.degree v < t := lt_of_not_le fun h => white_not_US N f v hv t h hvn
  match h₁ : (maximalMatching.rounds N f (2 * j + 1) u).2.2 with
    | .MR _ => exact black_not_MR N f u hu (2 * j + 1) _ rfl ⟨_, h₁⟩
    | .MS _ =>
        have : 2 * j + 1 ≤ t := by omega
        rw [maximalMatching.rounds_eq_of_mem_stoppingStates N f this u (by simp [h₁]), hun] at h₁
        simp at h₁
    | .US =>
        have : ∃ k < 2 * (j : ℕ) + 1, (maximalMatching.rounds N f k u).2.2 = .UR ∧
            (maximalMatching.rounds N f (k + 1) u).2.2 = .US := by
          let k := Nat.findGreatest (fun z => (maximalMatching.rounds N f z u).2.2 = .UR) (2 * j)
          have hk : (maximalMatching.rounds N f k u).2.2 = .UR := by
            refine Nat.findGreatest_spec (P := fun z => (maximalMatching.rounds N f z u).2.2 = .UR)
              (Nat.zero_le _) ?_
            simp only [Algorithm.rounds_zero, initialVector_2_2, hu, true_and, ite_eq_right_iff,
              imp_false, ← pos_iff_ne_zero]
            rw [N.degree_pos_iff_exists_adj]
            exact ⟨N.ofPort u i, by simp⟩
          have : k ≤ 2 * j := Nat.findGreatest_le _
          refine ⟨k, by omega, hk, ?_⟩
          match h₂ : (maximalMatching.rounds N f (k + 1) u).2.2 with
          | .US => rfl
          | .MR _ => cases black_not_MR N f u hu (k + 1) _ rfl ⟨_, h₂⟩
          | .MS _ =>
              rw [maximalMatching.rounds_eq_of_mem_stoppingStates N f
                (show k + 1 ≤ 2 * j + 1 by omega) u (by simp [h₂]), h₁] at h₂
              cases h₂
          | .UR =>
              cases lt_or_eq_of_le this
              case inr h => rw [←h₂, h, h₁]
              case inl h => cases Nat.findGreatest_is_greatest (Nat.lt_succ_self k) (by omega) h₂
        obtain ⟨k, hk, h₂, h₃⟩ := this
        have h₄ := black_US_empty_X N f (k + 1) u hu h₃
        have h₅ : (maximalMatching.rounds N f k u).2.1 = .black ∅ ∅ := by
          obtain ⟨M, X, hMX⟩ := remains_black N f k u hu
          have ht : ¬ Even (maximalMatching.rounds N f k u).1 := by
            intro hk'
            simp only [nextVector_black_UR_even N u (Algorithm.rounds_succ _ _) hk' hMX h₂] at h₃
          have hM : ¬M.Nonempty := by
            intro hM
            simp only [nextVector_black_UR_odd_nonemptyM N u (Algorithm.rounds_succ _ _) ht hMX
              h₂ hM] at h₃
          have hX : ¬X.Nonempty := by
            intro hX
            rw [nextVector_black_UR_odd_nonemptyX N u (Algorithm.rounds_succ _ _) ht hMX
              h₂ hM hX] at h₃
            simp at h₃
          simp only [Finset.not_nonempty_iff_eq_empty] at hM hX
          rw [hMX, hM, hX]
        have : k < t := by omega
        have h₆ : ∀ (i : ℕ), (maximalMatching.rounds N f k v).2.2 ≠ EdgeState.MS i := by
          intro i hi
          rw [maximalMatching.rounds_eq_of_mem_stoppingStates N f this.le v (by simp [hi]),
            hvn] at hi
          cases hi
        have h₇ : ∀ (i : ℕ), (maximalMatching.rounds N f k v).2.2 ≠ EdgeState.MR i := by
          intro i hi
          have hk : Even k := by
            by_contra hk
            exact white_odd_not_MR N f v hv _ hk _ rfl ⟨_, hi⟩
          have : (maximalMatching.rounds N f (k + 1) v).2.2 = EdgeState.MS i := by
            rw [nextVector_white_MR N v _ (Algorithm.rounds_succ _ _) (remains_white _ _ _ _ hv)
              hi, if_pos]
            rwa [maximalMatching_round_count _ _ _ _ (by simp [hi])]
          rw [maximalMatching.rounds_eq_of_mem_stoppingStates N f (show k + 1 ≤ t by omega) v
            (by simp [this]), hvn] at this
          cases this
        obtain ⟨M, X, hM, hMX⟩ := not_send_on_no_match N f hf v u hv hu i hui k h₂ h₆ h₇
        rw [hMX] at h₅
        cases h₅
        simp at hM
    | .UR =>
        obtain ⟨M, X, hMX', hMX⟩ := invariant N f hf v u hv hu j hvj i hui h₁
        have h₂ : ∀ i : ℕ, (maximalMatching.rounds N f (2 * j + 1) v).2.2 ≠ .MS i := by
          intro i hi
          rw [maximalMatching.rounds_eq_of_mem_stoppingStates N f (show 2 * j + 1 ≤ t by omega) v
            (by simp [hi]), hvn] at hi
          cases hi
        have h₃ : ∀ i : ℕ, (maximalMatching.rounds N f (2 * j + 1) v).2.2 ≠ .MR i := by
          intro i hi
          exact white_odd_not_MR N f v hv _ (by simp [parity_simps]) _ rfl ⟨_, hi⟩
        obtain ⟨M', X', hM, hMX''⟩ :=
          not_send_on_no_match N f hf v u hv hu i hui (2 * j + 1) h₁ h₂ h₃
        rw [hMX''] at hMX
        cases hMX
        replace hMX' := hMX'.resolve_left (by simp [hM])
        have h₄ : ¬Even (maximalMatching.rounds N f (2 * ↑j + 1) u).1 := by
          rw [maximalMatching_round_count _ _ _ _ (by simp [h₁])]
          simp [parity_simps]
        have h₅ := nextVector_black_UR_odd_nonemptyM N u (Algorithm.rounds_succ _ _) h₄ hMX''
          h₁ hMX'
        have h₆ : 2 * j + 1 + 1 ≤ t := by omega
        rw [maximalMatching.rounds_eq_of_mem_stoppingStates N f h₆ u (by simp [h₅]), hun] at h₅
        cases h₅

lemma encodes_maximal_matching (f : V → Bool) (hf : f ∈ (Problem.Colouring Bool).valid V N) (t : ℕ)
    (h : maximalMatching.stoppedBy N f t) :
    maximalMatching.outputAt N f t h ∈ Problem.MaximalMatching.valid V N := by
  simp only [Problem.MaximalMatching, Set.mem_inter_iff, encodes_matching N f hf _ h, true_and,
    Set.mem_setOf_eq, ne_eq, outputAt_eq_none_iff]
  intro v hv j hj
  set u : V := N.ofPort v j
  set i : Fin (N.degree u) := N.reversePort v j
  have hui : N.ofPort u i = v := by simp [u, i]
  wlog hv' : f v = false generalizing u v
  case inr =>
    have hu : f u = false := by simpa [u, hv'] using hf v u (N.ofPort_adj _)
    exact this u hj i (by simp [*]) (by simp) hu
  exact adj_not_US N f hf _ _ _ _ _ rfl hui hv' hj hv

open scoped Classical

/--
The maximal matching algorithm solves the maximal matching problem given a 2-colouring as input on
all graphs in time 2Δ+1.
-/
theorem maximalMatching_solvesProblemInTime :
    solvesProblemInTime maximalMatching (fun _ => Set.univ)
      (Problem.Colouring Bool)
      Problem.MaximalMatching
      (fun G => 2 * G.maxDegree + 1) := fun N f _ hf =>
  ⟨2 * N.maxDegree + 1, stoppedBy N f hf, le_rfl, encodes_maximal_matching _ _ hf _ _⟩

end MaximalBipartiteMatching

end sec_3_5
