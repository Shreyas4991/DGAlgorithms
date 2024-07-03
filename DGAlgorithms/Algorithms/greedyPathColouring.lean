import DGAlgorithms.ForMathlib.SimpleGraph
import DGAlgorithms.Algorithm

section sec_3_4

open SimpleGraph

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

namespace ThreeColourPath

variable {V : Type*} [Fintype V] [DecidableEq V] {N : PortNumbered V} [DecidableRel N.Adj]

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

@[simp] lemma messageRecd (curr : V → ℕ) (v : V) (i : Fin (N.degree v)) :
    colouringPathAlgorithm.messageRecd N curr v i = curr (N.ofPort v i) := rfl

-- the collection of received messages is the set of colours of the neighbours
lemma image_messageRecd (curr : V → ℕ) (v : V) :
    (Finset.univ.image (colouringPathAlgorithm.messageRecd N curr v)) =
      (N.neighborFinset v).image curr := by
  ext i
  simp [PortNumbered.exists_ports]

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
  rw [N.forall_ports]
  simpa

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
  have hM : M.card ≤ 2 := by
    refine Finset.card_image_le.trans ?_
    simpa only [card_neighborFinset_eq_degree, PortNumbered.degree_eq]
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
  refine colour_decreases _ _ _ ((N.degree_le_maxDegree v).trans h)

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
    ·
      convert (N.degree_le_maxDegree _).trans ?_
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
    solvesProblem colouringPathAlgorithm (fun V => {G | G.IsPath})
      (Problem.Colouring ℕ)
      (Problem.Colouring ({0, 1, 2} : Finset ℕ)) := by
  rintro V _ N f hN hf
  classical
  dsimp at hN
  refine ⟨maxColour f - 2, stops f hf hN.maxDegree (maxColour f) le_rfl, ?_⟩
  rw [Problem.colouring_subtype_iff, Algorithm.outputAt, coe_comp_outputs_apply]
  exact all_valid _ _ hf _

end ThreeColourPath

end sec_3_4
