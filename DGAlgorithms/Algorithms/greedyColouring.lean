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

namespace GreedyColour

variable {V : Type*} [Fintype V] [DecidableEq V] {N : PortNumbered V} [DecidableRel N.Adj]
variable {n : ℕ}

@[simps!]
def greedyColouring (n : ℕ) : Algorithm ℕ ℕ ℕ (Finset.range (n + 1)) :=
  Algorithm.subtypeMk ℕ ℕ ℕ
    (Finset.range (n + 1))
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
    maxColour f ≤ x ↔ ∀ v, f v ≤ x := by simp [maxColour]

lemma le_maxColour [Fintype V] (f : V → ℕ) (x : V) :
    f x ≤ maxColour f := Finset.le_sup (by simp)

lemma stoppingStates : (greedyColouring n).stoppingStates = (Finset.range (n + 1) : Finset ℕ) :=
  Algorithm.subtypeMk_stoppingStates

lemma initialVector (f : V → ℕ) : (greedyColouring n).initialVector N f = f := rfl

lemma coe_outputs_apply (curr : V → ℕ) (h : (greedyColouring n).isStopped curr) (v : V) :
    ((greedyColouring n).outputs curr h v : ℕ) = curr v :=
  Algorithm.coe_subtypeMk_outputs_apply _ _

lemma coe_comp_outputs_apply (curr : V → ℕ) (h : (greedyColouring n).isStopped curr) :
    Subtype.val ∘ (greedyColouring n).outputs curr h = curr :=
  funext (coe_outputs_apply _ _)

@[simp] lemma messageRecd (curr : V → ℕ) (v : V) (i : Fin (N.degree v)) :
    (greedyColouring n).messageRecd N curr v i = curr (N.ofPort v i) := rfl

-- the collection of received messages is the set of colours of the neighbours
lemma image_messageRecd (curr : V → ℕ) (v : V) :
    (Finset.univ.image ((greedyColouring n).messageRecd N curr v)) =
      (N.neighborFinset v).image curr := by
  ext i
  simp [PortNumbered.exists_ports]

lemma nextVector_of_stopped (curr : V → ℕ) (v : V)
    (h : curr v ∈ (greedyColouring n).stoppingStates) :
    (greedyColouring n).nextVector N curr v = curr v :=
  Algorithm.nextVector_stopped _ _ _ h

-- in practice we know curr v ≠ curr w, but the proof works in the more general case too
lemma nextVector_of_not_local_max (curr : V → ℕ) (v w : V) (h₁ : N.Adj v w)
    (h₂ : curr v ≤ curr w) : (greedyColouring n).nextVector N curr v = curr v := by
  refine Algorithm.nextVector_eq_self _ _ _ ?_
  intro h₃
  rw [Algorithm.nextVector, Algorithm.fullReceive_not_stoppingState _ h₃,
    greedyColouring_receive, if_neg]
  simp only [not_forall, not_lt]
  refine ⟨N.toPort v w h₁, ?_⟩
  rwa [messageRecd, N.ofPort_toPort]

lemma nextVector_of_local_max (curr : V → ℕ) (v : V)
    (h₁ : curr v ∉ (greedyColouring n).stoppingStates)
    (h₂ : ∀ w, N.Adj v w → curr w < curr v) :
    (greedyColouring n).nextVector N curr v =
      smallestMissing ((N.neighborFinset v).image curr) := by
  rw [Algorithm.nextVector, Algorithm.fullReceive_not_stoppingState _ h₁,
    greedyColouring_receive, if_pos, image_messageRecd curr]
  rw [N.forall_ports]
  simpa

lemma mem_stoppingStates_iff_le {v : ℕ} :
    v ∈ (greedyColouring n).stoppingStates ↔ v ≤ n := by
  simp [stoppingStates, Nat.lt_add_one_iff]

lemma isStopped_iff_maxColour_le {curr : V → ℕ} :
    (greedyColouring n).isStopped curr ↔ maxColour curr ≤ n := by
  simp only [Algorithm.isStopped, mem_stoppingStates_iff_le, maxColour_le_iff]

lemma nextVector_lt_of_local_max (curr : V → ℕ) (v : V) (hv : N.degree v ≤ n)
    (h₁ : curr v ∉ (greedyColouring n).stoppingStates)
    (h₂ : ∀ w, N.Adj v w → curr w < curr v) :
    (greedyColouring n).nextVector N curr v < curr v := by
  rw [nextVector_of_local_max _ _ h₁ h₂]
  set M := (N.neighborFinset v).image curr
  have hM : M.card ≤ n := by
    refine Finset.card_image_le.trans ?_
    simpa using hv
  have : smallestMissing M ≤ n := smallestMissing_le_card.trans hM
  rw [mem_stoppingStates_iff_le, not_le] at h₁
  omega

lemma validColouring_aux (curr : V → ℕ) (v w : V) (h : N.Adj v w)
    (h₁ : curr v ∉ (greedyColouring n).stoppingStates)
    (h₂ : ∀ w, N.Adj v w → curr w < curr v) :
    (greedyColouring n).nextVector N curr v ≠ curr w := by
  intro h₃
  have h₄ := smallestMissing_spec ((N.neighborFinset v).image curr)
  rw [←nextVector_of_local_max curr v h₁ h₂, h₃] at h₄
  refine h₄ ?_
  simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset]
  exact ⟨w, h, rfl⟩

lemma validColouring (curr : V → ℕ) (v w : V) (h₁ : N.Adj v w) (h₂ : curr v ≠ curr w) :
    (greedyColouring n).nextVector N curr v ≠ (greedyColouring n).nextVector N curr w := by
  wlog h₄ : curr w < curr v generalizing v w
  · exact (this _ _ h₁.symm h₂.symm (lt_of_le_of_ne (le_of_not_lt h₄) h₂)).symm
  intro h₃
  rw [nextVector_of_not_local_max _ _ _ h₁.symm h₄.le] at h₃
  have h₅ : curr v ∉ (greedyColouring n).stoppingStates := by
    contrapose! h₂
    rw [←h₃, nextVector_of_stopped _ _ h₂]
  have h₆ : ∀ w, N.Adj v w → curr w < curr v := by
    contrapose! h₂
    obtain ⟨x, h₆, h₇⟩ := h₂
    rw [←h₃, nextVector_of_not_local_max curr v x h₆ h₇]
  exact validColouring_aux curr v w h₁ h₅ h₆ h₃

lemma validColouring' (curr : V → ℕ) (h : curr ∈ (Problem.Colouring _).valid V N) :
    (greedyColouring n).nextVector N curr ∈ (Problem.Colouring _).valid V N :=
  fun _ _ h' => validColouring _ _ _ h' (h _ _ h')

lemma colour_decreases (curr : V → ℕ) (v : V) (hv : N.degree v ≤ n) :
    (greedyColouring n).nextVector N curr v ≤ curr v := by
  by_contra! h₁
  have h₂ : curr v ∉ (greedyColouring n).stoppingStates := by
    intro h₂
    rw [nextVector_of_stopped _ _ h₂] at h₁
    exact lt_irrefl _ h₁
  have h₃ : ∀ w, N.Adj v w → curr w < curr v := by
    intro w h
    by_contra! h₃
    rw [nextVector_of_not_local_max curr _ _ h h₃] at h₁
    exact lt_irrefl _ h₁
  exact h₁.not_lt (nextVector_lt_of_local_max _ _ hv h₂ h₃)

lemma maxColour_decreases (curr : V → ℕ) (h : N.maxDegree ≤ n) :
    maxColour ((greedyColouring n).nextVector N curr) ≤ maxColour curr := by
  refine Finset.sup_mono_fun ?_
  simp only [Finset.mem_univ, true_implies]
  intro v
  refine colour_decreases _ _ ((N.degree_le_maxDegree v).trans h)

lemma maxColour_strict_decreases (curr : V → ℕ) (h : N.maxDegree ≤ n)
    (h₁ : curr ∈ (Problem.Colouring _).valid V N)
    (h₂ : ¬ (greedyColouring n).isStopped curr) :
    maxColour ((greedyColouring n).nextVector N curr) < maxColour curr := by
  rw [isStopped_iff_maxColour_le, not_le] at h₂
  have h₄ : ∀ x : V, curr x = maxColour curr →
      (greedyColouring n).nextVector N curr x < curr x := by
    intro x hx
    have : ∀ y : V, N.Adj x y → curr y < curr x := by
      intro y h₃
      refine lt_of_le_of_ne ?_ (h₁ x y h₃).symm
      rw [hx]
      exact le_maxColour _ _
    refine nextVector_lt_of_local_max _ _ ?_ ?_ this
    · exact (N.degree_le_maxDegree _).trans h
    · rwa [mem_stoppingStates_iff_le, not_le, hx]
  rw [maxColour, Finset.sup_lt_iff]
  rintro x -
  swap
  · simp only [bot_eq_zero']
    omega
  refine lt_of_le_of_ne ?_ ?_
  · exact (maxColour_decreases _ h).trans' (le_maxColour _ _)
  intro h₅
  have h₆ : curr x = maxColour curr := by
    have' := colour_decreases curr x (h.trans' (N.degree_le_maxDegree x))
    have : curr x ≤ maxColour curr := le_maxColour _ _
    omega
  have := h₄ x h₆
  omega

lemma all_valid (N : PortNumbered V) (f : V → ℕ)
    (hf : f ∈ (Problem.Colouring _).valid V N) (T : ℕ) :
    (greedyColouring n).rounds N f T ∈ (Problem.Colouring ℕ).valid V N := by
  induction T with
  | zero => exact hf
  | succ T ih =>
      rw [Algorithm.rounds_succ]
      refine validColouring' _ ih

lemma maxColour_rounds (h : N.maxDegree ≤ n)
    (f : V → ℕ) (hf : f ∈ (Problem.Colouring _).valid V N) (T : ℕ)
    (hf' : ¬ (greedyColouring n).isStopped ((greedyColouring n).rounds N f T)) :
    maxColour ((greedyColouring n).rounds N f T) + T ≤ maxColour f := by
  induction T with
  | zero => rw [Algorithm.rounds_zero, initialVector, add_zero]
  | succ T ih =>
      have : ¬ (greedyColouring n).isStopped ((greedyColouring n).rounds N f T) := by
        contrapose! hf'
        rw [Algorithm.rounds_succ]
        exact Algorithm.nextVector_isStopped _ _ _ hf'
      refine (ih this).trans' ?_
      rw [←add_assoc, add_right_comm, add_le_add_iff_right, Nat.add_one_le_iff,
        Algorithm.rounds_succ]
      exact maxColour_strict_decreases _ h (all_valid _ _ hf _) this

lemma stops (f : V → ℕ)
    (hf : f ∈ (Problem.Colouring ℕ).valid V N) (hd : N.maxDegree ≤ n)
    (x : ℕ) (hx : maxColour f ≤ x) :
    (greedyColouring n).stoppedBy N f (x - n) := by
  rcases le_or_lt x n with h | h
  · rw [tsub_eq_zero_of_le h, Algorithm.stoppedBy, Algorithm.rounds_zero, initialVector,
      isStopped_iff_maxColour_le]
    omega
  rw [Algorithm.stoppedBy]
  by_contra! h'
  have := maxColour_rounds hd _ hf _ h'
  rw [isStopped_iff_maxColour_le, not_le] at h'
  omega

open Classical in
lemma solvesColouringProblem (Δ : ℕ) :
    solvesProblem (greedyColouring Δ)
      (fun V => {G | ∃ (_ : Fintype V), G.maxDegree ≤ Δ})
      (Problem.Colouring ℕ)
      (Problem.Colouring (Finset.range (Δ + 1) : Finset ℕ)) := by
  rintro V _ N f hN hf
  simp only [Set.mem_setOf_eq] at hN
  obtain ⟨_, hΔ⟩ := hN
  refine ⟨maxColour f - Δ, ?_, ?_⟩
  · refine stops f hf ?_ (maxColour f) le_rfl
    convert hΔ
  rw [Problem.colouring_subtype_iff, Algorithm.outputAt, coe_comp_outputs_apply]
  exact all_valid _ _ hf _

end GreedyColour

end sec_3_4
