import Mathlib
import DGAlgorithms.Network.PNNetwork
import DGAlgorithms.Models.MessagePassing.PortNumbering

namespace DGAlgorithms

inductive MMMsg
| none_reject
| propose_accept
| stop

structure MMState (P : Type*) where
  turn : Bool
  role : Bool
  neighbors : Set P
  matched : Option P


open Classical in
noncomputable
def bipartiteMatching (P : Type*) : PNAlgorithm P Bool (Option P) where
  State := fun _ ↦ MMState P
  Msg := MMMsg
  init := fun p role ↦ ⟨false, role, p, none⟩
  send := fun ⟨turn, role, neigh, matched⟩ ↦
    match turn, role, matched with
    | _, _, some q =>
      -- Respond to a proposal, and keep confirming our love
      fun p ↦ if p = q then .propose_accept else .stop
    | false, false, none =>
      -- Send a proposal
      if h : neigh.Nonempty then
        fun p ↦ if p = h.choose then .propose_accept else .none_reject
      else
        fun _ ↦ .none_reject
    | _, _, _ =>
      -- Not our turn to act, or we have already been matched
      fun _ ↦ .none_reject
  recv := fun ⟨turn, role, neigh, matched⟩ msg ↦
    if hn : neigh = ∅ then
      ⟨turn, role, ∅, matched⟩
    else
      match turn, role, matched with
      | _, _, some _ =>
         -- We have been matched already, let's keep it at that
         ⟨!turn, role, ∅, matched⟩
      | true, false, none =>
        -- Last round, we sent a proposal: remove the node from the set of neighbors
        if h : ∃ p, msg p = .propose_accept then
          ⟨!turn, role, ∅, some (h.choose)⟩
        else
          have hn : neigh.Nonempty := Set.nonempty_iff_ne_empty.mpr hn
          ⟨!turn, role, neigh \ {hn.choose}, none⟩
      | false, true, none =>
        -- It is our turn to accept or reject a proposal
        if h : ∃ p, msg p = .propose_accept then
          ⟨!turn, role, ∅, some (h.choose)⟩
        else if ∀ p, msg p = .stop then
          ⟨!turn, role, ∅, none⟩
        else
          ⟨!turn, role, neigh, none⟩
      | _, _, _ =>
        ⟨!turn, role, neigh, none⟩
  output := fun ⟨_turn, _role, _neigh, matched⟩ ↦
    matched

def PNNetwork.PartitionWith {α : Type*} (N : PNNetwork V P) (i : V → I) (f : I → α) : Prop := ∀ v u, N.Adj v u → f (i v) ≠ f (i u)
def PNNetwork.BipartiteWith (N : PNNetwork V P) (i : V → I) (f : I → α) : Prop := N.PartitionWith i f

-- def bipartiteMatching.Stopping : ∀ p : Set P, (bipartiteMatching P).State p → Prop := fun _ ⟨_turn, _role, neigh, _matched⟩ ↦ neigh = ∅
def MMState.Stopping : MMState P → Prop := fun s ↦ s.neighbors = ∅

@[simp]
lemma bipartiteMatching.Stopping_idempotent {p : Set P} :
    ∀ s : (bipartiteMatching P).State p, ∀ msg : p → (bipartiteMatching P).Msg,
      s.Stopping → (bipartiteMatching P).recv s msg = s := by
        intro s msg
        unfold MMState.Stopping
        dsimp [bipartiteMatching]
        intro hn
        rw [hn]
        simp
        rw [← hn]
        rfl

instance : PNAlgorithm.WithStopping (bipartiteMatching P) where
  Stopping := MMState.Stopping
  lawfull_stopping := bipartiteMatching.Stopping_idempotent

@[simp]
lemma bipartiteMatching.Stopping_to_Stopping {p : Set P} :
    ∀ s : (bipartiteMatching P).State p, ∀ msg : p → (bipartiteMatching P).Msg,
      s.Stopping → ((bipartiteMatching P).recv s msg).Stopping := by simp_all

@[simp]
lemma bipartiteMatching.NotStopping_turns_alternate {p : Set P} :
    ∀ s : (bipartiteMatching P).State p, ∀ msg : p → (bipartiteMatching P).Msg,
      ¬s.Stopping → ((bipartiteMatching P).recv s msg).turn = !s.turn := by
        intro s msg notstop
        dsimp [MMState.Stopping] at notstop
        simp [notstop, bipartiteMatching]
        split
        repeat (any_goals split)
        all_goals (rfl)

@[simp]
lemma bipartiteMatching_neigh_subset  {p : Set P} :
  ∀ s : (bipartiteMatching P).State p, ∀ msg : p → (bipartiteMatching P).Msg,
    ((bipartiteMatching P).recv s msg).neighbors ⊆ s.neighbors := by
      intro s msg
      simp [bipartiteMatching]
      split
      repeat (any_goals split)
      all_goals (simp)

lemma bipartiteMatching_matched_stopped {p : Set P} :
  ∀ s : (bipartiteMatching P).State p, ∀ msg : p → (bipartiteMatching P).Msg,
  ¬(((bipartiteMatching P).recv s msg).matched = none) → ((bipartiteMatching P).recv s msg).neighbors = ∅ := by
  intro s msg hmatch
  simp only [bipartiteMatching] at *
  split
  · rfl
  · split
    repeat (any_goals split)
    any_goals (rfl) -- technically unneeded, but makes the amount of goals smaller
    all_goals (split at hmatch)
    repeat (any_goals split at hmatch)
    any_goals (contradiction)
    all_goals (simp_all) -- only way I found to get around the ''split does not give me names'' issue

lemma bipartiteMatching_matched_remains {p : Set P} :
  ∀ s : (bipartiteMatching P).State p, ∀ msg : p → (bipartiteMatching P).Msg,
  ¬(s.matched=none) → s.matched = ((bipartiteMatching P).recv s msg).matched := by
    intro s msg notmatch
    simp only [bipartiteMatching]
    split; rfl; split
    any_goals (split; contradiction)
    · rfl
    · contradiction
    · contradiction
    · apply Option.isSome_iff_ne_none.mpr at notmatch
      aesop

lemma bipartiteMatching_not_unmatching {p : Set P} :
  ∀ s : (bipartiteMatching P).State p, ∀ msg : p → (bipartiteMatching P).Msg,
  ¬(s.matched=none) → ¬(((bipartiteMatching P).recv s msg).matched=none) := by
    intro s msg nonmatch
    rw [← bipartiteMatching_matched_remains s msg nonmatch]
    assumption

lemma bipartiteMatching_role_remains {p : Set P} :
  ∀ s : (bipartiteMatching P).State p, ∀ msg : p → (bipartiteMatching P).Msg,
  s.role = ((bipartiteMatching P).recv s msg).role := by
    intro s msg
    simp only [bipartiteMatching]
    split;
    repeat (any_goals (split))
    all_goals rfl

-- this is absolutely awful!
lemma bipartiteMatching_proposing_decreases {p : Set P} :
   ∀ s : (bipartiteMatching P).State p, ∀ msg : p → (bipartiteMatching P).Msg,
  ¬s.role → s.neighbors.Nonempty → s.turn → ((bipartiteMatching P).recv s msg).neighbors ⊂ s.neighbors := by
    intro s msg hrole hnonempty hturn
    apply Set.ssubset_iff_exists.mpr
    constructor
    · exact bipartiteMatching_neigh_subset s msg
    · cases ((bipartiteMatching P).recv s msg).neighbors.eq_empty_or_nonempty with
      | inl h =>
        obtain ⟨x,hx⟩ := Set.nonempty_def.mp hnonempty
        use x
        simp [hx,h]
      | inr h =>
        apply Set.nonempty_iff_ne_empty.mp at hnonempty
        apply Set.nonempty_iff_ne_empty.mp at h
        simp only [bipartiteMatching,hnonempty,dite_false] at h
        simp only [bipartiteMatching,hnonempty,dite_false]
        repeat split
        repeat split at h
        any_goals (contradiction)
        · simp_all
        · have hproof := bipartiteMatching._proof_1 P s.neighbors (Eq.mpr_not (eq_false hnonempty) not_false)
          use (Exists.choose hproof)
          have hx := Exists.choose_spec hproof
          simp_all
        · split at h; contradiction
          all_goals (split)
          any_goals (contradiction);
          · simp_all
          have hproof := bipartiteMatching._proof_1 P s.neighbors (Eq.mpr_not (eq_false hnonempty) not_false)
          use (Exists.choose hproof)
          have hx := Exists.choose_spec hproof
          all_goals (simp_all)
        · have unmatch : ∀ (val : P), s.matched = some val → False := by assumption
          rw [← Option.eq_none_iff_forall_ne_some] at unmatch
          simp_all

variable {V P : Type*} (N : PNNetwork V P)

lemma left_or_not_left_and_right (a b : Prop) : a ∨ b → a ∨ (¬a ∧ b) := by tauto

lemma bipartiteMatching.turn_eq_odd_k (N : PNNetwork V P) (i : V → Bool) :
    ∀ v : V, ((bipartiteMatching P).execFor N i k v).Stopping ∨ ((bipartiteMatching P).execFor N i k v).turn = Odd k := by
  intro v
  induction k
  case zero => simp [bipartiteMatching]
  case succ n hi =>
    apply left_or_not_left_and_right at hi
    cases' hi with hi hi
    · left
      rw [PNAlgorithm.execFor_succ]
      apply (bipartiteMatching P).step_Stopping_to_Stopping
      assumption
    · right
      obtain ⟨hs, hi⟩ := hi
      rw [Nat.odd_add_one, ←hi, PNAlgorithm.execFor_succ]
      generalize (bipartiteMatching P).execFor N i n = x at *
      simp [bipartiteMatching.NotStopping_turns_alternate _ _ hs]

lemma bipartiteMatching_step_neigh_subset (cfg : PNAlgorithm.CfgOn (bipartiteMatching P) N) :
   ∀ v : V, (((bipartiteMatching P).step N) cfg v).neighbors ⊆ (cfg v).neighbors := by
   intro v
   rw [((bipartiteMatching P).step_eq_recv_of N cfg) v]
   simp

lemma bipartiteMatching.active_neigh_ssubset (cfg : PNAlgorithm.CfgOn (bipartiteMatching P) N) :
    ∀ v : V, ¬(cfg v).role → (cfg v).neighbors.Nonempty → (((bipartiteMatching P).step N)^[2] cfg v).neighbors ⊂ (cfg v).neighbors := by
    intro v hrole hnonempty
    -- somehow, using repeat below creates new goals.
    unfold Nat.iterate; unfold Nat.iterate; unfold Nat.iterate
    rw [(bipartiteMatching P).step_eq_recv_of,(bipartiteMatching P).step_eq_recv_of]
    let fmsg := (PNAlgorithm.CfgOn'.stepComm (bipartiteMatching P) (PNAlgorithm.CfgOn.stepSend (bipartiteMatching P) cfg) v).1
    let nstate := (bipartiteMatching P).recv (cfg v) fmsg
    let smsg := (PNAlgorithm.CfgOn'.stepComm (bipartiteMatching P) (PNAlgorithm.CfgOn.stepSend (bipartiteMatching P) ((bipartiteMatching P).step N cfg)) v).1
    by_cases hempty: nstate.neighbors.Nonempty
    · by_cases hturn: (cfg v).turn
      · have hdec := bipartiteMatching_proposing_decreases (cfg v) fmsg hrole hnonempty hturn
        have hsub := bipartiteMatching_neigh_subset nstate smsg
        exact Set.ssubset_of_subset_of_ssubset hsub hdec
      · have hsub := bipartiteMatching_neigh_subset (cfg v) fmsg
        have not_stop : ¬(cfg v).Stopping := by unfold MMState.Stopping; exact Set.nonempty_iff_ne_empty.mp hnonempty
        have next_turn := bipartiteMatching.NotStopping_turns_alternate (cfg v) fmsg not_stop
        simp only [hturn, Bool.not] at next_turn
        rw [bipartiteMatching_role_remains (cfg v) ((PNAlgorithm.CfgOn'.stepComm (bipartiteMatching P) (PNAlgorithm.CfgOn.stepSend (bipartiteMatching P) cfg) v).1)] at hrole
        have hdec := bipartiteMatching_proposing_decreases nstate smsg hrole hempty next_turn
        exact Set.ssubset_of_ssubset_of_subset hdec hsub
    · apply Set.not_nonempty_iff_eq_empty.mp at hempty
      have hdec := Set.empty_ssubset.mpr hnonempty
      rw [← hempty] at hdec
      have hsub := bipartiteMatching_neigh_subset nstate smsg
      exact Set.ssubset_of_subset_of_ssubset hsub hdec

-- lemma bipartiteMatching.stopped_unmatched_node_is_locally_finite

-- lemma bipartiteMatching.is_matching

-- lemma bipartiteMatching.matching_is_maximal
