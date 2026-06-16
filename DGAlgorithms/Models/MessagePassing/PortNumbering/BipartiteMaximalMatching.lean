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
      -- | _, _, some q =>
      --   -- We have been matched already, let's keep it at that
      --   ⟨turn, role, ∅, some q⟩
      | true, false, none =>
        -- Last round, we sent a proposal: remove the node from the set of neighbors
        if h : ∃ p, msg p = .propose_accept then
          ⟨¬turn, role, ∅, some (h.choose)⟩
        else
          have hn : neigh.Nonempty := Set.nonempty_iff_ne_empty.mpr hn
          ⟨¬turn, role, neigh \ {hn.choose}, none⟩
      | false, true, none =>
        -- It is our turn to accept or reject a proposal
        if h : ∃ p, msg p = .propose_accept then
          ⟨¬turn, role, ∅, some (h.choose)⟩
        else if ∀ p, msg p = .stop then
          ⟨¬turn, role, ∅, none⟩
        else
          ⟨¬turn, role, neigh, none⟩
      | _, _, _ =>
        ⟨¬turn, role, neigh, none⟩
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

-- @[simp]
-- lemma bipartiteMatching.Stopping_to_Stopping {p : Set P} :
--     ∀ s : (bipartiteMatching P).State p, ∀ msg : p → (bipartiteMatching P).Msg,
--       s.Stopping → ((bipartiteMatching P).recv s msg).Stopping := by simp_all

@[simp]
lemma bipartiteMatching.NotStopping_turns_alternate {p : Set P} :
    ∀ s : (bipartiteMatching P).State p, ∀ msg : p → (bipartiteMatching P).Msg,
      ¬s.Stopping → ((bipartiteMatching P).recv s msg).turn = !s.turn := by
        intro s msg notstop
        dsimp [MMState.Stopping] at notstop
        simp [notstop, bipartiteMatching]
        split
        all_goals (try split)
        all_goals (try split)
        all_goals (try rfl)


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

lemma bipartiteMatching.active_neigh_ssubset (cfg : PNAlgorithm.CfgOn (bipartiteMatching P) N) :
    ∀ v : V, ¬(cfg v).role → (cfg v).neighbors.Nonempty → (((bipartiteMatching P).step N)^[2] cfg v).neighbors ⊂ (cfg v).neighbors := by
  sorry
  -- intro v hr h
  -- apply Set.ssubset_iff_exists.mpr
  -- constructor
  -- ·
  --   intro x a
  --   -- unfold bipartiteMatching.recv
  --   simp_all []

  --   -- aesop
  --   sorry
  -- · simp
  --   by_cases h : (cfg v).neighbors.Nonempty
  --   ·
  --     obtain ⟨a, h⟩ := h
  --     use a
  --     constructor; assumption
  --     -- simp [(bipartiteMatching P).recv]
  --     -- intro ha
  --     -- eta_reduce at ha
  --     -- beta_reduce at ha
  --     -- beta_reduce at ha


  --     -- dsimp [bipartiteMatching]



  --   -- use (cfg v).
  --   sorry

-- lemma bipartiteMatching.stopped_unmatched_node_is_locally_finite

-- lemma bipartiteMatching.is_matching

-- lemma bipartiteMatching.matching_is_maximal
