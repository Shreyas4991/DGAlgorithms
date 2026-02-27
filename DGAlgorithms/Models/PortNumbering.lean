import Mathlib
import DGAlgorithms.Network.PNNetwork
import DGAlgorithms.Network.CoveringMap

namespace DGAlgorithms



-- Algorithm ≃ I → O
structure PNAlgorithm (I O : Type*) where
  Msg : Type*
  State : Type*
  stopStates : Set State
  init : ℕ → I → State
  send : (d : ℕ) → State → ℕ → Msg
  recv : (d : ℕ) → State → (Fin d → Msg) → State
  stopping_condition : ∀ d : ℕ, ∀ y : Fin d → Msg, ∀ s : State, s ∈ stopStates → recv d s y = s
  output : (state : State) → state ∈ stopStates → O -- TODO: State → O

section Examples

def PNalgorithm.id {A : Type*} : PNAlgorithm A A where
  Msg := Unit
  State := A
  stopStates := Set.univ
  init := fun d v ↦ v
  send := fun _ _ _ ↦ ()
  recv := fun _ v _ ↦ v
  stopping_condition := by simp
  output := fun v _ ↦ v


def PNalgorithm.local_map (f : S → S'): PNAlgorithm S S' where
  Msg := Unit
  State := S'
  stopStates := Set.univ
  init := fun d v ↦ f v
  send := fun _ _ _ ↦ ()
  recv := fun _ v _ ↦ v
  stopping_condition := by simp
  output := fun v _ ↦ v

end Examples

/-- A configuration of an algorithm is the collection of states at all nodes. -/
abbrev PNAlgorithm.Cfg (𝔸 : PNAlgorithm I O) (V : Type u) := V → 𝔸.State

def PNAlgorithm.initialize (A : PNAlgorithm I O) {V : Type*} (N : PNNetwork V) (i : V → I) : A.Cfg V :=
  fun v ↦ A.init (N.deg v) (i v)

def PNAlgorithm.step (A : PNAlgorithm I O) (N : PNNetwork V) (cfg : A.Cfg V) : A.Cfg V :=
  fun v ↦
    A.recv (N.deg v) (cfg v) (fun p ↦ let u := N.pmap (v, p); A.send (N.deg u.node) (cfg u.node) u.port)

lemma PNAlgorithm.step.obey_network_equiv (A : PNAlgorithm I O) (N₁ N₂ : PNNetwork V) : N₁ ≈ N₂ → A.step N₁ = A.step N₂ := by
  intro hequiv
  ext cfg v
  unfold step
  have hequiv : PNNetwork.eq N₁ N₂ := hequiv
  unfold PNNetwork.eq at hequiv
  cases' hequiv with hdeg hpmap
  rw [←hdeg]
  congr! with p

  rw [hpmap]
  exact p.isLt

def PNAlgorithm.eval' (A : PNAlgorithm I O) (N : PNNetwork V) (i : V → I) : ℕ → A.Cfg V
  | 0 => A.initialize N i
  | k+1 => A.step N (A.eval' N i k)

/-- A "proof" that `A` evaluates to `e` when starting from `s`. -/
structure PNAlgorithm.EvolvesTo (A : PNAlgorithm I O) (N : PNNetwork V) (s e : A.Cfg V) where
  steps : ℕ
  evals_in_steps : (A.step N)^[steps] s = e

-- #print Nat.rec
def PNAlgorithm.EvolvesTo.induction (A : PNAlgorithm I O) (N : PNNetwork V) {s e : A.Cfg V} (heval : A.EvolvesTo N s e)
  {motive : A.Cfg V → Sort u} (hbase : motive s) (hstep : ∀ {s' : A.Cfg V}, motive s' → motive (A.step N s')) : motive e :=
    let rec recursion (k : ℕ) : motive ((A.step N)^[k] s) := match k with
      | 0 => hbase
      | k+1 =>
        (Function.iterate_succ' _ _).symm ▸ hstep (recursion k)
    heval.evals_in_steps ▸ recursion heval.steps

/-- A "proof" that `A` reaches `e` from `s` in at most given number of steps. -/
structure PNAlgorithm.EvolvesToInTime (A : PNAlgorithm I O) (N : PNNetwork V) (s e : A.Cfg V) (m : ℕ) extends A.EvolvesTo N s e where
  steps_le_m : steps ≤ m

@[refl]
def PNAlgorithm.EvolvesTo.refl : (PNAlgorithm.EvolvesTo A N a a) where
  steps := 0
  evals_in_steps := rfl

@[trans]
def PNAlgorithm.EvolvesTo.trans (h₁ : PNAlgorithm.EvolvesTo A N a b) (h₂ : PNAlgorithm.EvolvesTo A N b c) : (PNAlgorithm.EvolvesTo A N a c) where
  steps := h₁.steps + h₂.steps
  evals_in_steps := by
    rw [Nat.add_comm, Function.iterate_add, Function.comp,
        h₁.evals_in_steps, h₂.evals_in_steps]

-- @[refl] Unfortunately we cannot have that due to pattern matching failing
def PNAlgorithm.EvolvesToInTime.refl : (PNAlgorithm.EvolvesToInTime A N a a 0) where
  steps := 0
  evals_in_steps := rfl
  steps_le_m := Nat.zero_le 0

@[trans]
def PNAlgorithm.EvolvesToInTime.trans (h₁ : PNAlgorithm.EvolvesToInTime A N a b n) (h₂ : PNAlgorithm.EvolvesToInTime A N b c m) : (PNAlgorithm.EvolvesToInTime A N a c (n+m)) where
  steps := h₁.steps + h₂.steps
  evals_in_steps := by
    rw [Nat.add_comm, Function.iterate_add, Function.comp,
        h₁.evals_in_steps, h₂.evals_in_steps]
  steps_le_m := by
    grw [h₁.steps_le_m, h₂.steps_le_m]

/-- A configuration is stopping if all nodes are in a stopping state. -/
def PNAlgorithm.Cfg.IsStopping {A : PNAlgorithm I O} (c : A.Cfg V) : Prop :=
  ∀ v : V, c v ∈ A.stopStates

/-- Once an algorithm has stopped, the configuration won't change anymore. -/
@[simp]
lemma PNAlgorithm.step_id_if_stopping {A : PNAlgorithm I O} {N : PNNetwork V} {c : A.Cfg V} (h : c.IsStopping) : A.step N c = c := by
  unfold step
  ext x
  apply A.stopping_condition
  apply h

/-- Continuing evaluation after a stopping configuration does not modify the configuration anymore. -/
@[simp]
lemma PNAlgorithm.Stopping_EvalsTo_eq_self {A : PNAlgorithm I O} {N : PNNetwork V} {c c' : A.Cfg V} (h : c.IsStopping) : A.EvolvesTo N c c' → c = c' := by
  intro h'
  trans (A.step N)^[h'.steps] c
  · -- Use induction in number of steps and show that after each step, the expression is still c
    induction' h'.steps with n hn
    · rfl
    · rw [Function.iterate_succ_apply, step_id_if_stopping h]
      exact hn
  · exact h'.evals_in_steps

def PNAlgorithm.Cfg.output {A : PNAlgorithm I O} {c : A.Cfg V} (h : c.IsStopping) : V → O :=
  fun v ↦ A.output (c v) (h v)


structure PNAlgorithm.EvalsTo (A : PNAlgorithm I O) (N : PNNetwork V) (i : V → I) (o : V → O) where
  end_state : A.Cfg V
  stops : end_state.IsStopping
  output_correct : end_state.output stops = o
  evolves : EvolvesTo A N (A.initialize N i) end_state


structure PNAlgorithm.EvalsToStopping (A : PNAlgorithm I O) (N : PNNetwork V) (s e : A.Cfg V) extends EvolvesTo A N s e where
  stopping : e.IsStopping

def PNAlgorithm.EvalsToStopping.output {A : PNAlgorithm I O} {N : PNNetwork V} {s e : A.Cfg V} (h : A.EvalsToStopping N s e) : V → O :=
  fun v => A.output (e v) (h.stopping v)


structure PNAlgorithm.EvalsToStoppingInTime (A : PNAlgorithm I O) (N : PNNetwork V) (s e : A.Cfg V) (m : ℕ) extends EvalsToStopping A N s e, EvolvesToInTime A N s e m where


/-- Run two PNAlgorithms in parallel. -/
def PNAlgorithm.parallel (A₁ : PNAlgorithm I₁ O₁) (A₂ : PNAlgorithm I₂ O₂) : PNAlgorithm (I₁ × I₂) (O₁ × O₂) where
  Msg := A₁.Msg × A₂.Msg
  State := A₁.State × A₂.State
  stopStates := A₁.stopStates ×ˢ A₂.stopStates
  init := fun d i ↦ (A₁.init d i.fst, A₂.init d i.snd)
  send := fun d s p ↦ (A₁.send d s.fst p, A₂.send d s.snd p)
  recv := fun d s m ↦ (A₁.recv d s.fst (Prod.fst ∘ m), A₂.recv d s.snd (Prod.snd ∘ m))
  stopping_condition := by
    intro d m s h
    ext
    · apply A₁.stopping_condition d (Prod.fst ∘ m) s.1
      simp_all
    · apply A₂.stopping_condition d (Prod.snd ∘ m) s.2
      simp_all
  output := fun s h ↦ (A₁.output s.fst (by simp_all), A₂.output s.snd (by simp_all))

-- def bar {V α β : Type*} : ((V → α) → V → α) → ((V → β) → V → β) → (V → α × β) → V → α × β := by apply?

-- lemma foo  {A₁ : PNAlgorithm I₁ O₁} {A₂ : PNAlgorithm I₂ O₂} : (A₁.parallel A₂).step N = bar (A₁.step N) (A₂.step N) := by
--   sorry

-- def PNAlgorithm.parallel.EvolvesTo (h₁ : PNAlgorithm.EvolvesTo A₁ N s₁ e₁) (h₂ : PNAlgorithm.EvolvesTo A₂ N s₂ e₂) :
--     PNAlgorithm.EvolvesTo (A₁.parallel A₂) N (fun v ↦ (s₁ v, s₂ v)) (fun v ↦ (e₁ v, e₂ v)) where
--   steps := max h₁.steps h₂.steps
--   evals_in_steps := by
--     ext v

--     -- intro
--     sorry

-- def PNAlgorithm.Output {A : PNAlgorithm I O} {N : PNNetwork V} {s e : A.Cfg V} (h : A.EvolvesTo N s e) (h' : ∀ v, e v ∈ A.stopStates) : V → O :=
--   fun v ↦
--     A.output
--   sorry

-- structure PNAlgorithm.StopsTo (A : PNAlgorithm I O) (N : PNNetwork V) (s : A.Cfg V) (e : )

-- def PNAlgorithm.eval


-- Covering maps
def CoveringMap.expand_cfg {N₁ : PNNetwork V₁} {N₂ : PNNetwork V₂} (cm : CoveringMap N₁ N₂) : (V₂ → S) → V₁ → S :=
  fun cfg v ↦ cfg (cm.map v)

@[simp]
lemma PNAlgorithm.covering_map_step {N₁ : PNNetwork V₁} {N₂ : PNNetwork V₂}  (A : PNAlgorithm I O) (cm : CoveringMap N₁ N₂) :
    ∀ cfg : A.Cfg V₂, A.step N₁ (cm.expand_cfg cfg) = cm.expand_cfg (A.step N₂ cfg) := by
  unfold step CoveringMap.expand_cfg
  intro cfg
  ext v
  dsimp
  rw [←cm.map_deg]
  congr
  ext p
  rw [cm.map_deg]
  have := cm.map_adj (v, p) p.isLt
  grind


section Examples

-- Define a simple directed cylce
def PNNetwork.cycle (n : ℕ) : PNNetwork (Fin (n+1)) :=
  PNNetwork.mk'
  (deg := fun _ ↦ 2)
  (
    fun p ↦ if (p.port == 0) then ⟨p.node - 1, 1⟩ else ⟨p.node + 1, 0⟩
  )
  (by
    intro vp
    simp
    split_ifs with h₁ h₂
    · grind
    · ext
      · unfold FinPort.node
        simp
      · simp [h₁]
    · ext
      · unfold FinPort.node
        simp
      · simp
        exact Eq.symm (Fin.eq_one_of_ne_zero vp.snd h₁)
    · grind
  )


def PNNetwork.cycle_cover (n m : ℕ) (h : (n + 1) ∣ (m + 1)) : CoveringMap (cycle m) (cycle n) where
  map := fun v => Fin.ofNat (n+1) v
  map_surj := by
    simp [Fin.ofNat_eq_cast, Function.Surjective]
    intro b

    sorry
  map_deg := sorry
  map_adj := sorry

-- lemma PNAlgorithm.no_coloring_algorithm : ¬∃ A : PNAlgorithm () ℕ, ∃ A.Cf

end Examples


namespace AsyncStart

section WakeUpSeq

def WakeUpSeq (V I : Type*) := ℕ → V → Option I

variable (wus : WakeUpSeq V I)

-- def WakeUpSeq.WakesUpAll : Prop := ∃ K : ℕ, ∀ v : V, ∃ k ≤ K, (wus k v).isSome

def WakeUpSeq.ComesFrom (f : V → I) : Prop :=
  ∀ k : ℕ, ∀ v : V, (h : (wus k v).isSome) → ((wus k v).get h) = f v


def WakeUpSeq.InitializedBy (t : ℕ) : Prop :=
  ∀ v : V, ∃ k < t, (wus k v).isSome


end WakeUpSeq

-- Semantics:
--
-- Round 1:
-- wake_up
-- step
-- Round 2:
-- wake_up
-- step
-- ...

structure APNAlgorithm (I O : Type*) where
  Msg : Type*
  State : Type*
  stopStates : Set State
  init : ℕ → I → State
  send : (d : ℕ) → State → ℕ → Msg
  recv : (d : ℕ) → State → (Fin d → Option Msg) → State
  stopping_condition : ∀ d : ℕ, ∀ y : Fin d → Option Msg, ∀ s : State, s ∈ stopStates → recv d s y = s
  output : (state : State) → state ∈ stopStates → O -- TODO: State → O

-- structure RunningFlag (V : Type*) where
--   fn : ℕ → V → Prop
--   fn_monotone : ∀ k : ℕ, ∀ v : V, fn k v → fn k.succ v

-- def RunningFlag.start := ⊓ k : ℕ, True

/-- A configuration of an algorithm is the collection of states at all nodes. -/
abbrev APNAlgorithm.Cfg (𝔸 : APNAlgorithm I O) (V : Type u) := V → Option 𝔸.State


/-- A configuration is stopping if all nodes are in a stopping state. -/
def APNAlgorithm.Cfg.IsStopping {A : APNAlgorithm I O} (c : A.Cfg V) : Prop :=
  ∀ v : V, (c v).isSome ∧ ((h : (c v).isSome) → (c v).get h ∈ A.stopStates)

def APNAlgorithm.Cfg.output {A : APNAlgorithm I O} {c : A.Cfg V} (h : c.IsStopping) : V → O :=
  fun v ↦ A.output ((c v).get (h v).left) ((h v).right (h v).left)

-- def APNAlgorithm.initialize (A : APNAlgorithm I O) {V : Type*} (N : PNNetwork V) (i : V → I) : A.Cfg V :=
--   fun v ↦ A.init (N.deg v) (i v)
def APNAlgorithm.initial (A : APNAlgorithm I O) : A.Cfg V :=
  fun _ => none

def APNAlgorithm.step (A : APNAlgorithm I O) (N : PNNetwork V) (cfg : A.Cfg V) : A.Cfg V :=
  fun v ↦
    let send_helper : V → ℕ → Option A.Msg :=
      fun u q =>
        (cfg u) >>= fun cfg_u =>
          some <| A.send (N.deg u) cfg_u q
    (cfg v) >>= fun cfg_v =>
      some <| A.recv (N.deg v) cfg_v (fun p ↦ let u := N.pmap (v, p); send_helper u.node u.port)

lemma APNAlgorithm.step.monotone {A : APNAlgorithm I O} {N : PNNetwork V} (cfg : A.Cfg V) :
  ∀ v : V, (cfg v).isSome → ((A.step N cfg) v).isSome := by
    sorry

def APNAlgorithm.wake_up (A : APNAlgorithm I O) (N : PNNetwork V) (i : V → Option I) (cfg : A.Cfg V) : A.Cfg V :=
  fun v =>
    if (cfg v).isSome then
      cfg v
    else
      (i v) >>= fun i_v => A.init (N.deg v) i_v

lemma APNAlgorithm.wake_up.monotone {A : APNAlgorithm I O} {N : PNNetwork V} (cfg : A.Cfg V) (i : V → Option I) :
  ∀ v : V, (cfg v).isSome → (A.wake_up N i cfg) v = cfg v := by
    sorry

def APNAlgorithm.round (A : APNAlgorithm I O) (N : PNNetwork V) (i : V → Option I) : A.Cfg V → A.Cfg V :=
  (A.step N) ∘ (A.wake_up N i)

def APNAlgorithm.round.iter (A : APNAlgorithm I O) (N : PNNetwork V) (steps : ℕ) (wake_ups : WakeUpSeq V I) (cfg : A.Cfg V) :
    A.Cfg V :=
  match steps with
  | 0 => cfg
  | k+1 => A.round N (wake_ups k) $ APNAlgorithm.round.iter A N k wake_ups cfg

/-- A "proof" that `A` evaluates to `e` when starting from `s`. -/
structure APNAlgorithm.EvolvesToWith (A : APNAlgorithm I O) (N : PNNetwork V) (s e : A.Cfg V) (wake_ups : WakeUpSeq V I) where
  steps : ℕ
  evals_in_steps : APNAlgorithm.round.iter A N steps wake_ups s = e

/-- A "proof" that `A` reaches `e` from `s` in at most given number of steps. -/
structure APNAlgorithm.EvolvesToInTimeWith (A : APNAlgorithm I O) (N : PNNetwork V) (s e : A.Cfg V) (m : ℕ) (wake_ups : WakeUpSeq V I) extends A.EvolvesToWith N s e wake_ups where
  steps_le_m : steps ≤ m


/-- An asynchronous PN algorithm computes something stably if
for every finitely-initializing wake up sequence coming from input `i`,
the algorithm evaluates in `time` steps after full initialization
to a configuration that is stopping and produces output `o`.
-/
def APNAlgorithm.StablyComputes
    (A : APNAlgorithm I O) (N : PNNetwork V)
    (i : V → I) (o : V → O) (time : ℕ) : Prop :=
  ∀ t₁ : ℕ, ∀ wus : WakeUpSeq V I, wus.ComesFrom i → wus.InitializedBy t₁ →
    ∃ e : A.Cfg V, ∃ _ : A.EvolvesToInTimeWith N A.initial e (t₁ + time) wus,
      e.IsStopping ∧ ((h : e.IsStopping) → e.output h = o)


def PNAlgorithm.toAsync (A : PNAlgorithm I O) : APNAlgorithm I O := sorry

-- TODO: +2 in time is just a guess
lemma PNAlgorithm.toAsync.stably_computes
    (A : PNAlgorithm I O) (N : PNNetwork V) (i : V → I) (o : V → O)
    (time : ℕ) (h : A.EvalsTo N i o) (h_time : h.evolves.steps ≤ time) :
    (PNAlgorithm.toAsync A).StablyComputes N i o (time+2) := sorry


def APNAlgorithm.toSync (A : APNAlgorithm I O) : PNAlgorithm I O := sorry

-- -- #print Nat.rec
-- def PNAlgorithm.EvolvesTo.induction (A : PNAlgorithm I O) (N : PNNetwork V) {s e : A.Cfg V} (heval : A.EvolvesTo N s e)
--   {motive : A.Cfg V → Sort u} (hbase : motive s) (hstep : ∀ {s' : A.Cfg V}, motive s' → motive (A.step N s')) : motive e :=
--     let rec recursion (k : ℕ) : motive ((A.step N)^[k] s) := match k with
--       | 0 => hbase
--       | k+1 =>
--         (Function.iterate_succ' _ _).symm ▸ hstep (recursion k)
--     heval.evals_in_steps ▸ recursion heval.steps

-- /-- A "proof" that `A` reaches `e` from `s` in at most given number of steps. -/
-- structure PNAlgorithm.EvolvesToInTime (A : PNAlgorithm I O) (N : PNNetwork V) (s e : A.Cfg V) (m : ℕ) extends A.EvolvesTo N s e where
--   steps_le_m : steps ≤ m

-- @[refl]
-- def PNAlgorithm.EvolvesTo.refl : (PNAlgorithm.EvolvesTo A N a a) where
--   steps := 0
--   evals_in_steps := rfl

-- @[trans]
-- def PNAlgorithm.EvolvesTo.trans (h₁ : PNAlgorithm.EvolvesTo A N a b) (h₂ : PNAlgorithm.EvolvesTo A N b c) : (PNAlgorithm.EvolvesTo A N a c) where
--   steps := h₁.steps + h₂.steps
--   evals_in_steps := by
--     rw [Nat.add_comm, Function.iterate_add, Function.comp,
--         h₁.evals_in_steps, h₂.evals_in_steps]




end AsyncStart

-- inductive Trace (A : PNAlgorithm I O) (N : PNNetwork V) : Type* where
--   | init (i : V → I) : Trace A N
--   | step (prev : Trace A N s): Trace A N (
--     fun v ↦ A.recv (N.deg v) (s v) (fun p ↦ let u := N.pmap (v, p); A.send (N.deg u.node) (s u.node) u.port)
--   )

-- def Trace.length : Trace A N s → ℕ
--   | init _ => 0
--   | step p => p.length + 1


def dirCycle (n : ℕ) : PNNetwork (Fin (n+2)) where
  deg := fun _ ↦ 2
  pmap := fun p ↦ (ite (p.port == 0) (p.node+1) (p.node-1), ite (p.port == 0) 1 0)
  pmap_involutive := by
    intro v i hi
    have hi : i = 0 ∨ i = 1 := by grind
    cases' hi with hi hi
    all_goals grind
  is_well_defined := by
    intro vp

    sorry

-- def fooboar (A : Type*) : PNAlgorithm A A where
--   Msg := Unit
--   State := A
--   stopStates := Set.univ
--   init := fun v ↦ v
--   send := fun _ _ _ ↦ ()
--   recv := fun _ v _ ↦ v
--   stopping_condition := by simp
--   output := fun v _ ↦ v
-- def id_start : Trace (fooboar ℕ) (dirCycle 10) := Trace.init (fun _ ↦ 3)


structure PNAlgorithm.comp.State (a1 : PNAlgorithm A B) (a2 : PNAlgorithm B C) where
  state₁ : a1.State
  state₂ : Option a2.State
  deg : ℕ
  msg₂ : Vector (Option a2.Msg) deg
  needs_send₂ : Bool

def PNAlgorithm.comp (a1 : PNAlgorithm A B) (a2 : PNAlgorithm B C) [∀ s, Decidable (s ∈ a1.stopStates)] : PNAlgorithm A C where
  Msg := a1.Msg × Option a2.Msg
  State := comp.State a1 a2
  init := fun d input =>
    let state₁ := a1.init d input
    let state₂ := if h : state₁ ∈ a1.stopStates then some (a2.init d (a1.output state₁ h)) else none
    {
      state₁,
      state₂,
      deg := d,
      msg₂ := Vector.ofFn (fun _ => none),
      needs_send₂ := state₂.isSome,
    }
  stopStates := setOf $ fun s =>
    if h : s.state₂.isSome then
      s.state₁ ∈ a1.stopStates ∧ s.state₂.get h ∈ a2.stopStates
    else
      False
  send := fun d s p =>
    (a1.send d s.state₁ p, if h : s.needs_send₂ ∧ s.state₂.isSome then some (a2.send d (s.state₂.get h.right) p) else none)
  recv := fun d s msg =>
    if hdeg : d = s.deg then
      -- Update first state machine and the set of received messages
      let state₁ := a1.recv d s.state₁ (Prod.fst ∘ msg)
      let msg₂ := Vector.ofFn fun p =>
          (msg p).snd.or (s.msg₂.get (hdeg ▸ p))

      if h : state₁ ∈ a1.stopStates then
        -- Phase two
        let state₂ := s.state₂.getD (a2.init d (a1.output state₁ h))
        -- Step if all messages received
        if h : msg₂.all Option.isSome then
          let state₂ := a2.recv d state₂ (fun p =>
            (msg₂.get p).get (by
              rw [Vector.all_eq_true] at h
              exact h (↑p) p.isLt
            )
          )
          {
            state₁,
            state₂,
            deg := d,
            msg₂ := Vector.ofFn (fun _ => none),
            needs_send₂ := true,
          }
        else
          {
          state₁,
          state₂,
          deg := d,
          msg₂,
          needs_send₂ := false,
        }
      else
        -- Still in phase one
        {
          state₁,
          state₂ := none,
          deg := d,
          msg₂,
          needs_send₂ := false
        }
      else
        -- Invalid update: degree shouldn't change
        s
  stopping_condition := by
    intro d msg state hstop
    simp at hstop
    obtain ⟨hstop₁, _, hstop₂⟩ := hstop
    extract_lets state₁
    have hstop_evol₁ := a1.stopping_condition d (Prod.fst ∘ msg) _ hstop₁

    split
    rename_i hdeg

    extract_lets msg₂
    · split_ifs with hstop₁' hsome₂
      · extract_lets state₂ state₂'
        -- congr


        sorry
      · sorry
      · absurd hstop₁'
        unfold state₁
        rw [hstop_evol₁]
        exact hstop₁
    · rfl
  output := fun s h =>
    have valid₂ : s.state₂.isSome := by aesop
    let s := s.state₂.get valid₂
    a2.output s (by simp_all [s])

-- lemma PNAlgorithm.comp_spec_foo {N : PNNetwork V} {a1 : PNAlgorithm A B} {a2 : PNAlgorithm B C} [∀ s, Decidable (s ∈ a1.stopStates)]
--     (input : V → A)
--     {e₁ : a1.Cfg V}
--     {e₂ : a2.Cfg V}
--     (h₁ : a1.EvalsToStoppingInTime N (a1.initialize N input) e₁ T₁) (h₂ : a2.EvalsToStoppingInTime N (a2.initialize N h₁.output) e₂ T₂ ) :
--       -- (a1.comp a2).EvalsToStoppingInTime N (a1.initialize N input)
--      := sorry

def PNAlgorithm.comp' (a1 : PNAlgorithm A B) (a2 : PNAlgorithm B C) : PNAlgorithm A C where
  Msg := a1.Msg ⊕ a2.Msg
  State := a1.State ⊕ a2.State
  stopStates := fun s ↦
    match s with
    | .inl s1 => False
    | .inr s2 => s2 ∈ a2.stopStates
  init := sorry
  send := fun d s p ↦
    match s with
    | .inl s1 => .inl $ a1.send d s1 p
    | .inr s2 => .inr $ a2.send d s2 p
  recv := sorry
  stopping_condition := sorry
  output := fun s h ↦ by
    sorry
    -- match h with
    -- | .inr _ => sorry
    -- match s with
    -- | .inl _ => False.elim h
    -- | .inr s => by
    --   exact a2.output _ h

-- lemma PNAlgorithm.comp_State (a1 : PNAlgorithm A B) (a2 : PNAlgorithm B C) : (a1.comp a2).State = (a1.State ⊕ a2.State) := rfl

end DGAlgorithms
