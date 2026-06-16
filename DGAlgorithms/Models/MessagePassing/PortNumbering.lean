import Mathlib
import DGAlgorithms.Network.PNNetwork
-- import DGAlgorithms.Network.CoveringMap

namespace DGAlgorithms

def PNNetwork.PortLabeling (N : PNNetwork V P) (Λ : Type*) := N.Port → Λ

@[ext, grind]
structure PNAlgorithm (P I O: Type*) where
  State : Set P → Type*
  -- State' : Set P → Type*
  Msg : Type*
  init : (p : Set P) → I → State p
  send : {p : Set P} → State p → (p → Msg)
  recv : {p : Set P} → State p → (p → Msg) → State p
  output :  State p → O

section Examples

@[simps]
def PNalgorithm.id : PNAlgorithm P S S where
  Msg := Unit
  State := fun _ ↦ S
  init := fun _ v ↦ v
  send := fun _ _ ↦ ()
  recv := fun v _ ↦ v
  output := fun v ↦ v

@[simps, grind]
def PNalgorithm.local_map (f : S → S'): PNAlgorithm P S S' where
  Msg := Unit
  State := fun _ ↦ S'
  init := fun _ v ↦ f v
  send := fun _ _ ↦ ()
  recv := fun v _ ↦ v
  output := fun v ↦ v

end Examples

variables {P I O V : Type*}

/-- A configuration of an algorithm is the collection of states at all nodes. -/
abbrev PNAlgorithm.CfgOn (𝔸 : PNAlgorithm P I O) (N : PNNetwork V P) := (v : V) → 𝔸.State (N.neighborIndexSet v)
abbrev PNAlgorithm.CfgOn' (𝔸 : PNAlgorithm P I O) (N : PNNetwork V P) := (v : V) → ((N.neighborIndexSet v) → 𝔸.Msg) × 𝔸.State (N.neighborIndexSet v)

-- @[simp, grind]
abbrev PNAlgorithm.CfgOn.output {𝔸 : PNAlgorithm P I O} {N : PNNetwork V P} (c : 𝔸.CfgOn N) : (v : V) → O := fun v ↦ 𝔸.output (c v)

-- @[simp, grind]
abbrev PNAlgorithm.CfgOn'.to_CfgOn {𝔸 : PNAlgorithm P I O} {N : PNNetwork V P} (c : 𝔸.CfgOn' N) : 𝔸.CfgOn N := fun v ↦ (c v).snd

-- @[simp, grind]
-- lemma PNAlgorithm.CfgOn.pmap_pmap {𝔸 : PNAlgorithm P I O} {N : PNNetwork V P} : ∀ cfg : 𝔸.CfgOn N, ∀ vp : N.Port, cfg (N.pmap (N.pmap vp)).node = cfg vp.node := by
--   sorry

@[simp, grind]
def PNAlgorithm.initialize (A : PNAlgorithm P I O) {V : Type*} (N : PNNetwork V P) (i : (v : V) → I) : A.CfgOn N :=
  fun v ↦ A.init (N.neighborIndexSet v) (i v)

@[simp, grind]
def PNAlgorithm.CfgOn.stepSend (A : PNAlgorithm P I O) {N : PNNetwork V P} (cfg : A.CfgOn N) : A.CfgOn' N :=
  fun v ↦
    (A.send (cfg v), cfg v)

@[simp]
lemma PNAlgorithm.CfgOn'.stepSend_toCfg {A : PNAlgorithm P I O} {N : PNNetwork V P} : ∀ cfg : A.CfgOn N, cfg.stepSend.to_CfgOn = cfg := by
  intro cfg'
  rfl

@[simp, grind]
def PNAlgorithm.CfgOn'.stepComm (A : PNAlgorithm P I O) {N : PNNetwork V P} (cfg' : A.CfgOn' N) : A.CfgOn' N :=
  fun v ↦
    (fun p ↦
        let u := N.pmap ⟨(v, p), by simp [←N.mem_neighborIndexSet]⟩
        (cfg' u.node).fst ⟨u.index, N.port_index_mem_neighborIndexSet _⟩,
    (cfg' v).snd)

@[simp]
lemma PNAlgorithm.CfgOn'.stepComm_stepComm {A : PNAlgorithm P I O} {N : PNNetwork V P} : ∀ cfg' : A.CfgOn' N, cfg'.stepComm.stepComm = cfg' := by
  intro cfg'
  ext v p
  · unfold stepComm
    simp
    apply congr_heq
    · congr
      all_goals simp
    · congr!
      simp
  · rfl

@[simp]
lemma PNAlgorithm.CfgOn'.stepComm_toCfg {A : PNAlgorithm P I O} {N : PNNetwork V P} : ∀ cfg' : A.CfgOn' N, cfg'.stepComm.to_CfgOn = cfg'.to_CfgOn := by
  intro cfg'
  rfl

@[simp, grind]
def PNAlgorithm.CfgOn'.stepRecv (A : PNAlgorithm P I O) {N : PNNetwork V P} (cfg : A.CfgOn' N) : A.CfgOn N :=
  fun v ↦
    A.recv (cfg v).snd (cfg v).fst

@[simp, grind]
def PNAlgorithm.step (A : PNAlgorithm P I O) (N : PNNetwork V P) (cfg : A.CfgOn N) : A.CfgOn N :=
  cfg.stepSend.stepComm.stepRecv

@[simp, grind]
lemma PNAlgorithm.step_eq_recv_of (A : PNAlgorithm P I O) (N : PNNetwork V P) (cfg : A.CfgOn N) :
    ∀ v : V, A.step N cfg v = A.recv (cfg v) ((cfg.stepSend.stepComm) v).fst := by simp

@[simp, grind]
def PNAlgorithm.execFor (A : PNAlgorithm P I O) (N : PNNetwork V P) (i : V → I) (n : ℕ) : A.CfgOn N :=
  (A.step N)^[n] (A.initialize N i)

@[simp]
lemma PNAlgorithm.execFor_zero  (A : PNAlgorithm P I O) (N : PNNetwork V P) (i : V → I) : A.execFor N i 0 = A.initialize N i := by rfl

@[simp]
lemma PNAlgorithm.execFor_succ  (A : PNAlgorithm P I O) (N : PNNetwork V P) (i : V → I) (n : ℕ) : A.execFor N i (n+1) = A.step N (A.execFor N i n) := by
  unfold execFor
  rw [Function.iterate_succ']
  rfl

section Stopping

class PNAlgorithm.WithStopping (A : PNAlgorithm P I O) where
  Stopping : {p : Set P} → A.State p → Prop
  lawfull_stopping : ∀ {p : Set P}, ∀ s : A.State p, ∀ msg : p → A.Msg, Stopping s → A.recv s msg = s

abbrev PNAlgorithm.Stopping (A : PNAlgorithm P I O) [inst : A.WithStopping] : {p : Set P} → A.State p → Prop := inst.Stopping

@[simp]
abbrev PNAlgorithm.Stopping_recv (A : PNAlgorithm P I O) [inst : A.WithStopping] : ∀ {p : Set P}, ∀ s : A.State p, ∀ msg : p → A.Msg, A.Stopping s → A.recv s msg = s := inst.lawfull_stopping

variable {A : PNAlgorithm P I O} [A.WithStopping]

lemma PNAlgorithm.recv_Stopping_to_Stopping {p : Set P} :
    ∀ s : A.State p, ∀ msg : p → A.Msg, A.Stopping s → A.Stopping (A.recv s msg) := by simp_all

@[simp]
lemma PNAlgorithm.Stopping_step :
    ∀ cfg : A.CfgOn N, ∀ v : V, A.Stopping (cfg v) → A.step N cfg v = cfg v := by simp_all

lemma PNAlgorithm.step_Stopping_to_Stopping :
    ∀ cfg : A.CfgOn N, ∀ v : V, A.Stopping (cfg v) → A.Stopping (A.step N cfg v) := by simp_all

abbrev PNAlgorithm.CfgOn.Stopping {N : PNNetwork V P} (cfg : A.CfgOn N) := ∀ v : V, A.Stopping (cfg v)

end Stopping

/-- A "proof" that `A` evolves to `e` when starting from `s`. -/
structure PNAlgorithm.EvolvesTo (A : PNAlgorithm P I O) (N : PNNetwork V P) (s e : A.CfgOn N) where
  steps : ℕ
  evals_in_steps : (A.step N)^[steps] s = e

@[simp]
def PNAlgorithm.EvolvesTo.induction (A : PNAlgorithm P I O) (N : PNNetwork V P) {s e : A.CfgOn N} (heval : A.EvolvesTo N s e)
  {motive : A.CfgOn N → Sort u} (hbase : motive s) (hstep : ∀ {s' : A.CfgOn N}, motive s' → motive (A.step N s')) : motive e :=
    let rec recursion (k : ℕ) : motive ((A.step N)^[k] s) := match k with
      | 0 => hbase
      | k+1 =>
        (Function.iterate_succ' _ _).symm ▸ hstep (recursion k)
    heval.evals_in_steps ▸ recursion heval.steps


@[refl, simp, grind]
def PNAlgorithm.EvolvesTo.refl : (PNAlgorithm.EvolvesTo A N c c) where
  steps := 0
  evals_in_steps := rfl

@[trans, simp, grind]
def PNAlgorithm.EvolvesTo.trans (h₁ : PNAlgorithm.EvolvesTo A N a b) (h₂ : PNAlgorithm.EvolvesTo A N b c) : (PNAlgorithm.EvolvesTo A N a c) where
  steps := h₁.steps + h₂.steps
  evals_in_steps := by
    rw [Nat.add_comm, Function.iterate_add, Function.comp,
        h₁.evals_in_steps, h₂.evals_in_steps]

/-- A "proof" that `A` reaches `e` from `s` in at most given number of steps. -/
structure PNAlgorithm.EvolvesToInTime (A : PNAlgorithm P I O) (N : PNNetwork V P) (m : ℕ) (s e : A.CfgOn N) extends A.EvolvesTo N s e where
  steps_le_m : steps ≤ m

@[refl, simp, grind]
def PNAlgorithm.EvolvesToInTime.refl : (PNAlgorithm.EvolvesToInTime A N 0 a a) where
  steps := 0
  evals_in_steps := rfl
  steps_le_m := Nat.zero_le 0

@[trans, simp, grind]
def PNAlgorithm.EvolvesToInTime.trans (h₁ : PNAlgorithm.EvolvesToInTime A N n a b) (h₂ : PNAlgorithm.EvolvesToInTime A N m b c) : (PNAlgorithm.EvolvesToInTime A N (n+m) a c) where
  steps := h₁.steps + h₂.steps
  evals_in_steps := by
    rw [Nat.add_comm, Function.iterate_add, Function.comp,
        h₁.evals_in_steps, h₂.evals_in_steps]
  steps_le_m := by
    grw [h₁.steps_le_m, h₂.steps_le_m]
