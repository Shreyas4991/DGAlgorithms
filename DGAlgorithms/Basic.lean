import Mathlib

-- Henrik Lievonen's Port Numbering Network definitions and algorithms.
-- The file is work in process, but should compile. It is provided for reference.

notation a " ≈ " b => HEq a b

structure PNNetwork (V : Type*) where
  degree : V → ℕ
  port : (v : V) → Fin (degree v) → ((u : V) × Fin (degree u))
  port_involutive : Function.Involutive (Sigma.uncurry port)

def PNNetwork.port' {g : PNNetwork V} : (v : V) × Fin (g.degree v) → ((u : V) × Fin (g.degree u)) :=
  Sigma.uncurry g.port

def PNNetwork.Port {g : PNNetwork V} : Type* := (v : V) × Fin (g.degree v)

def PNNetwork.coe_SimpleGraph (g : PNNetwork V) : SimpleGraph V where
  Adj := fun v u => v ≠ u ∧ ∃ (p : Fin (g.degree v)), (g.port v p).fst = u
  symm := by
    intro v u h
    constructor
    · exact h.left.symm
    · have ⟨p, h⟩ := h.right
      rw [←h]
      let q := (g.port v p).snd
      apply Exists.intro q
      have := congrArg Sigma.fst (g.port_involutive ⟨v, p⟩)
      assumption

instance PNNetwork.instCoeSimpleGraph : Coe (PNNetwork V) (SimpleGraph V) where
  coe := PNNetwork.coe_SimpleGraph

def PNNetwork.neighborSet (g : PNNetwork V) (v : V) : Set V :=
  {u : V | ∃ p, (g.port v p).fst = u}

-- instance PNNetwork.neighborSet.memDecidable (g : PNNetwork V) (v : V) : DecidablePred (· ∈ g.neighborSet v) :=

structure CoveringMap (g : PNNetwork V) (f : PNNetwork U) where
  map : V → U
  map_surj : Function.Surjective map
  map_preserves_degree : ∀ (v : V), g.degree v = f.degree (map v)
  map_preserves_connections : ∀ (v : V), (p : Fin (g.degree v)) →
    let ⟨v', p'⟩ := g.port v p
    let ⟨u', q'⟩ := f.port (map v) (map_preserves_degree v ▸ p)
    map v' = u' ∧ HEq p' q'

def CoveringMap.mapPort (cm : CoveringMap g f) : g.Port → f.Port :=
  fun vp => ⟨cm.map vp.fst, cm.map_preserves_degree _ ▸ vp.snd⟩


abbrev CoveringMap.expandState {S : ℕ → Type*} {g : PNNetwork V} {g' : PNNetwork V'} (cm : CoveringMap g g') : ((v : V') → S (g'.degree v)) → ((v : V) → S (g.degree v)) :=
  fun state =>
    fun v =>
      cm.map_preserves_degree _ ▸ state (cm.map v)

theorem CoveringMap.expandState.foo {S : ℕ → Type*} {g : PNNetwork V} {g' : PNNetwork V'} (cm : CoveringMap g g') (state : (v : V') → S (g'.degree v)) :
  ∀ (v : V), cm.expandState state v = cm.map_preserves_degree _ ▸ state (cm.map v) := by simp


-- theorem CoveringMap.expandState.preserves_functions {S : ℕ → Type*} {g : PNNetwork V} {g' : PNNetwork V'} (cm : CoveringMap g g') (state : (v : V') → S (g'.degree v)) (f : {d : ℕ} → S d → U) :
--   ∀ (v : V), f (state (cm.map v)) = f (cm.expandState state v) := by
--   intro v
--   congr
--   exact (cm.map_preserves_degree v).symm
--   simp

-- theorem CoveringMap.expandState'.preserves_functions {S S' : ℕ → Type*} {g : PNNetwork V} {g' : PNNetwork V'} (cm : CoveringMap g g') (state : (v : V') → S (g'.degree v)) (f : {d : ℕ} → S d → S' d) :
--   ∀ (v : V), f (state (cm.map v)) = f (cm.expandState' state v) := by
--   intro v
--   congr
--   rw [expandState', eqRec_eq_cast, eqRec_eq_cast, cast_cast, cast_eq]

def PNNetwork.doubleCover (g : PNNetwork V) : PNNetwork (V × Bool) where
  degree := fun ⟨v, _⟩ => g.degree v
  port := fun ⟨v, layer⟩ => fun p =>
    let ⟨u, q⟩ := g.port v p
    ⟨(u, ¬layer), q⟩
  port_involutive := by
    intro ⟨⟨v, layer⟩, p⟩
    repeat rw [Sigma.uncurry]
    simp

    have base := g.port_involutive ⟨v, p⟩

    constructor
    · exact congrArg Sigma.fst base
    · reduce at base
      rw [base]

def PNNetwork.doubleCover.is_cover (g : PNNetwork V) : CoveringMap g.doubleCover g where
  map := fun ⟨v, _⟩ => v
  map_surj := by
    intro v
    aesop
  map_preserves_degree := by
    aesop
  map_preserves_connections := by
    aesop


structure PNAlgorithm where
  Input : ℕ → Sort*
  State : ℕ → Sort*
  Msg : Sort*
  IsStoppingState : State d → Prop
  init : {d : ℕ} → Input d → State d
  send : {d : ℕ} → State d → Fin d → Msg
  recv : {d : ℕ} → State d → (Fin d → Msg) → State d
  recv_stop_idempotent : ∀ {d : ℕ}, ∀ (state : State d), IsStoppingState state → ∀ (msg : Fin d → Msg), recv state msg = state



def PNAlgorithm.initOn (a : PNAlgorithm) (g : PNNetwork V) (input : (v : V) → a.Input (g.degree v)) : (v : V) → a.State (g.degree v) :=
  fun v => a.init (input v)


abbrev PNAlgorithm.stepOn.incoming (a : PNAlgorithm) (g : PNNetwork V) (state : (v : V) → a.State (g.degree v)) : (v : V) → Fin (g.degree v) → a.Msg :=
  fun v p =>
    -- Collect messages from neighbors
    let ⟨u, q⟩ := g.port v p
    a.send (state u) q

def PNAlgorithm.stepOn (a : PNAlgorithm) (g : PNNetwork V) (state : (v : V) → a.State (g.degree v)) : (v : V) → a.State (g.degree v) :=
  fun v =>
    a.recv (state v) (stepOn.incoming a g state v)

def PNAlgorithm.stepOnFor (a : PNAlgorithm) (g : PNNetwork V) (state : (v : V) → a.State (g.degree v)) (steps : ℕ) : (v : V) → a.State (g.degree v) :=
  match steps with
  | 0 => state
  | n + 1 => stepOnFor a g (stepOn a g state) n

def PNAlgorithm.HaltsOnWith (a : PNAlgorithm) (g : PNNetwork V) (input : (v : V) → a.Input (g.degree v)) : Prop :=
  ∃ steps, ∀ v, a.IsStoppingState (a.stepOnFor g (a.initOn g input) steps v)

def PNAlgorithm.HaltsOn (a : PNAlgorithm) (g : PNNetwork V) : Prop :=
  ∀ input, a.HaltsOnWith g input

theorem PNAlgorithm.covering_map_indistinguishable.step_on.incoming {g : PNNetwork V} {g' : PNNetwork V'} (a : PNAlgorithm) (cm : CoveringMap g g')
  (state : (v : V') → a.State (g'.degree v)) :
  ∀ (v : V), stepOn.incoming a g' state (cm.map v) = cm.map_preserves_degree v ▸ stepOn.incoming a g (cm.expandState state) v := by
  intro v
  reduce
  rw [eqRec_eq_cast, cast_eq_iff_heq.mpr]
  apply Function.hfunext
  · congr
    exact cm.map_preserves_degree v

  · intro p q h_pq

    have ⟨b, c⟩ := cm.map_preserves_connections v p

    congr
    · rw [cm.map_preserves_degree, b]
      congr
      rw [eqRec_eq_cast, cast_eq_iff_heq]
      assumption

    · have := congr_arg_heq state b
      rw [rec_heq_iff_heq]
      apply HEq.trans this
      congr
      rw [eqRec_eq_cast, cast_eq_iff_heq]
      assumption

    · apply HEq.trans c
      rw [eqRec_eq_cast]
      congr
      rw [cast_eq_iff_heq.mpr]
      assumption

theorem PNAlgorithm.covering_map_indistinguishable.step_on {g : PNNetwork V} {g' : PNNetwork V'} (a : PNAlgorithm) (cm : CoveringMap g g') (state : (v : V') → a.State (g'.degree v)) :
  cm.expandState (a.stepOn g' state) = a.stepOn g (cm.expandState state) := by
  funext v
  reduce
  repeat rw [eqRec_eq_cast]
  rw [cast_eq_iff_heq]
  congr
  · exact (cm.map_preserves_degree v).symm
  · symm
    apply cast_heq
  · have h := covering_map_indistinguishable.step_on.incoming a cm state v
    reduce at h
    simp_all only [eqRec_heq_iff_heq, heq_eq_eq]


theorem PNAlgorithm.covering_map_indistinguishable.init_on {g : PNNetwork V} {g' : PNNetwork V'} (a : PNAlgorithm) (cm : CoveringMap g g') (input : (v : V') → a.Input (g'.degree v)) :
  cm.expandState (a.initOn g' input) = a.initOn g (cm.expandState input) := by
  funext v
  simp [CoveringMap.expandState, initOn]
  simp [eqRec_eq_cast]
  rw [cast_eq_iff_heq]
  congr
  · exact (cm.map_preserves_degree v).symm
  · symm
    apply cast_heq

def PortLabeling {V : Type*} (L : Type*) (g : PNNetwork V) := g.Port → L


def NodeLabeling {V : Type*} (L : Type*) (g : PNNetwork V) := V → L


structure Coloring {V : Type*} (c : ℕ) (g : PNNetwork V) where
  color : NodeLabeling (Fin c) g
  proper : ∀ (v : V), ∀ (p : Fin (g.degree v)), color v ≠ color (g.port v p).fst

def Coloring.to_higher {V : Type*} (c : ℕ) (g : PNNetwork V) (d : ℕ) {h : d ≥ c} (col : Coloring c g) : Coloring d g where
  color := fun v => (col.color v).castLE h
  proper := by
    intro v p h_contra
    apply col.proper
    exact Fin.castLE_inj.mp h_contra


def PNLabeling (⅀ : Type*) (g : PNNetwork V) := g.Port → ⅀

def PNLabeling.IsNodeLabeling {⅀ : Type*} {g : PNNetwork V} (L : PNLabeling ⅀ g) : Prop :=
  ∀ v : V, ∃ l : ⅀, ∀ p : Fin (g.degree v), L ⟨v, p⟩ = l


def PNProblem := {V U : Type*} → (g : PNNetwork V) → (l : V → U) → Prop

def PNColoring (d : Nat) : PNProblem := fun g l => ∀ v, ∀ u ∈ g.neighborSet v, l u ≠ l v
