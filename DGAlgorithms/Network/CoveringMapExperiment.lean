import Mathlib
import DGAlgorithms.Network.PNNetworkExperiment

namespace DGAlgorithms





abbrev PortProj (V : Type u) (P : Type v) (v : V)  := {p : Port V P // p.node = v}
/-- A covering map is a surjective, degree-preserving and adjacency-preserving
map between networks.

Note that the covering map also preserves the order of adjacent ports.
-/
structure CoveringMap (N : PNNetwork V P) (N' : PNNetwork V' P) where
  φ : V → V'
  φ_hom : ∀ v w : V, ∀ i j : P, N.pmap ⟨v, i⟩ = ⟨w, j⟩ → N'.pmap ⟨φ v, i⟩ = ⟨φ w, j⟩
  φ_surj : Function.Surjective φ
  -- map_deg : ∀ v : V, deg G v = deg G' (map v)
  φ_local_iso : ∀ v : V, PortProj V P v ≃ PortProj V' P (φ v)


-- structure CoveringMap (G : PNNetwork V α) (G' : PNNetwork V' α') where
--   map : V → V'
--   map_surj : Function.Surjective map
--   map_deg : ∀ v : V, deg G v = deg G' (map v)
--   map_adj : ∀ p : Port V, G.PortValid p →
--     let mapPort : Port V → Port V' := fun p ↦ (map p.node, p.port)
--     mapPort (G.pmap p) = G'.pmap (mapPort p)

/-- Lift the map from vertices of the network to its ports. -/
def CoveringMap.mapPort(G : PNNetwork V P) (G' : PNNetwork V' P)
  (CM : CoveringMap G G') : Port V P → Port V' P :=
  fun p =>
    {
      node := CM.φ p.node
      port := p.port
    }

-- def CoveringMap.mapPort(G : PNNetwork V α) (G' : PNNetwork V' α')
--   (CM : CoveringMap G G') : Port V α → Port V' α' :=
--   fun p ↦ ⟨CM.map p.node, p.port⟩, by
--     unfold PNNetwork.PortValid at *
--     rw [←CM.map_deg]
--     simpa using p.prop⟩

section Examples

def CoveringMap.self (G : PNNetwork V P) : CoveringMap G G where
  φ := id
  φ_hom := by
    intro v w i j
    simp
  φ_surj := by
    intro v
    simp
  φ_local_iso := by
    intro v
    simp [PortProj]
    constructor
    case toFun => exact id
    case invFun => exact id
    all_goals
      unfold autoParam
      simp_all [Function.LeftInverse, Function.RightInverse]


def doubleCover
  {V : Type u} {P : Type v}
  (N : PNNetwork V P) : PNNetwork (V × Bool) P where
  pmap := fun ⟨(v, boolean), port⟩ =>
    let ⟨u, port₂⟩ := N.pmap ⟨v, port⟩
    ⟨⟨u, not boolean⟩, port₂⟩
  pmap_involutive := by
    intro node port
    cases node.2 <;> simp_all
    constructor <;> simp [N.pmap_involutive]
    constructor <;> simp [N.pmap_involutive]

def doubleCover.isCoveringMap (N : PNNetwork V P) : CoveringMap (doubleCover N) N where
  φ v := v.fst
  φ_hom := by
    intro v w i j
    simp [doubleCover]
    intro hnode hport
    rw [←hnode, ←hport]
  φ_surj := by
    intro v
    aesop
  φ_local_iso := by
    intro v
    constructor
    case toFun =>
      intro p
      constructor
      case val =>
        exact ⟨v.fst, p.val.port⟩
      case property =>
        simp
    case invFun =>
      intro p
      constructor
      case val =>
        exact ⟨v, p.val.port⟩
      case property =>
        simp
    all_goals
      simp [autoParam, Function.LeftInverse, Function.RightInverse]
    case left_inv =>
      intro a ha
      rw [←ha]
    case right_inv =>
      intro a ha
      rw [←ha]


end Examples


def CoveringMap.of_equiv (N₁ N₂ : PNNetwork V P) (h_equiv : N₁ ≈ N₂) : CoveringMap N₁ N₂ where
  φ := id
  φ_surj := Function.surjective_id
  φ_local_iso := by
    intro v
    constructor
    case toFun =>
      intro p
      simp
      exact p
    case invFun =>
      intro p
      simp at p
      exact p
    all_goals
      simp_all[autoParam, Function.LeftInverse, Function.RightInverse]

  φ_hom := by
    intro v w i j h
    simp
    rw [←h, h_equiv]




def CoveringMap.comp (m₂ : CoveringMap G₂ G₃) (m₁ : CoveringMap G₁ G₂) : CoveringMap G₁ G₃ where
  φ:= m₂.φ ∘ m₁.φ
  φ_surj := Function.Surjective.comp m₂.φ_surj m₁.φ_surj
  φ_local_iso := by
    intro v
    apply Equiv.trans (m₁.φ_local_iso v) (m₂.φ_local_iso (m₁.φ v))

  φ_hom := by
    intro v w i j h
    simp
    rw [m₂.φ_hom]
    rw [m₁.φ_hom]
    exact h

infixr:90 " ∘ "  => CoveringMap.comp

@[simp] lemma CoveringMap.comp_self (m : CoveringMap G G') : m ∘ CoveringMap.self G = m := by rfl

@[simp] lemma CoveringMap.self_comp (m : CoveringMap G G') : CoveringMap.self G' ∘ m = m := by rfl

inductive LocallyCovering (G : PNNetwork V P) (G' : PNNetwork V' P) : P → V → V' → Type where
  | refl (v : V) (v' : V') (h : PortProj V P v ≃ PortProj V' P v') : LocallyCovering G G' p v v'
  | succ (v : V) (v' : V') (h : PortProj V P v ≃ PortProj V' P v') (h' : ∀ p : P, LocallyCovering G G' r (G.pmap ⟨v, p⟩).node (G'.pmap ⟨v', p⟩).node) : LocallyCovering G G' p v v'


@[refl] def LocallyCovering.rfl : LocallyCovering G G p v v := LocallyCovering.refl v v (by rfl)

-- @[trans]
-- def LeocallyCovering.trans (cm₁ : LocallyCovering G₁ G₂ r v₁ v₂) (cm₂ : LocallyCovering G₂ G₃ r v₂ v₃) : LocallyCovering G₁ G₂ r v₁ v₃ :=
--   r.recOn
--     (
--       -- .refl v₁ v₃ (Eq.trans cm₁.h)
--       sorry
--     )
--     sorry
--   -- sorry
