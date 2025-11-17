import Mathlib
import DGAlgorithms.Network.PNNetworkExperiment

namespace DGAlgorithms



variable {V V': Type u} {α : V → Type v} {α' : V' → Type v}
variable [∀ v : V, Fintype (α v)] [∀ v : V', Fintype (α' v)]

/-- A covering map is a surjective, degree-preserving and adjacency-preserving
map between networks.

Note that the covering map also preserves the order of adjacent ports.
-/
structure CoveringMap (G : PNNetwork V α) (G' : PNNetwork V' α') where
  map : V → V'
  map_surj : Function.Surjective map
  map_deg : ∀ v : V, deg G v = deg G' (map v)
  map_adj : ∀ p : Port V, G.PortValid p →
    let mapPort : Port V → Port V' := fun p ↦ (map p.node, p.port)
    mapPort (G.pmap p) = G'.pmap (mapPort p)

/-- Lift the map from vertices of the network to its ports. -/
def CoveringMap.mapPort (CM : CoveringMap G G') : G.Port' → G'.Port' :=
  fun p ↦ ⟨(CM.map p.node, p.port), by
    unfold PNNetwork.PortValid at *
    rw [←CM.map_deg]
    simpa using p.prop⟩

section Examples

def CoveringMap.self (G : PNNetwork V) : CoveringMap G G where
  map := id
  map_surj := by intro v; simp
  map_deg := by simp
  map_adj := by simp

def doubleCover (N : PNNetwork V) : PNNetwork (V × Bool) where
  deg := fun ⟨v, _⟩ ↦ N.deg v
  pmap := fun ⟨⟨v, l⟩, i⟩ =>
    let ⟨u, j⟩ := N.pmap ⟨v, i⟩
    ⟨⟨u, ¬l⟩, j⟩
  pmap_involutive := by simp_all
  is_well_defined := by simp_all [N.is_well_defined_iff]

def doubleCover.isCoveringMap (N : PNNetwork V) : CoveringMap (doubleCover N) N where
  map := fun ⟨v, l⟩ ↦ v
  map_surj := by
    intro v
    aesop
  map_deg := fun v ↦ Eq.refl (N.deg v.1)
  map_adj := by
    intro p mapPort
    simp_all [mapPort]
    rfl

end Examples

def CoveringMap.of_equiv (N₁ N₂ : PNNetwork V) (h_equiv : N₁ ≈ N₂) : CoveringMap N₁ N₂ where
  map := id
  map_surj := Function.surjective_id
  map_deg := by
    apply congrFun
    exact h_equiv.left
  map_adj := by
    intro p hp
    exact h_equiv.right p.node p.port hp

def CoveringMap.comp (m₂ : CoveringMap G₂ G₃) (m₁ : CoveringMap G₁ G₂) : CoveringMap G₁ G₃ where
  map := m₂.map ∘ m₁.map
  map_surj := Function.Surjective.comp m₂.map_surj m₁.map_surj
  map_deg := by
    intro v
    rw [m₁.map_deg, m₂.map_deg]
    rfl
  map_adj := by
    intro p hp
    dsimp
    rw [←m₂.map_adj (m₁.map p.node, p.port)]
    rw [←m₁.map_adj]
    exact hp
    unfold PNNetwork.PortValid at *
    rw [←m₁.map_deg]
    exact hp

infixr:90 " ∘ "  => CoveringMap.comp

@[simp] lemma CoveringMap.comp_self (m : CoveringMap G G') : m ∘ CoveringMap.self G = m := by rfl

@[simp] lemma CoveringMap.self_comp (m : CoveringMap G G') : CoveringMap.self G' ∘ m = m := by rfl

inductive LocallyCovering (G : PNNetwork V) (G' : PNNetwork V') : ℕ → V → V' → Type where
  | refl (v : V) (v' : V') (h : G.deg v = G'.deg v') : LocallyCovering G G' 0 v v'
  | succ (v : V) (v' : V') (hdeg : G.deg v = G'.deg v') (h' : ∀ i < G.deg v, LocallyCovering G G' r (G.pmap (v, i)).node (G'.pmap (v', i)).node) : LocallyCovering G G' r.succ v v'


@[refl] def LocallyCovering.rfl : LocallyCovering G G 0 v v := LocallyCovering.refl v v (Eq.refl _)

-- @[trans]
-- def LeocallyCovering.trans (cm₁ : LocallyCovering G₁ G₂ r v₁ v₂) (cm₂ : LocallyCovering G₂ G₃ r v₂ v₃) : LocallyCovering G₁ G₂ r v₁ v₃ :=
--   r.recOn
--     (
--       -- .refl v₁ v₃ (Eq.trans cm₁.h)
--       sorry
--     )
--     sorry
--   -- sorry
