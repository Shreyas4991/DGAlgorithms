import Mathlib
import DGAlgorithms.Network.PNNetwork
-- import Canonical

namespace DGAlgorithms

/-- A covering map is a surjective, degree-preserving and adjacency-preserving
map between networks.

Note that the covering map also preserves the order of adjacent ports.
-/
structure CoveringMap (G : PNNetwork V) (G' : PNNetwork V') where
  map : V → V'
  map_surj : Function.Surjective map
  map_deg : ∀ v : V, G.deg v = G'.deg (map v)
  map_adj : ∀ p : Port V,
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

def CoveringMap.comp (m₂ : CoveringMap G₂ G₃) (m₁ : CoveringMap G₁ G₂) : CoveringMap G₁ G₃ where
  map := m₂.map ∘ m₁.map
  map_surj := Function.Surjective.comp m₂.map_surj m₁.map_surj
  map_deg := by
    intro v
    rw [m₁.map_deg, m₂.map_deg]
    rfl
  map_adj := by
    intro p
    dsimp
    rw [←m₂.map_adj (m₁.map p.node, p.port)]
    rw [←m₁.map_adj]

infixr:90 " ∘ "  => CoveringMap.comp

@[simp] lemma CoveringMap.comp_self (m : CoveringMap G G') : m ∘ CoveringMap.self G = m := by rfl

@[simp] lemma CoveringMap.self_comp (m : CoveringMap G G') : CoveringMap.self G' ∘ m = m := by rfl
