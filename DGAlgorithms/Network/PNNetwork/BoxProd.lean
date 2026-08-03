import Mathlib
import DGAlgorithms.Network.PNNetwork

namespace DGAlgorithms

def PNNetwork.boxProd (N₁ : PNNetwork V₁ P₁) (N₂ : PNNetwork V₂ P₂) : PNNetwork (V₁ × V₂) (P₁ × P₂) where
  PortValid := fun ((v₁, v₂), (p₁, p₂)) ↦ N₁.PortValid (v₁, p₁) ∧ N₂.PortValid (v₂, p₂)
  pmap := fun vp ↦
    let uq₁ := N₁.pmap ⟨(vp.val.1.1, vp.val.2.1), vp.prop.left⟩
    let uq₂ := N₂.pmap ⟨(vp.val.1.2, vp.val.2.2), vp.prop.right⟩
    ⟨((uq₁.node, uq₂.node), (uq₁.index, uq₂.index)), And.intro uq₁.is_valid uq₂.is_valid⟩
  pmap_involutive := by
    intro vp
    simp_all
    eta_struct
    rfl

/-- Box product of PNNetworks. -/
infixl:70 " □ " => PNNetwork.boxProd

lemma PNNetwork.boxProd.pmap_def (N₁ : PNNetwork V₁ P₁) (N₂ : PNNetwork V₂ P₂) :
    ∀ vp, (N₁ □ N₂).pmap vp = ⟨(
      ((N₁.pmap ⟨(vp.node.1, vp.index.1), vp.is_valid.1⟩).node, (N₂.pmap ⟨(vp.node.2, vp.index.2), vp.is_valid.2⟩).node),
      ((N₁.pmap ⟨(vp.node.1, vp.index.1), vp.is_valid.1⟩).index, (N₂.pmap ⟨(vp.node.2, vp.index.2), vp.is_valid.2⟩).index)),
      And.intro (N₁.pmap ⟨(vp.node.1, vp.index.1), vp.is_valid.1⟩).is_valid (N₂.pmap ⟨(vp.node.2, vp.index.2), vp.is_valid.2⟩).is_valid⟩ := by
    intro vp; rfl

lemma PNNetwork.boxProd.pmap_eq_iff (N₁ : PNNetwork V₁ P₁) (N₂ : PNNetwork V₂ P₂) :
    ∀ vp up, (N₁ □ N₂).pmap vp = up ↔
    N₁.pmap ⟨(vp.node.1, vp.index.1), vp.is_valid.1⟩ = ⟨(up.node.1, up.index.1), up.is_valid.1⟩ ∧
    N₂.pmap ⟨(vp.node.2, vp.index.2), vp.is_valid.2⟩ = ⟨(up.node.2, up.index.2), up.is_valid.2⟩ := by
  intro vp up
  constructor
  · intro h
    obtain ⟨hl, hr⟩ := h
    constructor
    all_goals rfl
  · intro h
    obtain ⟨hl, hr⟩ := h
    rw [boxProd.pmap_def]
    congr
    simp [hl]
    simp [hr]
    simp [hl]
    simp [hr]

instance [SimplePN N₁] [SimplePN N₂] : SimplePN (N₁ □ N₂) where
  loopless := by
    intro vp hcontra
    obtain ⟨⟨⟨v₁, v₂⟩, ⟨p₁, p₂⟩⟩, ⟨h₁, h₂⟩⟩ := vp
    reduce at hcontra
    apply SimplePN.loopless (N := N₁) ⟨(v₁, p₁), h₁⟩
    simp_all
  simple := by
    intro vp₁ vp₂ heq hpeq
    rw [PNNetwork.boxProd.pmap_def, PNNetwork.boxProd.pmap_def] at hpeq
    apply Prod.ext_iff.mp at hpeq
    have h₁ := SimplePN.simple (N := N₁) ⟨(vp₁.node.1, vp₁.index.1), vp₁.is_valid.1⟩ ⟨(vp₂.node.1, vp₂.index.1), vp₂.is_valid.1⟩ (by simp [heq]) (by simp_all)
    have h₂ := SimplePN.simple (N := N₂) ⟨(vp₁.node.2, vp₁.index.2), vp₁.is_valid.2⟩ ⟨(vp₂.node.2, vp₂.index.2), vp₂.is_valid.2⟩ (by simp [heq]) (by simp_all)
    apply Prod.ext_iff.mp ∘ Subtype.ext_iff.mp at h₁
    apply Prod.ext_iff.mp ∘ Subtype.ext_iff.mp at h₂

    apply Subtype.ext
    apply Prod.ext
    · simp_all
    · apply Prod.ext
      all_goals simp_all
