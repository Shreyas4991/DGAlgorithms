import Mathlib
import DGAlgorithms.Network.PNNetwork
import DGAlgorithms.Models.MessagePassing.PortNumbering

namespace DGAlgorithms

open Classical in
noncomputable
def naiveColorReduction : PNAlgorithm P ℕ ℕ where
  State := fun _ ↦ ℕ
  Msg := ℕ
  init := fun _ color ↦ color
  send := fun color ↦ color
  recv := fun color msg ↦
    if h : ∀ n, color > msg n then
      Nat.find (p := fun n ↦ ∀ p, msg p ≠ n) (by
        use color
        intro p
        apply ne_of_lt (h p)
      )
    else
      color
  output := fun color ↦ color

-- TODO: This could also be defined as a graph homomorphism to a complete graph on α
def Coloring (N : PNNetwork V P) : (V → α) → Prop :=
  fun color ↦ ∀ v : V, ∀ u ∈ N.neighborSet v, color v ≠ color u


lemma naiveColorReduction.Coloring (N : PNNetwork V P) {c : naiveColorReduction.CfgOn N} (h : Coloring N c.output) :
    Coloring N (naiveColorReduction.step N c).output := by
  intro v u hvu
  specialize h v u hvu
  wlog hlt : c.output v < c.output u
  · symm
    exact this N u v ((PNNetwork.mem_neighborSet_symm N v u).mp hvu) h.symm (by omega)
  -- sorry
  simp [naiveColorReduction, PNAlgorithm.CfgOn.output] at ⊢ hlt
  split_ifs with hv hu
  · -- Both updated simultaneously, but this contradicts maximality
    exfalso
    obtain ⟨vp, hvp⟩ := hvu
    have := hv ⟨vp.index, by
      rw [←hvp.left]; exact PNNetwork.port_index_mem_neighborIndexSet N vp
    ⟩
    obtain ⟨a,b⟩ := hvp
    subst_vars
    -- simp at this
    -- eta_struct at this
    -- eta_struct at this
    apply not_lt_of_gt hlt this
  · exfalso
    obtain ⟨vp, hvp⟩ := hvu
    have := hv ⟨vp.index, by
      rw [←hvp.left]; exact PNNetwork.port_index_mem_neighborIndexSet N vp
    ⟩
    obtain ⟨a,b⟩ := hvp
    -- subst a b
    subst_vars
    -- simp at this
    -- eta_struct at this
    -- eta_struct at this
    apply not_lt_of_gt hlt this
  · classical
    intro hcontra
    symm at hcontra
    rw [Nat.find_eq_iff] at hcontra
    have h := hcontra.left
    rw [PNNetwork.mem_neighborSet_symm] at hvu
    obtain ⟨vp, hvp⟩ := hvu
    have := h ⟨vp.index, by
      rw [←hvp.left]; exact PNNetwork.port_index_mem_neighborIndexSet N vp
    ⟩
    apply this
    obtain ⟨a,b⟩ := hvp
    subst a b
    rfl
  omega
