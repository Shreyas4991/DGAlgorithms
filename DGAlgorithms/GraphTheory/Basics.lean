import Mathlib


namespace DGAlgorithms

variable (G : SimpleGraph V) [Fintype V] [DecidableEq V]

abbrev E (G : SimpleGraph V) := G.edgeSet

def isEdgeSubset (G : SimpleGraph V) (E' : Set (Sym2 V)) := E' ⊆ E G

def ball (G : SimpleGraph V) (center : V) (radius : ℕ) :=
  {v : V | G.dist center v ≤ radius}

noncomputable def diameter (G : SimpleGraph V) :=
  sSup {l | ∃ v w : V, G.dist v w = l}

noncomputable def isIndepVertexSet (G : SimpleGraph V) (I : Finset V) :=
  ∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w

noncomputable def isIndepVertexSet_edgeDef (G : SimpleGraph V) (I : Finset V) :=
  ∀ v w : V, G.Adj v w → ¬v ∈ I ∨  ¬ w ∈ I

omit [Fintype V] in
lemma test_equiv_lemma_ind : ∀ G : SimpleGraph V, ∀ I,
  isIndepVertexSet G I ↔ isIndepVertexSet_edgeDef G I := by
  intro G I
  constructor <;> simp_all [isIndepVertexSet, isIndepVertexSet_edgeDef]
  · intro h v w adjvw
    by_contra hcontra
    tauto
  · intro h v hvI w hwI hadj
    specialize h v w hadj
    cases h <;> tauto


noncomputable def isDominatingSet (G : SimpleGraph V) (C : Finset V) :=
  ∀ w : V, w ∈ C ∨ ∃ v ∈ C, G.Adj w v

noncomputable def isVertexCover (G : SimpleGraph V) (C : Finset V) :=
  ∀ v w : V, G.Adj v w → v ∈ C ∨ w ∈ C

noncomputable def isEdgeCover (G : SimpleGraph V) (E' : Set (Sym2 V)) :=
  E' ⊆ E G ∧ ∀ v : V, ∃ e ∈ E', v ∈ e

noncomputable def isEdgeDomSet (G : SimpleGraph V) (E' : Set (Sym2 V)) :=
  E' ⊆ E G ∧ ∀ e ∈ E G, e ∉ E' → ∃ e' ∈ E', ∃ v : V, v ∈ e' ∧ v ∈ e

noncomputable def isMinimalSet (Pred : Finset V → Prop)
  (X : Finset V) :=
    Pred X ∧ ∀ X' : Finset V, X' ⊂ X → ¬ Pred X'


noncomputable def isMaximalSet (Pred : Finset V → Prop)
  (X : Finset V) :=
    Pred X ∧ ∀ X' : Finset V, X ⊂ X' → ¬ Pred X'

noncomputable def isMaximalSet_noInsert (Pred : Finset V → Prop)
  (X : Finset V) :=
    Pred X ∧ ∀ v : V, v ∉ X → ¬ Pred (Insert.insert v X)


noncomputable def isMinimumSet (Pred : Finset V → Prop)
  (X : Finset V) :=
    Pred X ∧ ∀ X' : Finset V, X'.card < X.card → ¬ Pred X'

noncomputable def isMaximumSet (Pred : Finset V → Prop)
  (X : Finset V) :=
    Pred X ∧ ∀ X' : Finset V, X'.card > X.card → ¬ Pred X'

noncomputable def isMaximalIndSet (G : SimpleGraph V) (I : Finset V) :=
  isMaximalSet (isIndepVertexSet G) I

noncomputable def isMinimalVC (G : SimpleGraph V) (C : Finset V) :=
  isMinimalSet (isVertexCover G) C

noncomputable def isMinimalDomSet (G : SimpleGraph V) (C : Finset V) :=
  isMinimalSet (isDominatingSet G) C

noncomputable def isMaximumIndSet (G : SimpleGraph V) (I : Finset V) :=
  isMaximumSet (isIndepVertexSet G) I

noncomputable def isMinimumVC (G : SimpleGraph V) (C : Finset V) :=
  isMinimumSet (isVertexCover G) C

noncomputable def isMinimumDomSet (G : SimpleGraph V) (C : Finset V) :=
  isMinimumSet (isDominatingSet G) C

omit [Fintype V] in
lemma isMaximalImpliesNoIns (Pred : Finset V → Prop) (X : Finset V) :
  isMaximalSet Pred X → isMaximalSet_noInsert Pred X := by
  simp [isMaximalSet, isMaximalSet_noInsert]
  intro predicate
  intro h_isMaximal
  constructor
  · exact predicate
  · intro v v_not_X
    specialize h_isMaximal (insert v X)
    have hsub : X ⊂ insert v X := by
      exact Finset.ssubset_insert v_not_X
      done
    specialize h_isMaximal hsub
    exact h_isMaximal
    done

omit [Fintype V] [DecidableEq V] in
lemma maximum_implies_maximal (Pred : Finset V → Prop) (X : Finset V) :
  isMaximumSet Pred X → isMaximalSet Pred X := by
  intro h_maximum
  simp_all [isMaximumSet, isMaximalSet]
  cases h_maximum with
  | intro hpred hmax =>
      intro Y Y_sub Y_neq
      have : X.card < Y.card := by
        exact Finset.card_lt_card Y_sub
        done
      specialize hmax Y this
      exact hmax Y_neq

omit [Fintype V] [DecidableEq V] in
lemma minimum_implies_minimal (Pred : Finset V → Prop) (X : Finset V) :
  isMinimumSet Pred X → isMinimalSet Pred X := by
  intro h_minimum
  simp_all [isMinimalSet, isMinimumSet]
  intro Y Y_sub
  cases h_minimum with
  | intro hpred hmin =>
      have : Y.card < X.card := by
        exact Finset.card_lt_card Y_sub
      specialize hmin Y this
      exact hmin


-- Exercise 2.1 a)
theorem VC_complement_indep (G : SimpleGraph V)
  (C : Finset V) : isVertexCover G C ↔ isIndepVertexSet G (Cᶜ) := by
  constructor <;> simp_all [isVertexCover, isIndepVertexSet]
  · intro hVC v v_not_C w w_not_C adj_vw
    specialize hVC v w adj_vw
    tauto
    done
  · intro hIndep v w adj_vw
    by_contra h_C
    tauto
    done

lemma Finset_compl_sub [Fintype α] [DecidableEq α] (Y C : Finset α)
  : Cᶜ ⊆ Y → Yᶜ ⊆ C := by
  simp [Finset.subset_iff]
  intro h x x_notin_Y
  by_contra h'
  specialize h h'
  exact x_notin_Y h
  done

lemma Finset_compl_ssub [Fintype α] [DecidableEq α] (Y C : Finset α)
  : Cᶜ ⊂ Y → Yᶜ ⊂ C := by
  intro h
  cases h with
  | intro left right =>
    constructor
    · apply Finset_compl_sub
      exact left
    · by_contra h'
      have h'' : Y ⊆ Cᶜ := by
        have : C = Cᶜᶜ := by rw[compl_compl]
        rw [this] at h'
        apply Finset_compl_sub at h'
        rw [compl_compl] at h'
        exact h'
      exact right h''




lemma Finset_compl_compl_sub [Fintype α] [DecidableEq α] (Y C : Finset α) : Y ⊂ C → Cᶜ ⊂ Yᶜ := by
  intro h
  nth_rw 1 [←compl_compl Y] at h
  apply Finset_compl_ssub
  exact h
  done

lemma Finset_compl_card [Fintype α] [DecidableEq α] (Y C : Finset α)
  : Cᶜ.card < Y.card → Yᶜ.card < C.card := by
  intro hcard
  have univ₁ : Y.card ≤ Fintype.card α := by
    exact Finset.card_le_univ Y
  have bad_ineq : ¬ Y.card - ↑(Fintype.card α) ≥ 1 := by
    simp [univ₁]
    done
  rw [Finset.card_compl] at *
  omega
  done

lemma Finset_compl_compl_card [Fintype α] [DecidableEq α] (Y C : Finset α)
  : C.card < Y.card → Yᶜ.card < Cᶜ.card := by
  intro hcard
  apply Finset_compl_card
  rw [compl_compl]
  exact hcard

-- Exercise 2.1 b)
theorem minimal_VC_complement_maximal_indep
  (C : Finset V) : isMinimalVC G C ↔ isMaximalIndSet G Cᶜ := by
  simp [
      isMinimalVC,
      isMaximalIndSet,
      isMinimalSet,
      isMaximalSet]
  constructor
  · rintro ⟨isVC, isMinVC⟩
    constructor
    · rw[VC_complement_indep G C] at isVC
      assumption
    · intro Y Ysub
      specialize isMinVC Yᶜ (Finset_compl_ssub Y C Ysub)
      rw [VC_complement_indep G Yᶜ] at isMinVC
      rw [compl_compl] at isMinVC
      exact isMinVC
  · rintro ⟨hIndep, hMaxIndep⟩
    constructor
    · rw[←VC_complement_indep G C] at hIndep
      assumption
    · intro Y Y_sub
      specialize hMaxIndep Yᶜ (Finset_compl_compl_sub Y C Y_sub)
      rw [VC_complement_indep]
      exact hMaxIndep
      done

-- Exercise 2.1 c)

theorem minimum_VC_complement_maximum_indep (C : Finset V) :
  isMinimumVC G C ↔ isMaximumIndSet G Cᶜ := by
  simp [
      isMinimumVC,
      isMaximumIndSet,
      isMinimumSet,
      isMaximumSet]
  constructor
  · rintro ⟨VC, minVC⟩
    constructor
    · rw[VC_complement_indep G C] at VC
      exact VC
    · intro Y Ycard
      specialize minVC Yᶜ (Finset_compl_card Y C Ycard)
      rw[VC_complement_indep G Yᶜ, compl_compl] at minVC
      exact minVC
    done
  · rintro ⟨Ind, maxInd⟩
    constructor
    · rw[VC_complement_indep G C]
      exact Ind
    · intro Y Ycard
      apply Finset_compl_compl_card at Ycard
      specialize maxInd Yᶜ Ycard
      rw [VC_complement_indep]
      exact maxInd


end DGAlgorithms
