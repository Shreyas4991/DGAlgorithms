import DGAlgorithms.Algorithm
import DGAlgorithms.ForMathlib.CycleGraph

set_option autoImplicit false

variable {V V' I : Type*}

@[ext]
structure CoveringMap
    (N : NonSimplePortNumbered V) (N' : NonSimplePortNumbered V') (f : V → I) (f' : V' → I) :=
  (toFun : V → V')
  (surj' : toFun.Surjective)
  (degree_map' : ∀ v : V, N'.degree (toFun v) = N.degree v)
  (ofPort_map' : ∀ u i, N'.ofPort (toFun u) i = toFun (N.ofPort u (Fin.cast (degree_map' _) i)))
  (coe_reversePort_map' : ∀ u i,
    (N'.reversePort (toFun u) i : ℕ) = N.reversePort u (Fin.cast (degree_map' _) i))
  (label_map' : ∀ v : V, f' (toFun v) = f v)

instance {N : NonSimplePortNumbered V} {N' : NonSimplePortNumbered V'} {f : V → I} {f' : V' → I} :
    FunLike (CoveringMap N N' f f') V V' :=
  ⟨CoveringMap.toFun, CoveringMap.ext⟩

namespace CoveringMap

variable {N : NonSimplePortNumbered V} {N' : NonSimplePortNumbered V'} {f : V → I} {f' : V' → I}

variable (φ : CoveringMap N N' f f')

@[simp] lemma surj : Function.Surjective φ := φ.surj'
@[simp] lemma degree_map (v : V) : N'.degree (φ v) = N.degree v := φ.degree_map' v
@[simp] lemma ofPort_map (u : V) (i : Fin (N'.degree (φ u))) :
    N'.ofPort (φ u) i = φ (N.ofPort u (Fin.cast (by simp) i)) :=
  φ.ofPort_map' u i
@[simp] lemma coe_reversePort_map (u : V) (i : Fin (N'.degree (φ u))) :
    (N'.reversePort (φ u) i : ℕ) = N.reversePort u (Fin.cast (by simp) i) :=
  φ.coe_reversePort_map' u i
@[simp] lemma label_map (v : V) : f' (φ v) = f v := φ.label_map' v

lemma map_ofPort (u : V) (i : Fin (N.degree u)) :
    φ (N.ofPort u i) = N'.ofPort (φ u) (Fin.cast (by simp) i) := by simp

lemma coe_map_reversePort (u : V) (i : Fin (N.degree u)) :
    (N.reversePort u i : ℕ) = N'.reversePort (φ u) (Fin.cast (by simp) i) := by simp

lemma reversePort_map (u : V) (i : Fin (N'.degree (φ u))) :
    N'.reversePort (φ u) i =
      Fin.cast (by simp) (N.reversePort u (Fin.cast (φ.degree_map _) i)) := by
  rw [Fin.ext_iff, Fin.coe_cast]
  simp

lemma map_reversePort (u : V) (i : Fin (N.degree u)) :
    N.reversePort u i = Fin.cast (by simp) (N'.reversePort (φ u) (Fin.cast (by simp) i)) := by
  rw [Fin.ext_iff, Fin.coe_cast]
  simp

/--
If there is an right inverse of the underlying function of a covering map, we can upgrade the
inverse into a covering map.
-/
def coveringMap.inverse {V V' : Type*} {N : PortNumbered V} {N' : PortNumbered V'}
    {f : V → I} {f' : V' → I} (φ : CoveringMap N N' f f') (φ' : V' → V)
    (hr : Function.RightInverse φ φ') :
    CoveringMap N' N f' f where
  toFun := φ'
  surj' := hr.surjective
  degree_map' v := by
    rw [←φ.degree_map, Function.leftInverse_of_surjective_of_rightInverse φ.surj hr v]
  ofPort_map' u i := by
    refine hr.injective ?_
    rw [φ.map_ofPort (φ' u),
      Function.leftInverse_of_surjective_of_rightInverse φ.surj hr (N'.ofPort u _)]
    rw [←N'.ofPort_cast (φ (φ' u)) u]
    case h => exact Function.leftInverse_of_surjective_of_rightInverse φ.surj hr _
    rfl
  coe_reversePort_map' v i := by
    rw [φ.coe_map_reversePort]
    have : φ (φ' v) = v := Function.leftInverse_of_surjective_of_rightInverse φ.surj hr _
    rw [←N'.coe_reversePort_cast _ _ this.symm]
    rfl
  label_map' v := by
    rw [←φ.label_map]
    have : φ (φ' v) = v := Function.leftInverse_of_surjective_of_rightInverse φ.surj hr _
    rw [this]

def hom {V V' : Type*} {N : PortNumbered V} {N' : PortNumbered V'}
    {f : V → I} {f' : V' → I} (φ : CoveringMap N N' f f') :
    (N : SimpleGraph V) →g (N' : SimpleGraph V') where
  toFun := φ
  map_rel' := fun h => by
    rw [←N.adj_eq] at h
    obtain ⟨i, rfl⟩ := h
    rw [φ.map_ofPort]
    exact N'.ofPort_adj _

lemma coveringMap.connected {V V' : Type*} {N : PortNumbered V} {N' : PortNumbered V'}
    {f : V → I} {f' : V' → I} (φ : CoveringMap N N' f f') (h : N.Connected) :
    N'.Connected :=
  SimpleGraph.Connected.map φ.hom φ.surj h


def discrete {V W : Type*} (g : V → W) (hg : g.Surjective) (i : I) :
    CoveringMap (.discrete V) (.discrete W) (fun _ => i) (fun _ => i) where
  toFun := g
  surj' := hg
  degree_map' := by simp
  ofPort_map' := by simp
  coe_reversePort_map' := by simp
  label_map' := by simp

def loopSelf {V W : Type*} (g : V → W) (hg : g.Surjective) (i : I) :
    CoveringMap (.loopSelf V) (.loopSelf W) (fun _ => i) (fun _ => i) where
  toFun := g
  surj' := hg
  degree_map' := by simp
  ofPort_map' := by simp
  coe_reversePort_map' := by simp
  label_map' := by simp

def loopOther {V W : Type*} (g : V → W) (hg : g.Surjective) (i : I) :
    CoveringMap (.loopOther V) (.loopOther W) (fun _ => i) (fun _ => i) where
  toFun := g
  surj' := hg
  degree_map' := by simp
  ofPort_map' := by simp
  coe_reversePort_map' := by simp
  label_map' := by simp

section Execution

variable {S M O : Type*} {A : Algorithm I S M O}
variable (φ : CoveringMap N N' f f')

lemma send_eq {d d' : ℕ} {s s' : S} {i : Fin d} {i' : Fin d'} (hd : d = d') (hs : s = s')
    (hi : (i : ℕ) = i') :
    A.send d s i = A.send d' s' i' := by
  cases hd
  rw [←Fin.ext_iff] at hi
  congr

lemma fullReceive_eq {d d' : ℕ} {f f'} {s s' : S} (hd : d = d') (hs : s = s')
    (hf : ∀ x, f x = f' (Fin.cast hd x)) :
    A.fullReceive d f s = A.fullReceive d' f' s' := by
  cases hd
  simp only [Fin.cast_eq_self, ←Function.funext_iff] at hf
  congr

lemma rounds_eq (t : ℕ) (v : V) : A.rounds N' f' t (φ v) = A.rounds N f t v := by
  induction t generalizing v with
  | zero => simp [Algorithm.rounds_zero, Algorithm.initialVector]
  | succ n ih =>
      simp only [Algorithm.rounds_succ, Algorithm.nextVector]
      refine fullReceive_eq (by simp) (ih v) ?_
      intro i
      exact send_eq (by simp) (by simp [ih]) (by simp)

lemma stoppedBy_iff (t : ℕ) : A.stoppedBy N f t ↔ A.stoppedBy N' f' t := by
  simp only [Algorithm.stoppedBy, Algorithm.isStopped, Function.Surjective.forall φ.surj,
    rounds_eq φ t]

lemma outputAt_eq' {t : ℕ} (ht : A.stoppedBy N f t) (v) :
    A.outputAt N f t ht v = A.outputAt N' f' t ((stoppedBy_iff φ _).1 ht) (φ v) := by
  rw [Algorithm.outputAt, Algorithm.outputAt, Algorithm.outputs,
    Algorithm.outputs, Algorithm.getOutput, Algorithm.getOutput]
  simp only [rounds_eq]

lemma outputAt_eq {t₁ t₂ : ℕ} (ht₁ : A.stoppedBy N f t₁) (ht₂ : A.stoppedBy N' f' t₂) (v) :
    A.outputAt N' f' t₂ ht₂ (φ v) = A.outputAt N f t₁ ht₁ v := by
  have ht₁' : A.stoppedBy N' f' t₁ := by rwa [←stoppedBy_iff φ]
  rw [A.outputAt_eq N' ht₂ ht₁']
  exact (outputAt_eq' φ _ _).symm

end Execution

end CoveringMap

section Cycle

lemma fin_two_injective {β : Type*} {f : Fin 2 → β} :
    Function.Injective f ↔ f 0 ≠ f 1 := by
  simp only [Function.Injective, Fin.forall_fin_two]
  aesop

@[simps! degree ofPort toSimpleGraph]
def cyclicNetwork (n : ℕ) : PortNumbered (Fin (n + 3)) :=
  PortNumbered.fromSimpleGraph'
    (SimpleGraph.cycleGraph (n + 3)) (fun _ => 2)
    (fun v => ![⟨v + 1, by simp [SimpleGraph.cycleGraph_neighborSet]⟩,
                ⟨v - 1, by simp [SimpleGraph.cycleGraph_neighborSet]⟩])
    (fun v => fin_two_injective.2 (by simpa using SimpleGraph.neighbours_diff.symm))
    (fun v => by rw [SimpleGraph.cycleGraph_degree_three_le])

lemma cyclicNetwork_reversePort (n : ℕ) (v : Fin (n + 3)) (i : Fin 2) :
    (cyclicNetwork n).reversePort v i = Equiv.swap 0 1 i := by
  refine PortNumbered.ofPort_injective _ ?_
  rw [NonSimplePortNumbered.ofPort_reversePort, cyclicNetwork_ofPort]
  revert i
  rw [Fin.forall_fin_two]
  simp

def cycleCovering {β : Type*} {n : ℕ} (f : Fin (n + 3) → β) (hf : ∀ v w, f v = f w) :
    CoveringMap
      (cyclicNetwork n : NonSimplePortNumbered (Fin (n + 3)))
      (NonSimplePortNumbered.loopOther Unit)
      f (fun _ => f 0) where
  toFun _ := ⟨⟩
  surj' _ := by simp
  degree_map' _ := by simp
  ofPort_map' u _ := by simp
  coe_reversePort_map' u i := by
    rw [cyclicNetwork_reversePort]
    rfl
  label_map' v := hf _ _

/-- The (unique) port numbered network on the graph with one edge. -/
@[simps toSimpleGraph degree ofPort reversePort]
def singleEdgeNetwork : PortNumbered (Fin 2) where
  degree _ := 1
  ofPort u i := Equiv.swap 0 1 u
  reversePort u i := 0
  ofPort_reversePort := by simp
  coe_reversePort_reversePort := by simp
  toSimpleGraph := SimpleGraph.pathGraph 2
  no_multi_edges u i j _ := Subsingleton.elim _ _
  adj_eq := by
    ext x y
    simp only [Fin.isValue, SimpleGraph.pathGraph_two_eq_top, SimpleGraph.top_adj, ne_eq,
      NonSimplePortNumbered.adj]
    revert x y
    decide

def singleEdgeCovering {β : Type*} (f : Fin 2 → β) (hf : ∀ v w, f v = f w) :
    CoveringMap
      (singleEdgeNetwork : NonSimplePortNumbered (Fin 2))
      (NonSimplePortNumbered.loopSelf Unit)
      f (fun _ => f 0) where
  toFun _ := ⟨⟩
  surj' _ := by simp
  degree_map' _ := by simp
  ofPort_map' u _ := by simp
  coe_reversePort_map' u _ := by simp
  label_map' v := hf _ _

/--
If G' is a simple graph isomorphic to the underlying graph of N, there is a covering map from
N to G'.
-/
def coveringMap_transfer {V V' : Type*} {N : PortNumbered V} {G' : SimpleGraph V'}
    {f : V → I}
    (e : G' ≃g (N : SimpleGraph V)) :
    CoveringMap
      (N : NonSimplePortNumbered V)
      (PortNumbered.transfer e : NonSimplePortNumbered V')
      f (f ∘ e) where
  toFun := e.symm
  surj' := e.symm.surjective
  degree_map' v := by simp
  ofPort_map' u i := by simp [NonSimplePortNumbered.ofPort_cast]
  coe_reversePort_map' u i := by
    simp [NonSimplePortNumbered.ofPort_cast, NonSimplePortNumbered.reversePort_cast]
  label_map' := by simp

variable {S M O : Type*}

theorem constant_on_cycleCovering' (A : Algorithm I S M O) (n : ℕ)
    (f : Fin (n + 3) → I) (hf : ∀ v w, f v = f w)
    (t : ℕ) (h : A.stoppedBy (cyclicNetwork n) f t) (v : _) :
    A.outputAt _ f t h v =
      A.outputAt (.loopOther Unit) (fun _ => f 0) t
        (((cycleCovering f hf).stoppedBy_iff _).1 h) ⟨⟩ := by
  simp only [(cycleCovering f hf).outputAt_eq' h]

/--
If algorithm A with constant input stops on the cyclic network on ≥ 3 nodes, all outputs are the
same.
-/
theorem constant_on_cycleCovering (A : Algorithm I S M O) (n : ℕ)
    (f : Fin (n + 3) → I) (hf : ∀ v w, f v = f w)
    (t : ℕ) (h : A.stoppedBy (cyclicNetwork n) f t) :
    ∃ o : O, ∀ v, A.outputAt _ f t h v = o := by
  simp only [(cycleCovering f hf).outputAt_eq' h]
  exact ⟨A.outputAt (.loopOther Unit) (fun _ => f 0) t _ ⟨⟩, fun v => rfl⟩

/--
If algorithm A with constant input stops on the network with a single edge, all outputs are the
same.
-/
theorem constant_on_singleEdgeNetwork (A : Algorithm I S M O) (f : Fin 2 → I)
    (hf : ∀ v w, f v = f w) (t : ℕ) (h : A.stoppedBy singleEdgeNetwork f t) :
    ∃ o : O, ∀ v, A.outputAt _ f t h v = o := by
  let φ := singleEdgeCovering f hf
  have h' := h
  rw [φ.stoppedBy_iff t] at h'
  simp only [←φ.outputAt_eq h h']
  use A.outputAt _ (fun _ => f 0) t h' ⟨⟩
  intro v
  simp

/--
If the cycle graph on three vertices and the cycle graph on four vertices are in our graph
family, there is no algorithm on this family which can count the number of vertices.
-/
theorem unsolvable_count_vertices (family : (V : Type) → Set (SimpleGraph V))
  (h3 : SimpleGraph.cycleGraph 3 ∈ family _) (h4 : SimpleGraph.cycleGraph 4 ∈ family _) :
  ¬ ∃ (A : Algorithm PUnit S M ℕ),
    solvesProblem A family
      Problem.trivialInp ⟨fun V _ => {fun _ => Nat.card V}⟩ := by
  rintro ⟨A, hA⟩
  obtain ⟨t₁, ht₁, h₁⟩ := hA (cyclicNetwork 0) default (by simpa) (by simp)
  simp only [Nat.reduceAdd, Pi.default_def, PUnit.default_eq_unit, zero_add,
    Nat.card_eq_fintype_card, Fintype.card_fin, Set.mem_singleton_iff] at h₁
  obtain ⟨t₂, ht₂, h₂⟩ := hA (cyclicNetwork 1) default (by simpa) (by simp)
  simp only [Nat.reduceAdd, Pi.default_def, PUnit.default_eq_unit, zero_add,
    Nat.card_eq_fintype_card, Fintype.card_fin, Set.mem_singleton_iff] at h₂
  apply_fun (· 0) at h₁
  apply_fun (· 0) at h₂
  rw [constant_on_cycleCovering' A _ _ (by simp) _ ht₁ 0] at h₁
  rw [constant_on_cycleCovering' A _ _ (by simp) _ ht₂ 0] at h₂
  have : 3 = 4 := by
    dsimp at h₁ h₂
    rw [←h₁, ←h₂]
    exact congrFun (A.outputAt_eq (.loopOther Unit) _ _) _
  simp at this

end Cycle

section topology

lemma card_le_card_of_inj {α β : Type*} {s : Finset α} {t : Finset β}
    (i : ∀ a ∈ s, β) (hi : ∀ a ha, i a ha ∈ t)
    (i_inj : ∀ a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂) :
    s.card ≤ t.card :=
  Finset.card_attach ▸ Finset.card_le_card_of_injOn (fun x => i x.1 x.2) (fun _ _ => hi _ _)
    (fun x _ y _ h => Subtype.ext <| i_inj _ x.2 _ y.2 h)

variable {N : PortNumbered V} {N' : PortNumbered V'} {f : V → I} {f' : V' → I}

private theorem preimage_card_le [Fintype V] [DecidableEq V']
    {N : NonSimplePortNumbered V} (φ : CoveringMap N N' f f')
    {v' w' : V'} (h : N'.Adj v' w') :
    (Finset.univ.filter (φ · = v')).card ≤ (Finset.univ.filter (φ · = w')).card := by
  let i := N'.toPort v' w' h
  let g : (v : V) → φ v = v' → V := fun v hv => N.ofPort v (Fin.cast (by simp [←hv]) i)
  have : ∀ v (hv : φ v = v'), φ (g v hv) = w' := by
    rintro v rfl
    simp [φ.map_ofPort, i]
  refine card_le_card_of_inj (fun v hv => g v (by simpa using hv)) (by simpa using this) ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro v₁ hv₁ v₂ hv₂ h'
  dsimp [g] at h'
  have h₁ : (N.reversePort v₁ (Fin.cast (by simp [←hv₁]) i) : ℕ) = N'.reversePort v' i := by
    rw [φ.coe_map_reversePort, Fin.cast_trans, N'.coe_reversePort_cast _ _ hv₁.symm]
  have h₂ : (N.reversePort v₂ (Fin.cast (by simp [←hv₂]) i) : ℕ) = N'.reversePort v' i := by
    rw [φ.coe_map_reversePort, Fin.cast_trans, N'.coe_reversePort_cast _ _ hv₂.symm]
  exact NonSimplePortNumbered.reversePort_inj _ _ _ _ h' (h₁.trans h₂.symm)

private theorem preimage_card_eq_adj [Fintype V] [DecidableEq V']
    {N : NonSimplePortNumbered V} {N' : PortNumbered V'} (φ : CoveringMap N N' f f')
    {v' w' : V'} (h : N'.Adj v' w') :
    (Finset.univ.filter (φ · = v')).card = (Finset.univ.filter (φ · = w')).card :=
  le_antisymm (preimage_card_le φ h) (preimage_card_le _ h.symm)

/-- If `w'` is reachable from `v'`, then they have the same preimage cardinality under `φ`. -/
theorem preimage_card_eq_reachable [Fintype V] [DecidableEq V']
    {N : NonSimplePortNumbered V} {N' : PortNumbered V'} (φ : CoveringMap N N' f f')
    {v' w' : V'} (h : N'.Reachable v' w') :
    (Finset.univ.filter (φ · = v')).card = (Finset.univ.filter (φ · = w')).card :=
  Relation.reflTransGen_of_transitive_reflexive
    (r := fun v' w' => (Finset.univ.filter (φ · = v')).card = (Finset.univ.filter (φ · = w')).card)
    (fun _ => rfl) (fun _ _ _ h₁ h₂ => Eq.trans h₁ h₂)
    (fun _ _ h' => preimage_card_eq_adj φ h') ((N'.reachable_iff_reflTransGen _ _).1 h)

/--
Compute the degree of a covering map. Note that this doesn't assume connectivity, but is only
well-behaved if N' is connected.
You probably don't want to use this to state or prove anything, only to compute.
-/
def CoveringMap.degree' [Fintype V] [Inhabited V'] [DecidableEq V'] (φ : CoveringMap N N' f f') :
    ℕ := (Finset.univ.filter (φ · = default)).card

open scoped Classical in
/--
Get the degree of a covering map. Note that this doesn't assume connectivity, but is only
well-behaved if N' is connected.
-/
noncomputable def CoveringMap.degree [Fintype V] (φ : CoveringMap N N' f f') : ℕ :=
  if h : Nonempty V' then let _ : Inhabited V' := ⟨h.some⟩; CoveringMap.degree' φ else 0

/--
If we have a covering map `φ : N → N'` and `N'` is connected, then the preimage of any vertex
`v' : V'` is constant equal to the degree.
-/
theorem CoveringMap.preimage_eq_degree [Fintype V] [DecidableEq V']
    {φ : CoveringMap N N' f f'} (h : N'.Preconnected) (v : V') :
    (Finset.univ.filter (φ · = v)).card = φ.degree := by
  classical
  have h' : Nonempty V' := ⟨v⟩
  rw [CoveringMap.degree, dif_pos h']
  change Finset.card _ = Finset.card _
  convert preimage_card_eq_reachable φ (h _ _)

lemma degree'_eq_degree [Fintype V] [Inhabited V'] [DecidableEq V'] {φ : CoveringMap N N' f f'}
    (h : N'.Preconnected) : φ.degree' = φ.degree :=
  CoveringMap.preimage_eq_degree h _

theorem CoveringMap.card_eq_card_mul_degree [Fintype V] [Fintype V']
    {φ : CoveringMap N N' f f'} (h : N'.Preconnected) :
    Fintype.card V' * φ.degree = Fintype.card V := by
  classical
  have := Finset.card_eq_sum_card_fiberwise (f := φ) (s := Finset.univ) (t := Finset.univ) (by simp)
  simpa [φ.preimage_eq_degree h] using this.symm

theorem CoveringMap.card_dvd [Fintype V] [Fintype V']
    {φ : CoveringMap N N' f f'} (h : N'.Preconnected) :
    Fintype.card V' ∣ Fintype.card V :=
  ⟨φ.degree, φ.card_eq_card_mul_degree h |>.symm⟩

end topology
