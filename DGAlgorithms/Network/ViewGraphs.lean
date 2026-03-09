import Mathlib


namespace SimpleGraph

/--
A view subgraph `ViewSubgraph` denotes a variant of `Subgraph` that corresponds to
the partial "view" of a node, that is the edges and vertices it "sees" at some stage
of the execution of a distributed algorithm. While it is similar to a `Simplegraph.Subgraph`,
we allow edges to be considered seen when only one of its incident vertices has been seen.
-/
@[ext, grind]
structure ViewSubgraph {V} (G : SimpleGraph V) where
  /-- The set of vertices that are included -/
  verts : Set V
  /-- The edge relation known in this view -/
  Adj : V → V → Prop
  /-- Every seen edge exists in the underlying graph G -/
  adj_sub : Adj v w → G.Adj v w
  /-- If an edge is seen, then it was observed by a node which is known to us,
  thus for each known edge, at least one of its vertices is known in the view -/
  edge_verts : ∀ {v w}, Adj v w → v ∈ verts ∨ w ∈ verts
  symm : Symmetric Adj := by aesop_graph

initialize_simps_projections SimpleGraph.ViewSubgraph (Adj → adj)

/-- The one-vertex subgraph. -/
@[simps]
protected def singletonViewSubgraph (G : SimpleGraph V) (v : V) : G.ViewSubgraph where
  verts := {v}
  Adj := ⊥
  adj_sub := False.elim
  edge_verts {x y} := by
    simp

/-- The one-edge subgraph. -/
@[simps]
def viewSubgraphOfAdj (G : SimpleGraph V) {v w : V} (hvw : G.Adj v w) : G.ViewSubgraph where
  verts := {v, w}
  Adj a b := s(v, w) = s(a, b)
  adj_sub h := by
    rw [← G.mem_edgeSet, ← h]
    exact hvw
  edge_verts {a b} h := by
    apply_fun fun e ↦ a ∈ e at h
    simp only [Sym2.mem_iff, true_or, eq_iff_iff, iff_true] at h
    simp [h]

namespace ViewSubgraph

variable {G : SimpleGraph V} {G₁ G₂ : G.ViewSubgraph} {a b : V}

protected theorem loopless (G' : ViewSubgraph G) : Std.Irrefl G'.Adj :=
  ⟨fun v h ↦ G.loopless.irrefl v (G'.adj_sub h)⟩

theorem adj_comm (G' : ViewSubgraph G) (v w : V) : G'.Adj v w ↔ G'.Adj w v :=
  ⟨fun x ↦ G'.symm x, fun x ↦ G'.symm x⟩

@[symm]
theorem adj_symm (G' : ViewSubgraph G) {u v : V} (h : G'.Adj u v) : G'.Adj v u :=
  G'.symm h

protected theorem Adj.symm {G' : G.ViewSubgraph} {u v : V} (h : G'.Adj u v) : G'.Adj v u :=
  G'.symm h

protected theorem Adj.adj_sub {H : G.ViewSubgraph} {u v : V} (h : H.Adj u v) : G.Adj u v :=
  H.adj_sub h

protected theorem Adj.fst_or_snd_mem {H : G.ViewSubgraph} {u v : V} (h : H.Adj u v) : u ∈ H.verts ∨ v ∈ H.verts :=
  H.edge_verts h

protected theorem Adj.ne {H : G.ViewSubgraph} {u v : V} (h : H.Adj u v) : u ≠ v :=
  h.adj_sub.ne

theorem adj_congr_of_sym2 {H : G.ViewSubgraph} {u v w x : V} (h2 : s(u, v) = s(w, x)) :
    H.Adj u v ↔ H.Adj w x := by
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h2
  rcases h2 with hl | hr
  · rw [hl.1, hl.2]
  · rw [hr.1, hr.2, ViewSubgraph.adj_comm]

/-- Coercion from `G' : ViewSubgraph G` to a `SimpleGraph G'.verts`. -/
@[simps]
protected def coe (G' : ViewSubgraph G) : SimpleGraph G'.verts where
  Adj v w := G'.Adj v w
  symm _ _ h := G'.symm h
  loopless := ⟨fun v h ↦ loopless G |>.irrefl v (G'.adj_sub h)⟩

@[simp]
theorem Adj.adj_sub' (G' : ViewSubgraph G) (u v : G'.verts) (h : G'.Adj u v) : G.Adj u v :=
  G'.adj_sub h

theorem coe_adj_sub (G' : ViewSubgraph G) (u v : G'.verts) (h : G'.coe.Adj u v) : G.Adj u v :=
  G'.adj_sub h

-- Given `h : H.Adj u v`, then `h.coe : H.coe.Adj ⟨u, _⟩ ⟨v, _⟩`.
protected theorem Adj.coe {H : G.ViewSubgraph} {u v : V} (h : H.Adj u v)
    (hu : u ∈ H.verts) (hv : v ∈ H.verts) : H.coe.Adj ⟨u, hu⟩ ⟨v, hv⟩ := h

instance (G : SimpleGraph V) (H : ViewSubgraph G) [DecidableRel H.Adj] : DecidableRel H.coe.Adj :=
  fun a b ↦ ‹DecidableRel H.Adj› _ _

/-- A subgraph is called a *spanning subgraph* if it contains all the vertices of `G`. -/
def IsSpanning (G' : ViewSubgraph G) : Prop :=
  ∀ v : V, v ∈ G'.verts

theorem isSpanning_iff {G' : ViewSubgraph G} : G'.IsSpanning ↔ G'.verts = Set.univ :=
  Set.eq_univ_iff_forall.symm

theorem IsSpanning.verts_eq_univ {G' : ViewSubgraph G} (h : G'.IsSpanning) :
    G'.verts = Set.univ :=
  isSpanning_iff.mp h

/-- Coercion from `Subgraph G` to `SimpleGraph V`.  If `G'` is a spanning
subgraph, then `G'.spanningCoe` yields an isomorphic graph.
In general, this adds in all vertices from `V` as isolated vertices. -/
@[simps]
protected def spanningCoe (G' : ViewSubgraph G) : SimpleGraph V where
  Adj := G'.Adj
  symm := G'.symm
  loopless := ⟨fun v hv ↦ G.loopless.irrefl v (G'.adj_sub hv)⟩

@[simp]
lemma spanningCoe_coe (G' : G.ViewSubgraph) : G'.coe.spanningCoe ≤ G'.spanningCoe := by
  intro v w hvw
  rcases hvw with ⟨u, u', hadj, rfl, rfl⟩
  exact hadj

theorem Adj.of_spanningCoe {G' : ViewSubgraph G} {u v : G'.verts} (h : G'.spanningCoe.Adj u v) :
    G.Adj u v :=
  G'.adj_sub h

lemma spanningCoe_le (G' : G.ViewSubgraph) : G'.spanningCoe ≤ G := fun _ _ ↦ G'.3

theorem spanningCoe_inj : G₁.spanningCoe = G₂.spanningCoe ↔ G₁.Adj = G₂.Adj := by
  constructor
  · intro h
    exact congrArg SimpleGraph.Adj h
  · intro h
    ext v w
    simp [ViewSubgraph.spanningCoe, h]

lemma mem_of_adj_spanningCoe {v w : V} {s : Set V} (G : SimpleGraph s)
    (hadj : G.spanningCoe.Adj v w) : v ∈ s := by aesop

@[simp]
lemma spanningCoe_subgraphOfAdj {v w : V} (hadj : G.Adj v w) :
    (G.subgraphOfAdj hadj).spanningCoe = fromEdgeSet {s(v, w)} := by
  ext v w
  aesop

/-- `spanningCoe` is equivalent to `coe` for a subgraph that `IsSpanning`. -/
@[simps]
def spanningCoeEquivCoeOfSpanning (G' : ViewSubgraph G) (h : G'.IsSpanning) :
    G'.spanningCoe ≃g G'.coe where
  toFun v := ⟨v, h v⟩
  invFun v := v
  map_rel_iff' := Iff.rfl

/-- A subgraph is called an *induced subgraph* if vertices of `G'` are adjacent if
they are adjacent in `G`. -/
def IsInduced (G' : ViewSubgraph G) : Prop :=
  ∀ ⦃v⦄, v ∈ G'.verts → ∀ ⦃w⦄, w ∈ G'.verts → G.Adj v w → G'.Adj v w

@[simp] protected lemma IsInduced.adj {G' : G.ViewSubgraph} (hG' : G'.IsInduced) {a b : G'.verts} :
    G'.Adj a b ↔ G.Adj a b :=
  ⟨coe_adj_sub _ _ _, hG' a.2 b.2⟩

/-- `H.support` is the set of vertices that form edges in the subgraph `H`. -/
def support (H : ViewSubgraph G) : Set V := SetRel.dom {(v, w) | H.Adj v w}

theorem mem_support (H : ViewSubgraph G) {v : V} : v ∈ H.support ↔ ∃ w, H.Adj v w := Iff.rfl

theorem support_subset_verts (H : ViewSubgraph G) :
    H.support ⊆ H.verts ∪ {v : V | ∃ w, H.Adj w v ∧ w ∈ H.verts} :=
  fun v hv ↦ by
    rcases hv with ⟨w, hvw⟩
    rcases H.edge_verts hvw with hv' | hw'
    · exact Or.inl hv'
    · exact Or.inr ⟨w, H.adj_symm hvw, hw'⟩

/-- `G'.neighborSet v` is the set of vertices adjacent to `v` in `G'`. -/
def neighborSet (G' : ViewSubgraph G) (v : V) : Set V := {w | G'.Adj v w}

theorem neighborSet_subset (G' : ViewSubgraph G) (v : V) : G'.neighborSet v ⊆ G.neighborSet v :=
  fun _ ↦ G'.adj_sub

theorem neighborSet_subset_verts (G' : ViewSubgraph G) {v : V} (hv : v ∉ G'.verts) :
    G'.neighborSet v ⊆ G'.verts :=
  fun _ h ↦ (G'.edge_verts h).resolve_left hv

@[simp]
theorem mem_neighborSet (G' : ViewSubgraph G) (v w : V) : w ∈ G'.neighborSet v ↔ G'.Adj v w := Iff.rfl

/-- A subgraph as a graph has equivalent neighbor sets. -/
def coeNeighborSetEquiv {G' : ViewSubgraph G} (v : G'.verts) :
    G'.coe.neighborSet v ≃ {w : V // w ∈ G'.neighborSet v ∧ w ∈ G'.verts} where
  toFun w := ⟨w, w.2, w.1.2⟩
  invFun w := ⟨⟨w, w.2.2⟩, w.2.1⟩
  left_inv w := by cases w; rfl
  right_inv w := by cases w; rfl

/-- The edge set of `G'` consists of a subset of edges of `G`. -/
def edgeSet (G' : ViewSubgraph G) : Set (Sym2 V) := Sym2.fromRel G'.symm

theorem edgeSet_subset (G' : ViewSubgraph G) : G'.edgeSet ⊆ G.edgeSet :=
  Sym2.ind (fun _ _ ↦ G'.adj_sub)

@[simp]
protected lemma mem_edgeSet {G' : ViewSubgraph G} {v w : V} : s(v, w) ∈ G'.edgeSet ↔ G'.Adj v w := .rfl

@[simp] lemma edgeSet_coe {G' : G.ViewSubgraph} : G'.coe.edgeSet = Sym2.map (↑) ⁻¹' G'.edgeSet := by
  ext e; induction e using Sym2.ind; simp

lemma image_coe_edgeSet_coe (G' : G.ViewSubgraph) : Sym2.map (↑) '' G'.coe.edgeSet ⊆ G'.edgeSet := by
  rintro _ ⟨e, he, rfl⟩
  simpa [edgeSet_coe] using he

theorem mem_verts_of_mem_edge {G' : ViewSubgraph G} {e : Sym2 V} (he : e ∈ G'.edgeSet) :
    ∃ v ∈ e, v ∈ G'.verts := by
  induction e using Sym2.ind with
  | h v w =>
      rcases G'.edge_verts he with hv | hw
      · exact ⟨v, by simp, hv⟩
      · exact ⟨w, by simp, hw⟩

/-- The `incidenceSet` is the set of edges incident to a given vertex. -/
def incidenceSet (G' : ViewSubgraph G) (v : V) : Set (Sym2 V) := {e ∈ G'.edgeSet | v ∈ e}

theorem incidenceSet_subset_incidenceSet (G' : ViewSubgraph G) (v : V) :
    G'.incidenceSet v ⊆ G.incidenceSet v :=
  fun _ h ↦ ⟨G'.edgeSet_subset h.1, h.2⟩

theorem incidenceSet_subset (G' : ViewSubgraph G) (v : V) : G'.incidenceSet v ⊆ G'.edgeSet :=
  fun _ h ↦ h.1

/-- Give a vertex as an element of the subgraph's vertex type. -/
abbrev vert (G' : ViewSubgraph G) (v : V) (h : v ∈ G'.verts) : G'.verts := ⟨v, h⟩

/--
Create an equal copy of a subgraph (see `copy_eq`) with possibly different definitional equalities.
See Note [range copy pattern].
-/
def copy (G' : ViewSubgraph G) (V'' : Set V) (hV : V'' = G'.verts)
    (adj' : V → V → Prop) (hadj : adj' = G'.Adj) : ViewSubgraph G where
  verts := V''
  Adj := adj'
  adj_sub := hadj.symm ▸ G'.adj_sub
  edge_verts := hV.symm ▸ hadj.symm ▸ G'.edge_verts
  symm := hadj.symm ▸ G'.symm

theorem copy_eq (G' : ViewSubgraph G) (V'' : Set V) (hV : V'' = G'.verts)
    (adj' : V → V → Prop) (hadj : adj' = G'.Adj) : G'.copy V'' hV adj' hadj = G' :=
  ViewSubgraph.ext hV hadj

/-- The union of two subgraphs. -/
instance : Max G.ViewSubgraph where
  max G₁ G₂ :=
    { verts := G₁.verts ∪ G₂.verts
      Adj := G₁.Adj ⊔ G₂.Adj
      adj_sub := fun hab => Or.elim hab (fun h => G₁.adj_sub h) fun h => G₂.adj_sub h
      edge_verts := by
        intro v w hvw
        rcases hvw with hvw | hvw
        · rcases G₁.edge_verts hvw with hv | hw
          · exact Or.inl <| Or.inl hv
          · exact Or.inr <| Or.inl hw
        · rcases G₂.edge_verts hvw with hv | hw
          · exact Or.inl <| Or.inr hv
          · exact Or.inr <| Or.inr hw
      symm := fun _ _ => Or.imp G₁.adj_symm G₂.adj_symm }

/-- The intersection of two subgraphs. -/
instance : Min G.ViewSubgraph where
  min G₁ G₂ :=
    { verts := G₁.verts ∩ G₂.verts
      Adj := fun v w => G₁.Adj v w ∧ G₂.Adj v w ∧ (v ∈ G₁.verts ∩ G₂.verts ∨ w ∈ G₁.verts ∩ G₂.verts)
      adj_sub := fun hab => G₁.adj_sub hab.1
      edge_verts := fun hab => hab.2.2
      symm := by
        intro v w hab
        exact ⟨G₁.adj_symm hab.1, G₂.adj_symm hab.2.1, hab.2.2.symm⟩ }

/-- The `top` subgraph is `G` as a subgraph of itself. -/
instance : Top G.ViewSubgraph where
  top :=
    { verts := Set.univ
      Adj := G.Adj
      adj_sub := id
      edge_verts := @fun v _ _ => Or.inl (Set.mem_univ v)
      symm := G.symm }

/-- The `bot` subgraph is the subgraph with no vertices or edges. -/
instance : Bot G.ViewSubgraph where
  bot :=
    { verts := ∅
      Adj := ⊥
      adj_sub := False.elim
      edge_verts := False.elim
      symm := fun _ _ => id }

instance : SupSet G.ViewSubgraph where
  sSup s :=
    { verts := ⋃ G' ∈ s, verts G'
      Adj := fun a b => ∃ G' ∈ s, Adj G' a b
      adj_sub := by
        rintro a b ⟨G', -, hab⟩
        exact G'.adj_sub hab
      edge_verts := by
        rintro a b ⟨G', hG', hab⟩
        rcases G'.edge_verts hab with ha | hb
        · exact Or.inl <| Set.mem_iUnion₂_of_mem hG' ha
        · exact Or.inr <| Set.mem_iUnion₂_of_mem hG' hb
      symm := fun a b h => by simpa [adj_comm] using h }

instance : InfSet G.ViewSubgraph where
  sInf s :=
    { verts := ⋂ G' ∈ s, verts G'
      Adj := fun a b =>
        (∀ ⦃G'⦄, G' ∈ s → Adj G' a b) ∧ G.Adj a b ∧
          (a ∈ ⋂ G' ∈ s, verts G' ∨ b ∈ ⋂ G' ∈ s, verts G')
      adj_sub := fun hab => hab.2.1
      edge_verts := fun hab => hab.2.2
      symm := by
        intro a b hab
        refine ⟨?_, G.adj_symm hab.2.1, hab.2.2.symm⟩
        intro G' hG'
        exact (hab.1 hG').symm }

@[simp]
theorem sup_adj : (G₁ ⊔ G₂).Adj a b ↔ G₁.Adj a b ∨ G₂.Adj a b :=
  Iff.rfl

@[simp]
theorem inf_adj (G₁ G₂ : G.ViewSubgraph) :
    (G₁ ⊓ G₂).Adj a b ↔
      G₁.Adj a b ∧ G₂.Adj a b ∧ (a ∈ G₁.verts ∩ G₂.verts ∨ b ∈ G₁.verts ∩ G₂.verts) :=
  Iff.rfl

@[simp]
theorem top_adj : (⊤ : ViewSubgraph G).Adj a b ↔ G.Adj a b :=
  Iff.rfl

@[simp]
theorem not_bot_adj : ¬ (⊥ : ViewSubgraph G).Adj a b :=
  not_false

@[simp]
theorem verts_sup (G₁ G₂ : G.ViewSubgraph) : (G₁ ⊔ G₂).verts = G₁.verts ∪ G₂.verts :=
  rfl

@[simp]
theorem verts_inf (G₁ G₂ : G.ViewSubgraph) : (G₁ ⊓ G₂).verts = G₁.verts ∩ G₂.verts :=
  rfl

@[simp]
theorem verts_top : (⊤ : G.ViewSubgraph).verts = Set.univ :=
  rfl

@[simp]
theorem verts_bot : (⊥ : G.ViewSubgraph).verts = ∅ :=
  rfl

theorem eq_bot_iff_verts_eq_empty (G' : G.ViewSubgraph) : G' = ⊥ ↔ G'.verts = ∅ :=
  ⟨(· ▸ verts_bot), by
    intro h
    refine ViewSubgraph.ext (h.trans verts_bot.symm) ?_
    funext v w
    refine propext ⟨?_, False.elim⟩
    intro hvw
    rcases G'.edge_verts hvw with hv | hw
    · exact (h ▸ hv).elim
    · exact (h ▸ hw).elim⟩

theorem ne_bot_iff_nonempty_verts (G' : G.ViewSubgraph) : G' ≠ ⊥ ↔ G'.verts.Nonempty :=
  G'.eq_bot_iff_verts_eq_empty.not.trans <| Set.nonempty_iff_ne_empty.symm

@[simp]
theorem sSup_adj {s : Set G.ViewSubgraph} : (sSup s).Adj a b ↔ ∃ G ∈ s, Adj G a b :=
  Iff.rfl

@[simp]
theorem sInf_adj {s : Set G.ViewSubgraph} :
    (sInf s).Adj a b ↔
      (∀ G' ∈ s, Adj G' a b) ∧ G.Adj a b ∧ (a ∈ ⋂ G' ∈ s, verts G' ∨ b ∈ ⋂ G' ∈ s, verts G') :=
  Iff.rfl

@[simp]
theorem iSup_adj {f : ι → G.ViewSubgraph} : (⨆ i, f i).Adj a b ↔ ∃ i, (f i).Adj a b := by
  simp [iSup]

@[simp]
theorem iInf_adj {f : ι → G.ViewSubgraph} :
    (⨅ i, f i).Adj a b ↔
      (∀ i, (f i).Adj a b) ∧ G.Adj a b ∧ (a ∈ ⋂ i, (f i).verts ∨ b ∈ ⋂ i, (f i).verts) := by
  simp [iInf]

theorem sInf_adj_of_nonempty {s : Set G.ViewSubgraph} (hs : s.Nonempty) :
    (sInf s).Adj a b ↔
      (∀ G' ∈ s, Adj G' a b) ∧ (a ∈ ⋂ G' ∈ s, verts G' ∨ b ∈ ⋂ G' ∈ s, verts G') := by
  constructor
  · intro h
    exact ⟨h.1, h.2.2⟩
  · intro h
    obtain ⟨G', hG'⟩ := hs
    exact ⟨h.1, G'.adj_sub (h.1 _ hG'), h.2⟩

theorem iInf_adj_of_nonempty [Nonempty ι] {f : ι → G.ViewSubgraph} :
    (⨅ i, f i).Adj a b ↔
      (∀ i, (f i).Adj a b) ∧ (a ∈ ⋂ i, (f i).verts ∨ b ∈ ⋂ i, (f i).verts) := by
  rw [iInf, sInf_adj_of_nonempty (Set.range_nonempty _)]
  simp

@[simp]
theorem verts_sSup (s : Set G.ViewSubgraph) : (sSup s).verts = ⋃ G' ∈ s, verts G' :=
  rfl

@[simp]
theorem verts_sInf (s : Set G.ViewSubgraph) : (sInf s).verts = ⋂ G' ∈ s, verts G' :=
  rfl

@[simp]
theorem verts_iSup {f : ι → G.ViewSubgraph} : (⨆ i, f i).verts = ⋃ i, (f i).verts := by simp [iSup]

@[simp]
theorem verts_iInf {f : ι → G.ViewSubgraph} : (⨅ i, f i).verts = ⋂ i, (f i).verts := by simp [iInf]

@[simp] lemma coe_bot : (⊥ : G.ViewSubgraph).coe = ⊥ := rfl

@[simp] lemma IsInduced.top : (⊤ : G.ViewSubgraph).IsInduced := fun _ _ _ _ ↦ id

/-- The graph isomorphism between the top element of `G.subgraph` and `G`. -/
def topIso : (⊤ : G.ViewSubgraph).coe ≃g G where
  toFun := (↑)
  invFun a := ⟨a, Set.mem_univ _⟩
  left_inv _ := Subtype.eta ..
  map_rel_iff' := .rfl

theorem verts_spanningCoe_injective :
    (fun G' : ViewSubgraph G => (G'.verts, G'.Adj)).Injective := by
  intro G₁ G₂ h
  rw [Prod.ext_iff] at h
  exact ViewSubgraph.ext h.1 h.2

/-- For subgraphs `G₁`, `G₂`, `G₁ ≤ G₂` iff `G₁.verts ⊆ G₂.verts` and
`∀ a b, G₁.adj a b → G₂.adj a b`. -/
instance : PartialOrder G.ViewSubgraph where
  le x y := x.verts ⊆ y.verts ∧ ∀ ⦃v w : V⦄, x.Adj v w → y.Adj v w
  le_refl x := ⟨Set.Subset.rfl, fun _ _ h => h⟩
  le_trans x y z hxy hyz := ⟨Set.Subset.trans hxy.1 hyz.1, fun _ _ h => hyz.2 (hxy.2 h)⟩
  le_antisymm x y hxy hyx := by
    apply ViewSubgraph.ext (Set.Subset.antisymm hxy.1 hyx.1)
    funext v w
    exact propext ⟨fun h => hxy.2 h, fun h => hyx.2 h⟩

instance : BoundedOrder G.ViewSubgraph where
  le_top x := ⟨Set.subset_univ _, fun _ _ h => x.adj_sub h⟩
  bot_le _ := ⟨Set.empty_subset _, fun _ _ => False.elim⟩

@[gcongr] lemma verts_mono {H H' : G.ViewSubgraph} (h : H ≤ H') : H.verts ⊆ H'.verts := h.1
lemma verts_monotone : Monotone (verts : G.ViewSubgraph → Set V) := fun _ _ h ↦ h.1

@[simps]
instance subgraphInhabited : Inhabited (ViewSubgraph G) := ⟨⊥⟩

@[simp]
theorem neighborSet_sup {H H' : G.ViewSubgraph} (v : V) :
    (H ⊔ H').neighborSet v = H.neighborSet v ∪ H'.neighborSet v := rfl

@[simp]
theorem neighborSet_inf {H H' : G.ViewSubgraph} (v : V) :
    (H ⊓ H').neighborSet v ⊆ H.neighborSet v ∩ H'.neighborSet v :=
  fun _ h ↦ ⟨h.1, h.2.1⟩

@[simp]
theorem neighborSet_top (v : V) : (⊤ : G.ViewSubgraph).neighborSet v = G.neighborSet v := rfl

@[simp]
theorem neighborSet_bot (v : V) : (⊥ : G.ViewSubgraph).neighborSet v = ∅ := rfl

@[simp]
theorem neighborSet_sSup (s : Set G.ViewSubgraph) (v : V) :
    (sSup s).neighborSet v = ⋃ G' ∈ s, neighborSet G' v := by
  ext
  simp

@[simp]
theorem neighborSet_sInf (s : Set G.ViewSubgraph) (v : V) :
    (sInf s).neighborSet v ⊆ (⋂ G' ∈ s, neighborSet G' v) ∩ G.neighborSet v :=
  fun w h ↦ by
    refine ⟨Set.mem_iInter₂.2 (fun G' hG' => h.1 hG'), h.2.1⟩

@[simp]
theorem neighborSet_iSup (f : ι → G.ViewSubgraph) (v : V) :
    (⨆ i, f i).neighborSet v = ⋃ i, (f i).neighborSet v := by simp [iSup]

@[simp]
theorem neighborSet_iInf (f : ι → G.ViewSubgraph) (v : V) :
    (⨅ i, f i).neighborSet v ⊆ (⋂ i, (f i).neighborSet v) ∩ G.neighborSet v := by
  intro w hw
  simpa [iInf] using (neighborSet_sInf (G := G) (s := Set.range f) (v := v) hw)

@[simp]
theorem edgeSet_top : (⊤ : ViewSubgraph G).edgeSet = G.edgeSet := rfl

@[simp]
theorem edgeSet_bot : (⊥ : ViewSubgraph G).edgeSet = ∅ :=
  Set.ext <| Sym2.ind (by simp)

@[simp]
theorem edgeSet_inf {H₁ H₂ : ViewSubgraph G} : (H₁ ⊓ H₂).edgeSet ⊆ H₁.edgeSet ∩ H₂.edgeSet := by
  intro e he
  induction e using Sym2.ind with
  | h v w =>
      exact ⟨he.1, he.2.1⟩

@[simp]
theorem edgeSet_sup {H₁ H₂ : ViewSubgraph G} : (H₁ ⊔ H₂).edgeSet = H₁.edgeSet ∪ H₂.edgeSet :=
  Set.ext <| Sym2.ind (by simp)

@[simp]
theorem edgeSet_sSup (s : Set G.ViewSubgraph) : (sSup s).edgeSet = ⋃ G' ∈ s, edgeSet G' := by
  ext e
  induction e
  simp

@[simp]
theorem edgeSet_sInf (s : Set G.ViewSubgraph) :
    (sInf s).edgeSet ⊆ (⋂ G' ∈ s, edgeSet G') ∩ G.edgeSet := by
  intro e he
  induction e using Sym2.ind with
  | h v w =>
      exact ⟨Set.mem_iInter₂.2 (fun G' hG' => he.1 hG'), he.2.1⟩

@[simp]
theorem edgeSet_iSup (f : ι → G.ViewSubgraph) :
    (⨆ i, f i).edgeSet = ⋃ i, (f i).edgeSet := by simp [iSup]

@[simp]
theorem edgeSet_iInf (f : ι → G.ViewSubgraph) :
    (⨅ i, f i).edgeSet ⊆ (⋂ i, (f i).edgeSet) ∩ G.edgeSet := by
  intro e he
  simpa [iInf] using (edgeSet_sInf (G := G) (s := Set.range f) he)

@[simp]
theorem spanningCoe_top : (⊤ : ViewSubgraph G).spanningCoe = G := rfl

@[simp]
theorem spanningCoe_bot : (⊥ : ViewSubgraph G).spanningCoe = ⊥ := rfl

/-- Turn a subgraph of a `SimpleGraph` into a member of its equivalent `ViewSubgraph` type. -/
@[simps]
def toViewSubgraph (H : SimpleGraph V) (h : H ≤ G) : G.ViewSubgraph where
  verts := Set.univ
  Adj := H.Adj
  adj_sub e := h e
  edge_verts _ := Or.inl (Set.mem_univ _)
  symm := H.symm

theorem support_mono {H H' : ViewSubgraph G} (h : H ≤ H') : H.support ⊆ H'.support :=
  SetRel.dom_mono fun _ hvw ↦ h.2 hvw

theorem toViewSubgraph.isSpanning (H : SimpleGraph V) (h : H ≤ G) :
    (toViewSubgraph H h).IsSpanning :=
  Set.mem_univ

theorem spanningCoe_le_of_le {H H' : ViewSubgraph G} (h : H ≤ H') : H.spanningCoe ≤ H'.spanningCoe :=
  h.2

@[simp]
lemma sup_spanningCoe (H H' : ViewSubgraph G) :
    (H ⊔ H').spanningCoe = H.spanningCoe ⊔ H'.spanningCoe := rfl

/-- The bottom of the `Subgraph G` lattice is isomorphic to the empty graph on the empty
vertex type. -/
def botIso : (⊥ : ViewSubgraph G).coe ≃g emptyGraph Empty where
  toFun v := v.property.elim
  invFun v := v.elim
  left_inv := fun ⟨_, h⟩ ↦ h.elim
  right_inv v := v.elim
  map_rel_iff' := Iff.rfl

theorem edgeSet_mono {H₁ H₂ : ViewSubgraph G} (h : H₁ ≤ H₂) : H₁.edgeSet ≤ H₂.edgeSet :=
  Sym2.ind h.2

theorem edgeSet_disjoint_of_adj {H₁ H₂ : ViewSubgraph G}
    (h : ∀ ⦃u v⦄, H₁.Adj u v → ¬ H₂.Adj u v) : Disjoint H₁.edgeSet H₂.edgeSet := by
  refine Set.disjoint_left.2 ?_
  intro e he₁ he₂
  induction e using Sym2.ind with
  | h u v =>
      exact h he₁ he₂

section map

variable {W : Type*} {G' : SimpleGraph W} {f : G →g G'}

/-- Graph homomorphisms induce a covariant function on view subgraphs. -/
@[simps]
protected def map (f : G →g G') (H : G.ViewSubgraph) : G'.ViewSubgraph where
  verts := f '' H.verts
  Adj := Relation.Map H.Adj f f
  adj_sub := by
    rintro _ _ ⟨u, v, h, rfl, rfl⟩
    exact f.map_rel (H.adj_sub h)
  edge_verts := by
    rintro _ _ ⟨u, v, h, rfl, rfl⟩
    rcases H.edge_verts h with hu | hv
    · exact Or.inl (Set.mem_image_of_mem _ hu)
    · exact Or.inr (Set.mem_image_of_mem _ hv)
  symm := by
    rintro _ _ ⟨u, v, h, rfl, rfl⟩
    exact ⟨v, u, H.symm h, rfl, rfl⟩

@[simp] lemma map_id (H : G.ViewSubgraph) : H.map Hom.id = H := by
  ext <;> simp [ViewSubgraph.map]

lemma map_comp {U : Type*} {G'' : SimpleGraph U} (H : G.ViewSubgraph) (f : G →g G') (g : G' →g G'') :
    H.map (g.comp f) = (H.map f).map g := by
  ext <;> simp [ViewSubgraph.map]

@[gcongr] lemma map_mono {H₁ H₂ : G.ViewSubgraph} (hH : H₁ ≤ H₂) : H₁.map f ≤ H₂.map f := by
  constructor
  · intro
    simp only [map_verts, Set.mem_image, forall_exists_index, and_imp]
    rintro v hv rfl
    exact ⟨_, hH.1 hv, rfl⟩
  · rintro _ _ ⟨u, v, ha, rfl, rfl⟩
    exact ⟨_, _, hH.2 ha, rfl, rfl⟩

lemma map_monotone : Monotone (ViewSubgraph.map f) := fun _ _ ↦ map_mono

theorem map_sup (f : G →g G') (H₁ H₂ : G.ViewSubgraph) :
    (H₁ ⊔ H₂).map f = H₁.map f ⊔ H₂.map f := by
  ext <;> simp [Set.image_union, map_adj, sup_adj, Relation.Map, or_and_right, exists_or]

@[simp] lemma map_iso_top {H : SimpleGraph W} (e : G ≃g H) : ViewSubgraph.map e.toHom ⊤ = ⊤ := by
  ext <;> simp [Relation.Map, e.apply_eq_iff_eq_symm_apply, ← e.map_rel_iff]

@[simp] lemma edgeSet_map (f : G →g G') (H : G.ViewSubgraph) :
    (H.map f).edgeSet = Sym2.map f '' H.edgeSet := Sym2.fromRel_relationMap ..

/-- Graph homomorphisms induce a contravariant function on view subgraphs. -/
@[simps]
protected def comap {G' : SimpleGraph W} (f : G →g G') (H : G'.ViewSubgraph) : G.ViewSubgraph where
  verts := f ⁻¹' H.verts
  Adj u v := G.Adj u v ∧ H.Adj (f u) (f v)
  adj_sub h := h.1
  edge_verts h := by
    rcases H.edge_verts h.2 with hu | hv
    · exact Or.inl hu
    · exact Or.inr hv
  symm _ _ h := ⟨G.symm h.1, H.symm h.2⟩

theorem comap_monotone {G' : SimpleGraph W} (f : G →g G') : Monotone (ViewSubgraph.comap f) := by
  intro H H' h
  constructor
  · intro
    simp only [comap_verts, Set.mem_preimage]
    apply h.1
  · intro v w
    simp +contextual only [comap_adj, and_imp, true_and]
    intro
    apply h.2

@[simp] lemma comap_equiv_top {H : SimpleGraph W} (f : G →g H) : ViewSubgraph.comap f ⊤ = ⊤ := by
  ext <;> simp +contextual [f.map_adj]

theorem map_le_iff_le_comap {G' : SimpleGraph W} (f : G →g G') (H : G.ViewSubgraph) (H' : G'.ViewSubgraph) :
    H.map f ≤ H' ↔ H ≤ H'.comap f := by
  refine ⟨fun h ↦ ⟨fun v hv ↦ ?_, fun v w hvw ↦ ?_⟩, fun h ↦ ⟨fun v ↦ ?_, fun v w ↦ ?_⟩⟩
  · simp only [comap_verts, Set.mem_preimage]
    exact h.1 ⟨v, hv, rfl⟩
  · simp only [H.adj_sub hvw, comap_adj, true_and]
    exact h.2 ⟨v, w, hvw, rfl, rfl⟩
  · simp only [map_verts, Set.mem_image, forall_exists_index, and_imp]
    rintro w hw rfl
    exact h.1 hw
  · simp only [Relation.Map, map_adj, forall_exists_index, and_imp]
    rintro u u' hu rfl rfl
    exact (h.2 hu).2

instance [DecidableEq V] [Fintype V] [DecidableRel G.Adj] : Fintype G.ViewSubgraph := by
  refine .ofBijective
    (α := {H : Finset V × (V → V → Bool) //
      (∀ a b, H.2 a b → G.Adj a b) ∧
        (∀ a b, H.2 a b → a ∈ H.1 ∨ b ∈ H.1) ∧
          ∀ a b, H.2 a b = H.2 b a})
    (fun H ↦ ⟨H.1.1, fun a b => H.1.2 a b, @H.2.1, @H.2.2.1, by
      intro a b hab
      rw [← H.2.2.2 a b]
      exact hab⟩)
    ⟨?_, fun H => ?_⟩
  · rintro ⟨⟨_, _⟩, -⟩ ⟨⟨_, _⟩, -⟩
    simp [funext_iff]
  · classical
    refine ⟨⟨(H.verts.toFinset, fun a b => H.Adj a b), ?_, ?_, ?_⟩, by simp⟩
    · intro a b
      simpa using H.adj_sub
    · intro a b
      simpa using H.edge_verts
    · intro a b
      simp [H.adj_comm]

instance [Finite V] : Finite G.ViewSubgraph := by
  classical
  cases nonempty_fintype V
  infer_instance

end map

/-- Given two view subgraphs, one a subgraph of the other, there is an induced injective
homomorphism of the view subgraphs as graphs. -/
@[simps]
def inclusion {x y : ViewSubgraph G} (h : x ≤ y) : x.coe →g y.coe where
  toFun v := ⟨↑v, h.1 v.property⟩
  map_rel' hvw := h.2 hvw

theorem inclusion.injective {x y : ViewSubgraph G} (h : x ≤ y) : Function.Injective (inclusion h) := by
  intro v w h'
  rw [inclusion, DFunLike.coe, Subtype.mk_eq_mk] at h'
  exact Subtype.ext h'

/-- There is an induced injective homomorphism of a view subgraph of `G` into `G`. -/
@[simps]
protected def hom (x : ViewSubgraph G) : x.coe →g G where
  toFun v := v
  map_rel' := x.adj_sub

@[simp] lemma coe_hom (x : ViewSubgraph G) :
    (x.hom : x.verts → V) = fun (v : x.verts) => (v : V) := rfl

theorem hom_injective {x : ViewSubgraph G} : Function.Injective x.hom :=
  fun _ _ => Subtype.ext

lemma map_hom_top_le (G' : G.ViewSubgraph) : ViewSubgraph.map G'.hom ⊤ ≤ G' := by
  constructor
  · intro v hv
    rcases hv with ⟨u, hu, rfl⟩
    exact u.2
  · rintro v w ⟨u, u', hu, rfl, rfl⟩
    exact hu

/-- There is an induced injective homomorphism of a view subgraph of `G` as
a spanning subgraph into `G`. -/
@[simps]
def spanningHom (x : ViewSubgraph G) : x.spanningCoe →g G where
  toFun := id
  map_rel' := x.adj_sub

theorem spanningHom_injective {x : ViewSubgraph G} : Function.Injective x.spanningHom :=
  fun _ _ => id

theorem neighborSet_subset_of_subgraph {x y : ViewSubgraph G} (h : x ≤ y) (v : V) :
    x.neighborSet v ⊆ y.neighborSet v :=
  fun _ h' => h.2 h'

instance neighborSet.decidablePred (G' : ViewSubgraph G) [h : DecidableRel G'.Adj] (v : V) :
    DecidablePred (· ∈ G'.neighborSet v) :=
  h v

/-- If a graph is locally finite at a vertex, then so is a view subgraph of that graph. -/
instance finiteAt {G' : ViewSubgraph G} (v : G'.verts) [DecidableRel G'.Adj]
    [Fintype (G.neighborSet v)] : Fintype (G'.neighborSet v) :=
  Set.fintypeSubset (G.neighborSet v) (G'.neighborSet_subset v)

/-- If a view subgraph is locally finite at a vertex, then so are view subgraphs of that subgraph.

This is not an instance because `G''` cannot be inferred. -/
def finiteAtOfSubgraph {G' G'' : ViewSubgraph G} [DecidableRel G'.Adj] (h : G' ≤ G'') (v : G'.verts)
    [Fintype (G''.neighborSet v)] : Fintype (G'.neighborSet v) :=
  Set.fintypeSubset (G''.neighborSet v) (neighborSet_subset_of_subgraph h v)

theorem IsSpanning.card_verts [Fintype V] {G' : ViewSubgraph G} [Fintype G'.verts] (h : G'.IsSpanning) :
    G'.verts.toFinset.card = Fintype.card V := by
  simp only [isSpanning_iff.1 h, Set.toFinset_univ]
  congr

/-- The degree of a vertex in a view subgraph. It's defined when the local neighborhood is finite. -/
def degree (G' : ViewSubgraph G) (v : V) [Fintype (G'.neighborSet v)] : ℕ :=
  Fintype.card (G'.neighborSet v)

theorem finset_card_neighborSet_eq_degree {G' : ViewSubgraph G} {v : V} [Fintype (G'.neighborSet v)] :
    (G'.neighborSet v).toFinset.card = G'.degree v := by
  rw [degree, Set.toFinset_card]

theorem degree_le (G' : ViewSubgraph G) (v : V) [Fintype (G'.neighborSet v)]
    [Fintype (G.neighborSet v)] : G'.degree v ≤ G.degree v := by
  rw [← card_neighborSet_eq_degree]
  exact Set.card_le_card (G'.neighborSet_subset v)

theorem degree_le' (G' G'' : ViewSubgraph G) (h : G' ≤ G'') (v : V) [Fintype (G'.neighborSet v)]
    [Fintype (G''.neighborSet v)] : G'.degree v ≤ G''.degree v :=
  Set.card_le_card (neighborSet_subset_of_subgraph h v)

@[simp]
theorem degree_spanningCoe {G' : G.ViewSubgraph} (v : V) [Fintype (G'.neighborSet v)]
    [Fintype (G'.spanningCoe.neighborSet v)] : G'.spanningCoe.degree v = G'.degree v := by
  rw [← card_neighborSet_eq_degree, ViewSubgraph.degree]
  congr!

theorem degree_pos_iff_exists_adj {G' : ViewSubgraph G} {v : V} [Fintype (G'.neighborSet v)] :
    0 < G'.degree v ↔ ∃ w, G'.Adj v w := by
  simp only [degree, Fintype.card_pos_iff, nonempty_subtype, mem_neighborSet]

theorem degree_eq_one_iff_existsUnique_adj {G' : ViewSubgraph G} {v : V} [Fintype (G'.neighborSet v)] :
    G'.degree v = 1 ↔ ∃! w : V, G'.Adj v w := by
  rw [← finset_card_neighborSet_eq_degree, Finset.card_eq_one, Finset.singleton_iff_unique_mem]
  simp only [Set.mem_toFinset, mem_neighborSet]

lemma neighborSet_eq_of_equiv {v : V} {H : ViewSubgraph G}
    (h : G.neighborSet v ≃ H.neighborSet v) (hfin : (G.neighborSet v).Finite) :
    H.neighborSet v = G.neighborSet v := by
  lift H.neighborSet v to Finset V using h.set_finite_iff.mp hfin with s hs
  lift G.neighborSet v to Finset V using hfin with t ht
  refine congrArg _ <| Finset.eq_of_subset_of_card_le ?_ (Finset.card_eq_of_equiv h).le
  rw [← Finset.coe_subset, hs, ht]
  exact H.neighborSet_subset _

lemma adj_iff_of_neighborSet_equiv {v : V} {H : ViewSubgraph G}
    (h : G.neighborSet v ≃ H.neighborSet v) (hfin : (G.neighborSet v).Finite) :
    ∀ {w}, H.Adj v w ↔ G.Adj v w :=
  Set.ext_iff.mp (neighborSet_eq_of_equiv h hfin) _

section MkProperties

variable {W : Type*} {G' : SimpleGraph W}

instance (v : V) : Unique (G.singletonViewSubgraph v).verts :=
  Set.uniqueSingleton _

@[simp]
theorem singletonViewSubgraph_le_iff (v : V) (H : G.ViewSubgraph) :
    G.singletonViewSubgraph v ≤ H ↔ v ∈ H.verts := by
  refine ⟨fun h => h.1 (Set.mem_singleton v), ?_⟩
  intro h
  constructor
  · rwa [SimpleGraph.singletonViewSubgraph_verts, Set.singleton_subset_iff]
  · exact fun _ _ => False.elim

@[simp]
theorem map_singletonViewSubgraph (f : G →g G') {v : V} :
    ViewSubgraph.map f (G.singletonViewSubgraph v) = G'.singletonViewSubgraph (f v) := by
  ext <;> simp only [Relation.Map, ViewSubgraph.map_adj, singletonViewSubgraph_adj, Pi.bot_apply,
    exists_and_left, and_iff_left_iff_imp, ViewSubgraph.map_verts,
    singletonViewSubgraph_verts, Set.image_singleton]
  exact False.elim

@[simp]
theorem neighborSet_singletonViewSubgraph (v w : V) :
    (G.singletonViewSubgraph v).neighborSet w = ∅ :=
  rfl

@[simp]
theorem edgeSet_singletonViewSubgraph (v : V) : (G.singletonViewSubgraph v).edgeSet = ∅ :=
  Sym2.fromRel_bot

instance nonempty_viewSubgraphOfAdj_verts {v w : V} (hvw : G.Adj v w) :
    Nonempty (G.viewSubgraphOfAdj hvw).verts :=
  ⟨⟨v, by simp [viewSubgraphOfAdj_verts]⟩⟩

@[simp]
theorem edgeSet_viewSubgraphOfAdj {v w : V} (hvw : G.Adj v w) :
    (G.viewSubgraphOfAdj hvw).edgeSet = {s(v, w)} := by
  ext e
  refine e.ind ?_
  simp only [eq_comm, Set.mem_singleton_iff, ViewSubgraph.mem_edgeSet, viewSubgraphOfAdj_adj,
    forall₂_true_iff]

theorem viewSubgraphOfAdj_symm {v w : V} (hvw : G.Adj v w) :
    G.viewSubgraphOfAdj hvw.symm = G.viewSubgraphOfAdj hvw := by
  ext <;> simp [or_comm, and_comm]

@[simp]
theorem map_viewSubgraphOfAdj (f : G →g G') {v w : V} (hvw : G.Adj v w) :
    ViewSubgraph.map f (G.viewSubgraphOfAdj hvw) = G'.viewSubgraphOfAdj (f.map_adj hvw) := by
  ext <;> grind [ViewSubgraph.map_verts, viewSubgraphOfAdj_verts, Relation.Map, ViewSubgraph.map_adj,
    viewSubgraphOfAdj_adj]

theorem neighborSet_viewSubgraphOfAdj_subset {u v w : V} (hvw : G.Adj v w) :
    (G.viewSubgraphOfAdj hvw).neighborSet u ⊆ {v, w} := by
  intro x hx
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  have h2 : s(v, w) = s(u, x) := hx
  have h3 := congrArg (fun e => x ∈ e) h2
  simpa [Sym2.mem_iff] using h3

@[simp]
theorem neighborSet_fst_viewSubgraphOfAdj {v w : V} (hvw : G.Adj v w) :
    (G.viewSubgraphOfAdj hvw).neighborSet v = {w} := by
  ext u
  suffices w = u ↔ u = w by simpa [hvw.ne.symm] using this
  rw [eq_comm]

@[simp]
theorem neighborSet_snd_viewSubgraphOfAdj {v w : V} (hvw : G.Adj v w) :
    (G.viewSubgraphOfAdj hvw).neighborSet w = {v} := by
  rw [viewSubgraphOfAdj_symm hvw.symm]
  exact neighborSet_fst_viewSubgraphOfAdj hvw.symm

@[simp]
theorem neighborSet_viewSubgraphOfAdj_of_ne_of_ne {u v w : V} (hvw : G.Adj v w) (hv : u ≠ v)
    (hw : u ≠ w) : (G.viewSubgraphOfAdj hvw).neighborSet u = ∅ := by
  ext
  simp [hv.symm, hw.symm]

theorem neighborSet_viewSubgraphOfAdj [DecidableEq V] {u v w : V} (hvw : G.Adj v w) :
    (G.viewSubgraphOfAdj hvw).neighborSet u =
    (if u = v then {w} else ∅) ∪ if u = w then {v} else ∅ := by
  split_ifs <;> subst_vars <;> simp [*]

theorem singletonViewSubgraph_fst_le_viewSubgraphOfAdj {u v : V} {h : G.Adj u v} :
    G.singletonViewSubgraph u ≤ G.viewSubgraphOfAdj h := by
  simp [singletonViewSubgraph_le_iff]

theorem singletonViewSubgraph_snd_le_viewSubgraphOfAdj {u v : V} {h : G.Adj u v} :
    G.singletonViewSubgraph v ≤ G.viewSubgraphOfAdj h := by
  simp [singletonViewSubgraph_le_iff]

@[simp]
lemma support_viewSubgraphOfAdj {u v : V} (h : G.Adj u v) :
    (G.viewSubgraphOfAdj h).support = {u, v} := by
  ext
  rw [ViewSubgraph.mem_support]
  simp only [viewSubgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  refine ⟨?_, fun h' => h'.elim (fun hl => ⟨v, .inl ⟨hl.symm, rfl⟩⟩) fun hr => ⟨u, .inr ⟨rfl, hr.symm⟩⟩⟩
  rintro ⟨_, hw⟩
  exact hw.elim (fun h1 => .inl h1.1.symm) fun hr => .inr hr.2.symm

end MkProperties

end ViewSubgraph

/-- Turn a graph `H ≤ G` into a `ViewSubgraph G`. -/
abbrev _root_.SimpleGraph.toViewSubgraph (H : SimpleGraph V) (h : H ≤ G) : G.ViewSubgraph :=
  ViewSubgraph.toViewSubgraph (G := G) H h

theorem _root_.SimpleGraph.toViewSubgraph_isSpanning (H : SimpleGraph V) (h : H ≤ G) :
    (SimpleGraph.toViewSubgraph (G := G) H h).IsSpanning :=
  ViewSubgraph.toViewSubgraph.isSpanning (G := G) H h

@[simp]
theorem card_neighborSet_toViewSubgraph (G H : SimpleGraph V) (h : H ≤ G)
    (v : V) [Fintype ↑((SimpleGraph.toViewSubgraph (G := G) H h).neighborSet v)] [Fintype ↑(H.neighborSet v)] :
    Fintype.card ↑((SimpleGraph.toViewSubgraph (G := G) H h).neighborSet v) = H.degree v := by
  refine (Finset.card_eq_of_equiv_fintype ?_).symm
  simp only [mem_neighborFinset]
  rfl

@[simp]
lemma degree_toViewSubgraph (G H : SimpleGraph V) (h : H ≤ G) {v : V}
    [Fintype ↑((SimpleGraph.toViewSubgraph (G := G) H h).neighborSet v)] [Fintype ↑(H.neighborSet v)] :
    (SimpleGraph.toViewSubgraph (G := G) H h).degree v = H.degree v := by
  simp [ViewSubgraph.degree]

namespace ViewSubgraph

variable {G : SimpleGraph V}

/-! ### View subgraphs of view subgraphs -/

/-- Given a view subgraph of a view subgraph of `G`, construct a view subgraph of `G`. -/
protected abbrev coeSubgraph {G' : G.ViewSubgraph} : G'.coe.ViewSubgraph → G.ViewSubgraph :=
  ViewSubgraph.map G'.hom

/-- Given a view subgraph of `G`, restrict it to being a view subgraph of another view subgraph `G'` by
taking the portion of `G` that intersects `G'`. -/
protected abbrev restrict {G' : G.ViewSubgraph} : G.ViewSubgraph → G'.coe.ViewSubgraph :=
  ViewSubgraph.comap G'.hom

@[simp]
lemma verts_coeSubgraph {G' : ViewSubgraph G} (G'' : ViewSubgraph G'.coe) :
    (ViewSubgraph.coeSubgraph G'').verts = (G''.verts : Set V) :=
  rfl

lemma coeSubgraph_adj {G' : G.ViewSubgraph} (G'' : G'.coe.ViewSubgraph) (v w : V) :
    (G'.coeSubgraph G'').Adj v w ↔
      ∃ (hv : v ∈ G'.verts) (hw : w ∈ G'.verts), G''.Adj ⟨v, hv⟩ ⟨w, hw⟩ := by
  simp [Relation.Map]

lemma restrict_adj {G' G'' : G.ViewSubgraph} (v w : G'.verts) :
    (G'.restrict G'').Adj v w ↔ G'.Adj v w ∧ G''.Adj v w := Iff.rfl

theorem restrict_coeSubgraph {G' : G.ViewSubgraph} (G'' : G'.coe.ViewSubgraph) :
    ViewSubgraph.restrict (ViewSubgraph.coeSubgraph G'') = G'' := by
  ext
  · simp
  · rw [restrict_adj, coeSubgraph_adj]
    simpa using G''.adj_sub

theorem coeSubgraph_injective (G' : G.ViewSubgraph) :
    Function.Injective (ViewSubgraph.coeSubgraph : G'.coe.ViewSubgraph → G.ViewSubgraph) :=
  Function.LeftInverse.injective restrict_coeSubgraph

lemma coeSubgraph_le {H : G.ViewSubgraph} (H' : H.coe.ViewSubgraph) :
    ViewSubgraph.coeSubgraph H' ≤ H := by
  constructor
  · simp
  · rintro v w ⟨_, _, h, rfl, rfl⟩
    exact H'.adj_sub h

/-! ### Edge deletion -/

/-- Given a view subgraph `G'` and a set of vertex pairs, remove all of the corresponding edges
from its edge set, if present.

See also: `SimpleGraph.deleteEdges`. -/
def deleteEdges (G' : G.ViewSubgraph) (s : Set (Sym2 V)) : G.ViewSubgraph where
  verts := G'.verts
  Adj := G'.Adj \ Sym2.ToRel s
  adj_sub h' := G'.adj_sub h'.1
  edge_verts h' := G'.edge_verts h'.1
  symm a b := by simp [G'.adj_comm, Sym2.eq_swap]

section DeleteEdges

variable {G' : G.ViewSubgraph} (s : Set (Sym2 V))

@[simp]
theorem deleteEdges_verts : (G'.deleteEdges s).verts = G'.verts :=
  rfl

@[simp]
theorem deleteEdges_adj (v w : V) : (G'.deleteEdges s).Adj v w ↔ G'.Adj v w ∧ s(v, w) ∉ s :=
  Iff.rfl

@[simp]
theorem deleteEdges_deleteEdges (s s' : Set (Sym2 V)) :
    (G'.deleteEdges s).deleteEdges s' = G'.deleteEdges (s ∪ s') := by
  ext <;> simp [and_assoc, not_or]

@[simp]
theorem deleteEdges_empty_eq : G'.deleteEdges ∅ = G' := by
  ext <;> simp

@[simp]
theorem deleteEdges_spanningCoe_eq :
    G'.spanningCoe.deleteEdges s = (G'.deleteEdges s).spanningCoe := by
  ext
  simp

theorem deleteEdges_coe_eq (s : Set (Sym2 G'.verts)) :
    G'.coe.deleteEdges s = (G'.deleteEdges (Sym2.map (↑) '' s)).coe := by
  ext ⟨v, hv⟩ ⟨w, hw⟩
  simp only [SimpleGraph.deleteEdges_adj, coe_adj, deleteEdges_adj, Set.mem_image, not_exists,
    not_and, and_congr_right_iff]
  intro
  constructor
  · intro hs
    refine Sym2.ind ?_
    rintro ⟨v', hv'⟩ ⟨w', hw'⟩
    simp only [Sym2.map_pair_eq, Sym2.eq]
    contrapose!
    rintro (_ | _) <;> simpa only [Sym2.eq_swap]
  · intro h' hs
    exact h' _ hs rfl

theorem coe_deleteEdges_eq (s : Set (Sym2 V)) :
    (G'.deleteEdges s).coe = G'.coe.deleteEdges (Sym2.map (↑) ⁻¹' s) := by
  ext ⟨v, hv⟩ ⟨w, hw⟩
  simp

theorem deleteEdges_le : G'.deleteEdges s ≤ G' := by
  constructor <;> simp +contextual

theorem deleteEdges_le_of_le {s s' : Set (Sym2 V)} (h : s ⊆ s') :
    G'.deleteEdges s' ≤ G'.deleteEdges s := by
  constructor <;> simp +contextual only [deleteEdges_verts, deleteEdges_adj,
    true_and, and_imp, subset_rfl]
  exact fun _ _ _ hs' hs => hs' (h hs)

@[simp]
theorem deleteEdges_inter_edgeSet_left_eq :
    G'.deleteEdges (G'.edgeSet ∩ s) = G'.deleteEdges s := by
  ext <;> simp +contextual

@[simp]
theorem deleteEdges_inter_edgeSet_right_eq :
    G'.deleteEdges (s ∩ G'.edgeSet) = G'.deleteEdges s := by
  ext <;> simp +contextual [imp_false]

theorem coe_deleteEdges_le : (G'.deleteEdges s).coe ≤ (G'.coe : SimpleGraph G'.verts) := by
  intro v w
  simp +contextual

theorem spanningCoe_deleteEdges_le (G' : G.ViewSubgraph) (s : Set (Sym2 V)) :
    (G'.deleteEdges s).spanningCoe ≤ G'.spanningCoe :=
  spanningCoe_le_of_le (deleteEdges_le s)

end DeleteEdges

/-! ### Induced view subgraphs -/

/-- The induced view subgraph of a view subgraph on a given vertex set. -/
@[simps]
def induce (G' : G.ViewSubgraph) (s : Set V) : G.ViewSubgraph where
  verts := s
  Adj u v := u ∈ s ∧ v ∈ s ∧ G'.Adj u v
  adj_sub h := G'.adj_sub h.2.2
  edge_verts h := Or.inl h.1
  symm _ _ h := ⟨h.2.1, h.1, G'.symm h.2.2⟩

theorem _root_.SimpleGraph.induce_eq_coe_induce_top_view (s : Set V) :
    G.induce s = ((⊤ : G.ViewSubgraph).induce s).coe := by
  ext
  simp

section Induce

variable {G' G'' : G.ViewSubgraph} {s s' : Set V}

@[gcongr]
theorem induce_mono (hg : G' ≤ G'') (hs : s ⊆ s') : G'.induce s ≤ G''.induce s' := by
  constructor
  · simp [hs]
  · simp +contextual only [induce_adj, and_imp]
    intro v w hv hw ha
    exact ⟨hs hv, hs hw, hg.2 ha⟩

@[mono]
theorem induce_mono_left (hg : G' ≤ G'') : G'.induce s ≤ G''.induce s :=
  induce_mono hg subset_rfl

@[mono]
theorem induce_mono_right (hs : s ⊆ s') : G'.induce s ≤ G'.induce s' :=
  induce_mono le_rfl hs

@[simp]
theorem induce_empty : G'.induce ∅ = ⊥ := by
  ext <;> simp

theorem induce_self_verts_le : G'.induce G'.verts ≤ G' := by
  constructor
  · simp
  · intro v w h
    exact h.2.2

lemma le_induce_union : G'.induce s ⊔ G'.induce s' ≤ G'.induce (s ∪ s') := by
  constructor
  · simp only [verts_sup, induce_verts, Set.Subset.rfl]
  · simp only [sup_adj, induce_adj, Set.mem_union]
    rintro v w (h | h) <;> simp [h]

lemma le_induce_union_left : G'.induce s ≤ G'.induce (s ∪ s') := by
  exact induce_mono_right Set.subset_union_left

lemma le_induce_union_right : G'.induce s' ≤ G'.induce (s ∪ s') := by
  exact induce_mono_right Set.subset_union_right

theorem singletonViewSubgraph_eq_induce {v : V} :
    G.singletonViewSubgraph v = (⊤ : G.ViewSubgraph).induce {v} := by
  ext <;> simp +contextual [-Set.bot_eq_empty, Prop.bot_eq_false]

theorem viewSubgraphOfAdj_eq_induce {v w : V} (hvw : G.Adj v w) :
    G.viewSubgraphOfAdj hvw = (⊤ : G.ViewSubgraph).induce {v, w} := by
  ext
  · simp
  · constructor
    · intro h
      simp only [viewSubgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff] at h
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h <;> simp [hvw, hvw.symm]
    · intro h
      simp only [induce_adj, Set.mem_insert_iff, Set.mem_singleton_iff, top_adj] at h
      obtain ⟨rfl | rfl, rfl | rfl, ha⟩ := h <;> first | exact (ha.ne rfl).elim | simp

instance instDecidableRel_induce_adj (s : Set V) [∀ a, Decidable (a ∈ s)] [DecidableRel G'.Adj] :
    DecidableRel (G'.induce s).Adj :=
  fun _ _ => instDecidableAnd

/-- Equivalence between an induced view subgraph and its corresponding simple graph. -/
def coeInduceIso (s : Set V) (h : s ⊆ G'.verts) :
    (G'.induce s).coe ≃g G'.coe.induce {v : G'.verts | ↑v ∈ s} where
  toFun := fun ⟨v, hv⟩ => ⟨⟨v, h hv⟩, by simp at hv; aesop⟩
  invFun := fun ⟨v, hv⟩ => ⟨v, hv⟩
  map_rel_iff' := by simp

end Induce

/-- Given a view subgraph and a set of vertices, delete all the vertices from the view subgraph,
if present. Any edges incident to the deleted vertices are deleted as well. -/
abbrev deleteVerts (G' : G.ViewSubgraph) (s : Set V) : G.ViewSubgraph :=
  G'.induce (G'.verts \ s)

section DeleteVerts

variable {G' : G.ViewSubgraph} {s : Set V}

theorem deleteVerts_verts : (G'.deleteVerts s).verts = G'.verts \ s :=
  rfl

theorem deleteVerts_adj {u v : V} :
    (G'.deleteVerts s).Adj u v ↔ u ∈ G'.verts ∧ u ∉ s ∧ v ∈ G'.verts ∧ v ∉ s ∧ G'.Adj u v := by
  simp [and_assoc]

@[simp]
theorem deleteVerts_deleteVerts (s s' : Set V) :
    (G'.deleteVerts s).deleteVerts s' = G'.deleteVerts (s ∪ s') := by
  ext <;> simp +contextual [not_or, and_assoc]

theorem deleteVerts_le : G'.deleteVerts s ≤ G' := by
  constructor <;> simp [Set.diff_subset]

@[gcongr, mono]
theorem deleteVerts_mono {G' G'' : G.ViewSubgraph} (h : G' ≤ G'') :
    G'.deleteVerts s ≤ G''.deleteVerts s :=
  induce_mono h (Set.diff_subset_diff_left h.1)

@[gcongr, mono]
theorem deleteVerts_anti {s s' : Set V} (h : s ⊆ s') : G'.deleteVerts s' ≤ G'.deleteVerts s :=
  induce_mono (le_refl _) (Set.diff_subset_diff_right h)

@[simp]
theorem deleteVerts_inter_verts_left_eq : G'.deleteVerts (G'.verts ∩ s) = G'.deleteVerts s := by
  ext <;> simp +contextual

@[simp]
theorem deleteVerts_inter_verts_set_right_eq :
    G'.deleteVerts (s ∩ G'.verts) = G'.deleteVerts s := by
  ext <;> simp +contextual

instance instDecidableRel_deleteVerts_adj (u : Set V) [DecidablePred (· ∈ u)] [DecidableRel G.Adj] :
    DecidableRel ((⊤ : G.ViewSubgraph).deleteVerts u).coe.Adj :=
  fun x y =>
    decidable_of_iff (G.Adj x y) <| by
      simp [ViewSubgraph.induce, ViewSubgraph.top_adj]

/-- Equivalence between a view subgraph with deleted vertices and its corresponding simple graph. -/
def coeDeleteVertsIso (s : Set V) :
    (G'.deleteVerts s).coe ≃g G'.coe.induce {v : G'.verts | ↑v ∉ s} where
  toFun := fun ⟨v, hv⟩ => ⟨⟨v, Set.mem_of_mem_inter_left hv⟩, by aesop⟩
  invFun := fun ⟨v, hv⟩ => ⟨v, by simp_all⟩
  map_rel_iff' := by simp

end DeleteVerts

end ViewSubgraph

end SimpleGraph
