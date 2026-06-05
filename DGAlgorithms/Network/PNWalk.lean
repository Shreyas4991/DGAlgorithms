import DGAlgorithms.Network.PNNetwork

namespace DGAlgorithms

-- structure PNEdge {V : Type u} (N : PNNetwork V) where
--   up : N.Port'
--   vp : N.Port'
--   h_neighbor : N.pmap2' up = vp

-- abbrev PNEdge.u {N : PNNetwork V} (e : PNEdge N) : V := e.up.node
-- abbrev PNEdge.v {N : PNNetwork V} (e : PNEdge N) : V := e.vp.node


-- lemma PNEdge.h_neighbor' {N : PNNetwork V} (e : PNEdge N) : N.pmap2' e.vp = e.up := by
--   rw [←PNNetwork.pmap2'.involutive N e.up]; simp [e.h_neighbor]

structure PNEdge {V : Type u} (N : PNNetwork V) (u v : V) where
  ui : ℕ
  ui_valid : N.PortValid (u, ui)
  neighbor : (N.pmap (u, ui)).node = v

abbrev PNEdge.up (e : PNEdge N u v) : N.Port' := ⟨(u, e.ui), e.ui_valid⟩
abbrev PNEdge.vp (e : PNEdge N u v) : N.Port' := ⟨N.pmap (u, e.ui), (N.is_well_defined_iff (u, e.ui)).mpr e.ui_valid⟩

def PNEdge.reverse : PNEdge N u v → PNEdge N v u
  | ⟨ui, ui_valid, neighbor⟩ =>
    ⟨(N.pmap (u, ui)).port,
      by rw [←neighbor]; simp [N.is_well_defined_iff (u, ui), ui_valid],
      by subst neighbor; simp_all⟩

@[simp]
lemma PNEdge.reverse_reverse {N : PNNetwork V} (e : PNEdge N u v) : e.reverse.reverse = e := by
  simp [reverse]
  congr
  conv =>
    enter [1, 1, 2, 1]
    rw [←e.neighbor]
  rw [N.pmap_involutive' (u, e.ui)]
  exact e.ui_valid

@[reducible]
def PNEdge.toPort : PNEdge N u v → N.Port' := fun e => ⟨(u, e.ui), e.ui_valid⟩

-- inductive PNEdge' {V : Type u} (N : PNNetwork V) : V → V → Type u
--   | mk (h : N.pmap2' up = vp) : PNEdge' N up.node vp.node

-- @[match_pattern]
-- abbrev PNEdge'.mk' {N : PNNetwork V} (up vp : N.Port') (h : N.pmap2' up = vp) : PNEdge' N up.node vp.node := .mk h

-- def PNEdge'.up : PNEdge' N u v → N.Port'
--   | .mk' up _ _ => up

-- def PNEdge'.vp : PNEdge' N u v → N.Port'
--   | .mk' _ vp _ => vp
-- def PNEdge'.h : (e : PNEdge' N u v) → N.pmap2' e.up = e.vp
--   | .mk' _ _ h => h


-- def PNEdge'.reverse (e : PNEdge' N u v) : PNEdge' N v u :=
--   .mk' e.vp e.up (by
--     rw [←PNNetwork.pmap2'.involutive N e.up]
--     simp [e.h]
--   )

inductive PNWalk {V : Type u} (N : PNNetwork V) : V → V → Type u
  | nil (v : V) : PNWalk N v v
  | cons (e : PNEdge N u v) (tail : PNWalk N v w) : PNWalk N u w


def PNEdge.toWalk : PNEdge N u v → PNWalk N u v
  | e => .cons e (.nil v)


infixr:67 " :: " => PNWalk.cons

def PNWalk.length : PNWalk N u v → ℕ
  | nil _ => 0
  | cons _ tail => tail.length + 1

@[simp]
lemma PNWalk.length_nil : (PNWalk.nil (N := N) v).length = 0 := by rfl

@[simp]
lemma PNWalk.length_cons {tail : PNWalk N u v} : (e :: tail).length = tail.length + 1 := by rfl

@[simp]
lemma PNEdge.toWalk_length {e : PNEdge N u v} : e.toWalk.length = 1 := by rfl


def PNWalk.vertices {N : PNNetwork V} : PNWalk N u v → List V
| nil v => [v]
| cons e tail => u :: tail.vertices



def PNWalk.append : PNWalk N u v → PNWalk N v w → PNWalk N u w
  | .nil _, bs => bs
  | .cons a as, bs => a :: as.append bs

@[simp]
lemma PNWalk.nil_append {as : PNWalk N u v} : (PNWalk.nil u).append as = as := by rfl
@[simp]
lemma PNWalk.cons_append {e : PNEdge N u' u} {as : PNWalk N u v}  {bs : PNWalk N v w} : (e :: as).append bs = e :: (as.append bs) := by rfl

@[simp]
lemma PNWalk.append_nil {as : PNWalk N u v} : as.append (.nil v) = as := by
  induction as
  case nil => rfl
  case cons e as ih => simp [ih]

@[simp]
lemma PNWalk.append_cons {as : PNWalk N u v} {e : PNEdge N v v'} {bs : PNWalk N v' w} : as.append (e :: bs) = (as.append e.toWalk).append bs := by
  induction as
  case nil => rfl
  case cons e as ih => simp [ih]

@[simp]
lemma PNWalk.append_length {as : PNWalk N u v} {bs : PNWalk N v w} : (as.append bs).length = as.length + bs.length := by
  induction as
  case nil => simp
  case cons a as ih => simp [ih]; omega


def PNWalk.reverseAux {N : PNNetwork V} : PNWalk N w v → PNWalk N w u → PNWalk N v u
| nil _, w => w
| cons e tail, b =>
    reverseAux tail (e.reverse :: b)

@[simp]
lemma PNWalk.reverseAux_nil : (PNWalk.nil v).reverseAux w = w := by rfl

@[simp]
lemma PNWalk.reverseAux_cons {N : PNNetwork V} {e : PNEdge N u v} {tail : PNWalk N v w} {b : PNWalk N u x}:
  (e :: tail).reverseAux b = reverseAux tail (e.reverse :: b) := by rfl

lemma PNWalk.reverseAux_reverseAux {as : PNWalk N a b} {bs : PNWalk N a c} {cs : PNWalk N b d} :
  reverseAux (reverseAux as bs) cs = reverseAux bs (reverseAux (reverseAux as (.nil _)) cs) := by
  induction as generalizing c
  case nil => rfl
  case cons u _ _ e _ ih =>
    simp [ih (bs := e.reverse :: bs), ih (bs := e.reverse :: (.nil u))]


@[simp]
lemma PNWalk.reverseAux_reverseAux_nil {as : PNWalk N a b} {bs : PNWalk N a c} :
  reverseAux (reverseAux as bs) (.nil b) = reverseAux bs as := by
  induction as
  case nil => rfl
  case cons u _ _ e _ ih => simp [ih (bs := e.reverse :: bs)]

lemma PNWalk.reverseAux_eq_append {as : PNWalk N a b} {bs : PNWalk N a c} :
  reverseAux as bs = (reverseAux as (.nil a)).append bs := by
  induction as generalizing c
  case nil => rfl
  case cons a as ih =>
    simp [ih (bs := a.reverse :: bs), ih (bs := a.reverse :: .nil _)]

def PNWalk.reverse {N : PNNetwork V} : PNWalk N u v → PNWalk N v u :=
  fun w => PNWalk.reverseAux w (PNWalk.nil _)

@[simp]
lemma PNEdge.toWalk_reverse {e : PNEdge N u v} : e.toWalk.reverse = e.reverse.toWalk := by rfl

@[simp]
lemma PNWalk.reverse_reverse {as : PNWalk N u v} : as.reverse.reverse = as := by
  simp [reverse]

@[simp]
lemma PNWalk.nil_reverse : (PNWalk.nil (N := N) v).reverse = .nil v := by rfl

@[simp]
lemma PNWalk.cons_reverse {e : PNEdge N u' u} (as : PNWalk N u v) : (e :: as).reverse = as.reverse.append e.reverse.toWalk := by
  induction as
  simp [reverse]
  case nil => rfl
  case cons a as ih =>
    rw [reverse, reverse, ←reverseAux_eq_append]
    simp [PNEdge.toWalk]

@[simp]
lemma PNWalk.reverse_length (as : PNWalk N u v) : as.reverse.length = as.length := by
  induction as
  case nil => rfl
  case cons a as ih => simp [ih]


def PNWalk.ports : PNWalk N u v → List N.Port'
| nil _ => []
| cons e tail => e.toPort :: tail.ports

@[simp]
lemma PNWak.ports_length (w : PNWalk N u v) : w.ports.length = w.length := by
  induction w
  case nil => rfl
  case cons a as ih =>
    unfold PNWalk.ports
    simp [ih]

@[simp]
def PNWalk.nil_ports : (PNWalk.nil (N := N) v).ports = [] := by rfl

@[simp]
def PNWalk.cons_ports {e : PNEdge N u' u} (as : PNWalk N u v) : (e :: as).ports = e.toPort :: as.ports := by rfl


def PNNetwork.Port'.Adjacent {N : PNNetwork V} (p q : N.Port') : Prop := (N.pmap2' p).node = q.node

lemma PNWalk.ports_adjacent (w : PNWalk N u v) : w.ports.IsChain PNNetwork.Port'.Adjacent := by
  match (generalizing := true) w with
  | nil _ => simp
  | cons x (nil _) => simp
  | cons x (cons y tail) =>
    have ih := (cons y tail).ports_adjacent
    simp_all
    unfold PNNetwork.Port'.Adjacent
    have := x.neighbor
    -- rw [PNNetwork.pmap2'_eq_pmap]

    sorry
  -- induction w
  -- case nil => simp
  -- case cons e tail ih =>
  --   induction tail
  --   case nil => simp
  --   case cons e' tail' ih' =>
  --     simp_all

  --     sorry

-- inductive PNWalk' {V : Type u} (N : PNNetwork V) : V → V → Type u
--   | nil (v : V) : PNWalk' N v v
--   | cons (vp : N.Port') (tail : PNWalk' N (N.pmap2' vp).node u) : PNWalk' N vp.node u

-- def PNWalk'.reverseAux {N : PNNetwork V} : PNWalk' N w v → PNWalk' N w u → PNWalk' N v u
-- | nil _, w => w
-- | cons vp tail, b =>
--     reverseAux tail (PNWalk'.cons (N.pmap2' vp) ((PNNetwork.pmap2'.involutive N vp).symm ▸ b))

-- @[simp]
-- lemma PNWalk'.reverseAux_nil : (PNWalk'.nil v).reverseAux w = w := by rfl

-- @[simp]
-- -- lemma PNWalk'.reverseAux_cons {N : PNNetwork V} {vp : N.Port'} {h : (N.pmap2' vp).node = x} {w : PNWalk' N vp.node b} :
-- --   (PNWalk'.cons vp h tail).reverseAux w = reverseAux tail (h.symm ▸ PNWalk'.cons (N.pmap2' vp) (by rfl) (PNNetwork.pmap2'.involutive N vp ▸ w)) := by rfl

-- lemma PNWalk'.reverseAux_reverseAux {N : PNNetwork V} {as : PNWalk' N x y} {bs : PNWalk' N x w} {cs : PNWalk' N y v} :
--   reverseAux (reverseAux as bs) cs = reverseAux bs (reverseAux (reverseAux as (.nil _)) cs) := by
--   -- aesop_unfold reverseAux
--   induction as generalizing w with
--   | nil => rfl
--   | cons vp as ih =>
--     -- have foo := ih (bs := .cons (N.pmap2' vp) ((PNNetwork.pmap2'.involutive N vp).symm ▸ bs))
--     simp [reverseAux]
--     simp [ih (bs := .cons (N.pmap2' vp) ((PNNetwork.pmap2'.involutive N vp).symm ▸ bs))]
--     simp [reverseAux]
--     congr
--     exact PNNetwork.pmap2'.involutive N vp
--     apply eqRec_heq

--     let a := ih (bs := .cons (N.pmap2' vp) ((PNNetwork.pmap2'.involutive N vp).symm ▸ PNWalk'.nil (N := N) vp.node)) (cs := cs)
--     conv =>
--       rhs
--       rw [a]
--     sorry

noncomputable def PNNetwork.edist (N : PNNetwork V) (u v : V) : ℕ∞ :=
  ⨅ w : PNWalk N u v, w.length

def PNNetwork.Connected (N : PNNetwork V) (u v : V) : Prop := ∃ _ : PNWalk N u v, True

def PNNetwork.IsConnected (N : PNNetwork V) : Prop := ∀ u v : V, N.Connected u v
