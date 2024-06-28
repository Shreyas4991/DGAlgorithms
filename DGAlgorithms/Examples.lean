import DGAlgorithms.PortNumbered
import DGAlgorithms.CoveringMap

namespace NonSimplePortNumbered

/-- An example non simple port numbered network. -/
def eg : NonSimplePortNumbered (Fin 4) where
  degree := ![2, 2, 3, 4]
  ofPort := Fin.cons ![0, 1] <|
            Fin.cons ![2, 0] <|
            Fin.cons ![3, 1, 3] <|
            Fin.cons ![2, 2, 3, 3] <|
            fun i => Fin.elim0 i
  reversePort := Fin.cons (Fin.cons (0 : Fin 2) <|
                           Fin.cons (1 : Fin 2) <|
                           fun i => Fin.elim0 i) <|
                 Fin.cons (Fin.cons (1 : Fin 3) <|
                           Fin.cons (1 : Fin 2) <|
                           fun i => Fin.elim0 i) <|
                 Fin.cons (Fin.cons (0 : Fin 4) <|
                           Fin.cons (0 : Fin 2) <|
                           Fin.cons (1 : Fin 4) <|
                           fun i => Fin.elim0 i) <|
                 Fin.cons (Fin.cons (0 : Fin 3) <|
                           Fin.cons (2 : Fin 3) <|
                           Fin.cons (3 : Fin 4) <|
                           Fin.cons (2 : Fin 4) <|
                           fun i => Fin.elim0 i) <|
                 fun i => Fin.elim0 i
  ofPort_reversePort := by decide
  coe_reversePort_reversePort := by decide

def eg' : NonSimplePortNumbered (Fin 4) :=
  let degree : Fin 4 → ℕ := ![2, 2, 3, 4]
  let fn : (v : Fin 4) × Fin (degree v) → (v : Fin 4) × Fin (degree v)
    | ⟨0, (0 : Fin 2)⟩ => ⟨0, (0 : Fin 2)⟩
    | ⟨0, (1 : Fin 2)⟩ => ⟨1, (1 : Fin 2)⟩
    | ⟨1, (0 : Fin 2)⟩ => ⟨2, (1 : Fin 3)⟩
    | ⟨1, (1 : Fin 2)⟩ => ⟨0, (1 : Fin 2)⟩
    | ⟨2, (0 : Fin 3)⟩ => ⟨3, (0 : Fin 4)⟩
    | ⟨2, (1 : Fin 3)⟩ => ⟨1, (0 : Fin 2)⟩
    | ⟨2, (2 : Fin 3)⟩ => ⟨3, (1 : Fin 4)⟩
    | ⟨3, (0 : Fin 4)⟩ => ⟨2, (0 : Fin 3)⟩
    | ⟨3, (1 : Fin 4)⟩ => ⟨2, (2 : Fin 3)⟩
    | ⟨3, (2 : Fin 4)⟩ => ⟨3, (3 : Fin 4)⟩
    | ⟨3, (3 : Fin 4)⟩ => ⟨3, (2 : Fin 4)⟩
  mk' _ degree fn (by decide : ∀ _, _)

def eg3_1 : NonSimplePortNumbered (Fin 4) :=
  let degree : Fin 4 → ℕ := ![3, 2, 2, 1]
  let fn : (v : Fin 4) × Fin (degree v) → (v : Fin 4) × Fin (degree v)
    | ⟨0, (0 : Fin 3)⟩ => ⟨1, (0 : Fin 2)⟩
    | ⟨0, (1 : Fin 3)⟩ => ⟨2, (0 : Fin 2)⟩
    | ⟨0, (2 : Fin 3)⟩ => ⟨3, (0 : Fin 1)⟩
    | ⟨1, (0 : Fin 2)⟩ => ⟨0, (0 : Fin 3)⟩
    | ⟨1, (1 : Fin 2)⟩ => ⟨2, (1 : Fin 2)⟩
    | ⟨2, (0 : Fin 2)⟩ => ⟨0, (1 : Fin 3)⟩
    | ⟨2, (1 : Fin 2)⟩ => ⟨1, (1 : Fin 2)⟩
    | ⟨3, (0 : Fin 1)⟩ => ⟨0, (2 : Fin 3)⟩
  mk' _ degree fn (by decide : ∀ _, _)

def eg3_1' : PortNumbered (Fin 4) :=
  PortNumbered.fromNonSimple eg3_1 (by decide) (by decide)

end NonSimplePortNumbered

-- #check SimpleGraph.Box

abbrev graph7_8t : Type := Option (Fin 3 × (Unit ⊕ Bool ⊕ Bool))

def graph7_8_adj : graph7_8t → graph7_8t → Bool
  | none, none => False
  | none, some (_, Sum.inl _) => True
  | none, some (_, Sum.inr _) => False
  | some (_, Sum.inl _), none => True
  | some (_, Sum.inr _), none => False
  | some (_, Sum.inl _), some (_, Sum.inl _) => False
  | some (i, Sum.inl _), some (j, Sum.inr (Sum.inl _)) => i = j
  | some (i, Sum.inr (Sum.inl _)), some (j, Sum.inl _) => i = j
  | some (_, Sum.inr (Sum.inl _)), some (_, Sum.inr (Sum.inl _)) => False
  | some (_, Sum.inl _), some (_, Sum.inr (Sum.inr _)) => False
  | some (_, Sum.inr (Sum.inr _)), some (_, Sum.inl _) => False
  | some (i, Sum.inr (Sum.inl _)), some (j, Sum.inr (Sum.inr _)) => i = j
  | some (i, Sum.inr (Sum.inr _)), some (j, Sum.inr (Sum.inl _)) => i = j
  | some (i, Sum.inr (Sum.inr x)), some (j, Sum.inr (Sum.inr y)) => i = j ∧ x ≠ y

def graph7_8 : SimpleGraph graph7_8t where
  Adj x y := graph7_8_adj x y
  symm := (by decide : ∀ x, _)
  loopless := (by decide : ∀ x, _)

instance : DecidableRel graph7_8.Adj := fun v w => inferInstanceAs (Decidable (graph7_8_adj v w))

-- #eval (PortNumbered.inducing graph7_8).card
