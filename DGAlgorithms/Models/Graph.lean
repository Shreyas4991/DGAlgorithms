import Mathlib

structure Graph (α : Type) (n : Nat) where
  data : Vector α n
  adj_arr : Vector (Array <| Fin n) n

def fromArr [Inhabited α] (n : Nat)
  (inp : Vector (Array (Fin n)) n) : Graph α n :=
  {
    data := Vector.replicate n default ,
    adj_arr := inp
  }

def ex1 : Graph Nat 3 := fromArr 3 ⟨[#[0,1], #[0,2], #[1,2]], by simp⟩
