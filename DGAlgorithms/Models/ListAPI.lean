import Mathlib
import Batteries

set_option linter.unusedTactic false

def isUnique (xs : List α) : Prop :=
  match xs with
  | [] => True
  | y :: ys => ¬ y ∈ ys ∧ isUnique ys

def toUnique [DecidableEq α] (xs : List α) : List α :=
  match xs with
  | [] => []
  | y :: ys =>
      let ys' := toUnique ys
      if y ∈ ys then ys' else y :: ys'

lemma uniqueness_preserves_elem [DecidableEq α] (l : List α) :
  ∀ x : α, x ∈ l → x ∈ (toUnique l) := by
  intro x x_mem
  induction l with
  | nil =>
      simp at x_mem
  | cons head tail ih =>
      unfold toUnique
      cases x_mem with
      | head rest =>
          by_cases h : x ∈ tail <;> simp [h]
          apply ih h
      | tail b rest =>
          by_cases h_in_l : (head ∈ tail) <;> simp[h_in_l]
          apply ih
          case pos =>
            exact rest
          case neg =>
            right
            apply ih
            exact rest

lemma uniqueness_elem_implies_elem [DecidableEq α] (l : List α) :
  ∀ x : α, x ∈ (toUnique l) → x ∈ l := by
  intro x x_elem
  induction l with
  | nil =>
      simp_all only [List.not_mem_nil, toUnique]
  | cons head tail ih =>
      simp [toUnique] at x_elem
      by_cases h : head ∈ tail <;> simp_all [h]
      case neg =>
        tauto

lemma uniqueness_correct [DecidableEq α] (l : List α): isUnique (toUnique l) := by
  induction l with
  | nil =>
      simp[isUnique]
  | cons head tail ih =>
      simp [toUnique]
      by_cases h : head ∈ tail <;> simp_all [h]
      case neg =>
        unfold isUnique
        simp [ih]
        intro h'
        apply uniqueness_elem_implies_elem at h'
        exact h h'



-- Filter Helper lemmas
lemma List.filter_pred: ∀ l : List α, ∀ p : α → Bool,
  x ∈ (List.filter p l) → p x = true := by
  intros l p a
  apply List.of_mem_filter a

lemma List.membership : ∀ l r : List α, l = r → ∀ x : α, x ∈ l ↔ x ∈ r := by
  intro l r eq x
  exact Eq.to_iff (congrArg (Membership.mem x) eq)

lemma List.filter_equiv : ∀ l : List α, ∀ p q : α → Bool,
  (List.filter p l) = (List.filter q l) → ∀ x ∈ l, p x ↔ q x := by
  intro l p q heq
  intro x x_elem_l
  apply List.membership at heq
  constructor
  · intro hp
    replace heq := (heq x).mp
    have hfiltp : x ∈ List.filter p l := by
      apply List.mem_filter.mpr
      exact And.intro x_elem_l hp
      done
    apply heq at hfiltp
    have hnext := List.mem_filter.mp hfiltp
    exact hnext.right
  · intro hq
    replace heq := (heq x).mpr
    have hfiltp : x ∈ List.filter q l := by
      apply List.mem_filter.mpr
      exact And.intro x_elem_l hq
      done
    apply heq at hfiltp
    have hnext := List.mem_filter.mp hfiltp
    exact hnext.right
  done
