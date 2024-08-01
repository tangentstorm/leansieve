
structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

abbrev idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced Spider"
  ]
}

def NonEmptyList.get? : NonEmptyList α -> Nat -> Option α
  | xs, 0 => some xs.head
  | xs , n+1 => xs.tail.get? n

abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length

/-
unsolved goals

⊢ 2 ≤ idahoSpiders.tail.length
-/
theorem atLeastThreeSpiders : idahoSpiders.inBounds 2 := by
  simp
