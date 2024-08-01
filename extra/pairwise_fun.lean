import Batteries.Data.List.Pairwise

example
  {xs:List Nat} {p p' q : Nat → Nat → Prop}
  {hp' : p' = λx y => p x y ∨ q x y}
  (h₀: List.Pairwise p xs)
  : List.Pairwise p' xs := by
  simp_all
  show List.Pairwise (fun x y => p x y ∨ q x y) xs
  have : ∀ {x y:Nat}, p x y → p x y ∨ q x y := by exact fun {x y} a => Or.intro_left (q x y) a
  exact List.Pairwise.imp this h₀
