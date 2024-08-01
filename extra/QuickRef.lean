
-- see also:
-- https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_C/cheatsheet.html
-- (and that whole site)
import Mathlib.Tactic

#eval 2 + 2 -- 4
#check 2 -- 2 : Nat

section proofs

  variable {p q : Prop}

  example : p → q → p :=
    fun hp : p =>
    fun hq : q =>
    show p from hp

end proofs

-- `Xx.intro` is constructor for logical X operator
-- Xx ∈ {Iff, And, Or, Eq, Exists, }
theorem and_commutative : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (λ h : p ∧ q => show q ∧ p from And.intro (And.right h) (And.left h))
    (λ h : q ∧ p => show p ∧ q from And.intro (And.right h) (And.left h))


-- by : enter tactic mode
-- rw
-- simp
-- apply
-- conv  : lhs, rhs
-- congr
-- rfl
-- intro
-- funext
-- simp
-- exact
-- skip

-- universe
-- namespace X (... end X)?
-- notation
-- syntax
-- setext propext funext
-- open Ns renaming x → y, p → q
-- protected def X --> prevents X from being used without namespace qualifier

-- notation:65 lhs:65 " + " rhs:66 => HAdd.hAdd lhs rhs

#eval 5 < 2
#check 5 < 2
#reduce 5 < 2

#check And.intro
#check @And.intro

#infix:50 "⊞" => (· + ·)
#eval 3 ⊞ 4



syntax enterArg := ident <|> group("@"? num)
syntax "onter " "[" (colGt enterArg),+ "]": conv
macro_rules
  | `(conv| enter [$i:num]) => `(conv| arg $i)
  | `(conv| enter [@$i:num]) => `(conv| arg @$i)
  | `(conv| enter [$id:ident]) => `(conv| ext $id)
  | `(conv| enter [$arg:enterArg, $args,*]) => `(conv| (enter [$arg]; enter [$args,*]))



example (m n: Nat) (p: Prop): p := by
  apply ltByCases m n
  · show m < n → p ; sorry
  · show m = n → p ; sorry
  · show m > n → p ; sorry
