-- PrimeGen: a specification for algorithms that generate prime numbers.
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.Linarith.Frontend

def NPrime : Type := { n: Nat // Nat.Prime n } deriving Repr, Ord, LT, LE

@[simp] theorem NPrime.eq_iff (a b : NPrime) : a = b ↔ a.val = b.val := Subtype.ext_iff
instance : ToString NPrime where toString s := s!"{s.val}"
instance : Dvd NPrime where dvd a b := a.val ∣ b.val
instance : Coe NPrime Nat where coe n := n.val
-- interestingly, the following seems to shadow normal Nat ∈ Set Nat operations.
-- instance : Membership NPrime (Set Nat) where mem n s := n.val ∈ s

class PrimeGen (α : Type) where
  P : α → NPrime
  init : α
  next : α → α
  hP' (g:α) : (¬∃ q:NPrime, P g < q ∧  q < P (next g))
open PrimeGen

section simple_gen

  abbrev prime_gt n p := Nat.Prime p ∧ n < p
  instance : Decidable (prime_gt c p) := by rw[prime_gt]; apply inferInstanceAs
  theorem ex_prime_gt (c:Nat) : ∃ p, prime_gt c p := by
    simp[prime_gt]
    let d := c + 1 -- because the line below has ≤ and we need <
    let ⟨p, hcp, hprime⟩ : ∃ (p : ℕ), d ≤ p ∧ Nat.Prime p :=
      Nat.exists_infinite_primes d
    use p; apply And.intro
    · exact hprime
    · linarith

  structure MinPrimeGt (n:Nat) where
    p : Nat
    hp : Nat.Prime p
    hpgt : prime_gt n p
    hmin : ∀q:Nat, q < p → (¬ prime_gt n q)
    hmin' : ∀q:Nat, prime_gt n q → p ≤ q

  def min_prime_gt (n: Nat) : MinPrimeGt n :=
    let e := ex_prime_gt n
    { p:=Nat.find e,
      hp:=by have h:= Nat.find_spec e; simp[h],
      hpgt:=Nat.find_spec e,
      hmin:= by exact fun {q} a => Nat.find_min e a,
      hmin':=by exact fun q a => Nat.find_min' e a}

  structure SimpleGen where
    p : NPrime
    c : MinPrimeGt p.val

  def SimpleGen.next (g:SimpleGen) : SimpleGen :=
    { p:=⟨g.c.p, g.c.hp⟩, c:=min_prime_gt g.c.p }

  instance : PrimeGen SimpleGen where
    P g := g.p
    init := {p := ⟨2, Nat.prime_two⟩, c := min_prime_gt 2 }
    next := .next
    hP' g := by  -- goal: no prime q between g.p and (g.next.p = g.c.p)
      -- why? that would imply prime_gt (g.p) q, but hmin contradicts this
      unfold SimpleGen.next; simp; intro q qgtp; by_contra hq
      have h0 := g.c.hmin; simp at h0
      apply h0 at hq
      have : ¬q.val>g.p.val := by exact Nat.not_lt.mpr (hq q.prop)
      have : ¬g.p < q := by aesop
      contradiction

  open PrimeGen

end simple_gen


/- function power. apply f recursively n times to x₀ and collect the results -/
def fpow (f : α → α) (n:Nat) (x₀ : α) : List α :=
  let rec aux (n:Nat) (x:α) (acc:List α) :=
    if n = 0 then x::acc
    else aux (n-1) (f x) (x::acc)
  aux n x₀ [] |>.reverse

#eval fpow (λn => n+1) 10 0

def primes (α : Type) [pg: PrimeGen α] (n : Nat) : List NPrime :=
  fpow (fun g => pg.next g) n pg.init |>.map fun g => pg.P g

#eval primes SimpleGen 10
