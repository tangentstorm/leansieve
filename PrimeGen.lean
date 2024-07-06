-- PrimeGen: a specification for algorithms that generate prime numbers.
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.Linarith.Frontend

def NPrime : Type := { n: Nat // Nat.Prime n } deriving Repr
instance : ToString NPrime where
  toString s := s!"{s.val}"

-- these let us get rid of .val to unwrap in the definitions:
instance : LT NPrime where lt a b := a.val < b.val
instance : LE NPrime where le a b := a.val < b.val
instance : Dvd NPrime where dvd a b := a.val ∣ b.val
instance : Coe NPrime Nat where coe n := n.val
-- interestingly, this seems to shadow normal Nat ∈ Set Nat operations.
-- instance : Membership NPrime (Set Nat) where mem n s := n.val ∈ s

class PrimeGen (α : Type u) where
  C : α → NPrime
  init : α
  next : α → α

section simple_gen

  def prime_gt (c : Nat) (p : Nat) : Prop :=
    Nat.Prime p ∧ c < p

  instance : Decidable (prime_gt c p) := by
    rw[prime_gt]; apply inferInstanceAs

  theorem ex_prime_gt (c:Nat) : ∃ p, prime_gt c p := by
    simp[prime_gt]
    let d := c + 1 -- because the line below has ≤ and we need <
    let ⟨p, hcp, hprime⟩ : ∃ (p : ℕ), d ≤ p ∧ Nat.Prime p :=
      Nat.exists_infinite_primes d
    use p; apply And.intro
    · exact hprime
    · linarith

  -- Use Nat.find to get the smallest n that satisfies P
  def next_prime (c:Nat) : Nat := Nat.find <| ex_prime_gt c

  def PrimeGt (c:Nat): Type := { p : Nat // prime_gt c p }

  def next_primegt (c: Nat) : PrimeGt c :=
    ⟨Nat.find (ex_prime_gt c), Nat.find_spec (ex_prime_gt c)⟩

  def nprime_gt (pg:PrimeGt c): NPrime :=
    ⟨pg.val, (by
      have : prime_gt c pg.val := pg.property
      simp[prime_gt] at this
      exact this.left)⟩

  def next_nprime (c:Nat) : NPrime :=
    nprime_gt (next_primegt c)

  structure SimpleGen where
    c : NPrime
  deriving Repr

  instance : PrimeGen SimpleGen where
    C x := x.c
    init := ⟨⟨2, Nat.prime_two⟩⟩
    next x := ⟨next_nprime x.c⟩
  open PrimeGen

end simple_gen


/- function power. apply f recursively n times to x₀ and collect the results -/
def fpow (f : α → α) (n:Nat) (x₀ : α) : List α :=
  let rec aux (n:Nat) (x:α) (acc:List α) :=
    if n = 0 then x::acc
    else aux (n-1) (f x) (x::acc)
  aux n x₀ []

#eval fpow (λn => n+1) 10 0

def primes (α : Type) [pg: PrimeGen α] (n : Nat) : List NPrime :=
  fpow (fun g => pg.next g) n pg.init |>.map fun x => pg.C x

#eval primes SimpleGen 10
