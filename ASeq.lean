-- ASeq: Arithmetic Sequences
import Mathlib.Tactic

structure ASeq where  -- arithmetic sequence (k + dn)
  k : Nat  -- constant
  d : Nat  -- delta (step size)
deriving Repr

instance : Inhabited ASeq where
  default := .mk 0 1

instance : Ord ASeq where  -- !! TODO: use with List.mergeSort
  compare s1 s2 :=
    match compare s1.k s2.k with
    | .eq => compare s1.d s2.d
    | ord => ord

-- apply formula to n
def term (s : ASeq) (n : Nat) : Nat := s.k + s.d * n

-- apply one formula to another: r(n) := s(t(n))
def compose (s : ASeq) (t : ASeq) : ASeq := .mk (s.k + s.d * t.k) (s.d * t.d)

-- generate n terms of a sequence
def terms (s : ASeq) (n : Nat) : List Nat := List.range n |>.map λ i => term s i

-- identity sequence
def ids : ASeq := .mk 0 1
def evens : ASeq := .mk 0 2
def odds : ASeq := .mk 1 2

#eval terms ids 10  -- [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
#eval terms evens 10  -- [0, 2, 4, 6, 8, 10, 12, 14, 16, 18]
#eval terms odds 10  -- [1, 3, 5, 7, 9, 11, 13, 15, 17, 19]

-- use sequence like a function
instance : CoeFun ASeq fun _ => Nat → Nat := ⟨term⟩

#eval evens 10  -- 20

def partition (s : ASeq) (n : Nat) : List ASeq :=
  List.range n |>.map fun i => compose s $ .mk i n

instance : ToString ASeq where
  toString s :=
    if s.k == 0 then
      if s.d == 1 then "n"
      else s!"{s.d}n"
    else if s.d == 0 then s!"{s.k}"
    else if s.d == 1 then s!"{s.k} + n"
    else s!"{s.k} + {s.d}n"

-- limit results to those greater than or equal to n
def gte (s : ASeq) (n : Nat) : ASeq :=
  if n ≤ s.k then s
  else if n ≤ s.d then .mk (s.k + s.d) s.d
  else
    let t := n / s.d
    ASeq.mk (s.k + s.d * (t + 1)) s.d

theorem self_lt_mul_div_add (n d : Nat) (hd: d > 0) : n ≤ d * (n/d + 1) := by
  set r := n % d with hr
  set q := n / d with hq
  simp[← hq]
  have : d * (n/d) + (n % d) = n := Nat.div_add_mod n d
  have : r + d * q = n := by rw[←hq, ←hr] at this; linarith
  have : r < d := Nat.mod_lt n hd
  linarith

theorem gte_term (s : ASeq) (n : Nat) : s.d > 0 → n ≤ term (gte s n) 0 := by
  intro hdz
  simp[term,gte]
  if hsk : n ≤ s.k then simp [hsk]
  else if hsd : n ≤ s.d then simp [hsd, hsk]; linarith
  else
    simp[hsk,hsd]
    have hle: n ≤ s.d * (n/s.d + 1) := self_lt_mul_div_add n s.d hdz
    linarith
