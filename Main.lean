import Mathlib.Data.Nat.Prime

structure ASer where  -- arithmetic series (k + dn)
  k : Nat  -- constant
  d : Nat  -- difference
deriving Inhabited, Repr

instance : Ord ASer where  -- but there's no List.sort? !!
  compare s1 s2 :=
    match compare s1.k s2.k with
    | .eq => compare s1.d s2.d
    | ord => ord

-- mk k d = k + d*n
def mk (k d : Nat) : ASer := { k := k, d := d }

-- apply formula to n
def ap (s : ASer) (n : Nat) : Nat := s.k + s.d * n

-- apply one formula to another: r(n) := s(t(n))
def compose (s : ASer) (t : ASer) : ASer := mk (s.k + s.d * t.k) (s.d * t.d)

-- identity series
def id1 : ASer := mk 0 1

def partition (s : ASer) (n : Nat) : List ASer :=
  List.range n |>.map fun i => compose s $ mk i n

instance : ToString ASer where
  toString s :=
    if s.k == 0 then
      if s.d == 1 then "n"
      else s!"{s.d}n"
    else if s.d == 0 then s!"{s.k}"
    else if s.d == 1 then s!"n + {s.k}"
    else s!"{s.d}n + {s.k}"

def terms (s : ASer) (n : Nat) : List Nat := List.range n |>.map λ i =>ap s i

-- now for primes ------------------------------------------------

def NPrime : Type := { n: Nat // Nat.Prime n } deriving Repr
instance : ToString NPrime where
  toString s := s!"{s.val}"

structure PrimeSieve where
  ps : List NPrime      -- all primes we've used so far
  pr : Nat              -- current primorial (product of ps)
  np : NPrime           -- next prime
  ss : List ASer        -- list of sequences
deriving Repr

instance : ToString PrimeSieve where
  toString s := s!"ps: {s.ps}, pr: {s.pr}, np: {s.np}, ss: {s.ss}"

def init : PrimeSieve := { ps := [], pr := 1, np := ⟨2,Nat.prime_two⟩, ss := [id1] }

def step (s0 : PrimeSieve) : PrimeSieve :=
  let ps := s0.ps ++ [s0.np]
  let pr := s0.pr * s0.np.val
  let ss0 := (s0.ss.map fun s => partition s s0.np.val).join
  let ss := (ss0.filter fun s => s.k % s0.np.val != 0)  -- strip out multiples of np
  let np := (List.minimum? $ ss.map fun s => (let f1:=ap s 0; if f1 == 1 then ap s 1 else f1)).get! -- series with next prime
  { ps := ps, pr := pr, np := ⟨np,sorry⟩, ss := ss }

def printStep (s : PrimeSieve) (n : Nat) : IO Unit := do
  IO.println s
  s.ss.forM fun s => do
    let width := 15
    let formula := (String.pushn (toString s) ' ' width).take width
    IO.println s!"{formula}: {(terms s n)}"

def main : IO Unit := do
  let mut sv := init
  let n := 10
  printStep sv n
  for _ in [0:5] do
    sv := step sv
    IO.println "----------------"
    printStep sv n

#eval main
