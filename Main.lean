import ASeq
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.Linarith.Frontend

def NPrime : Type := { n: Nat // Nat.Prime n } deriving Repr
instance : ToString NPrime where
  toString s := s!"{s.val}"

structure PrimeSieve where
  ps : List NPrime      -- all primes we've used so far
  pr : Nat              -- current primorial (product of ps)
  np : NPrime           -- next prime
  ss : List ASeq        -- list of sequences
deriving Repr

instance : ToString PrimeSieve where
  toString s := s!"ps: {s.ps}, pr: {s.pr}, np: {s.np}, ss: {s.ss}"

def init : PrimeSieve := { ps := [], pr := 1, np := ⟨2,Nat.prime_two⟩, ss := [mk 2 1] }

def step (s0 : PrimeSieve) : PrimeSieve :=
  let ps := s0.ps ++ [s0.np]
  let pr := s0.pr * s0.np.val
  let ss0 := (s0.ss.map fun s => partition s s0.np.val).join
  let ss := (ss0.filter fun s => s.k % s0.np.val != 0)  -- strip out multiples of np
  let np := (List.minimum? $ ss.map fun s => (let f1:=ap s 0; if f1 == 1 then ap s 1 else f1)).get! -- series with next prime
  { ps := ps, pr := pr, np := ⟨np,sorry⟩, ss := ss }

lemma no_prime_factors_im_no_factors {c:ℕ} -- c is a candidate prime
  (h2lc: 2 ≤ c)                              -- c is at least 2
  (hnpf: ∀ p < c, Nat.Prime p → ¬(p∣c))      -- c has no prime factors
  : Nat.Prime c := by
    have : ∀ m < c, m ∣ c → m=1 := by  -- c has no divisors but 1 and c
      intro m hmc hmdc  -- give names to the above assumptions
      by_contra         -- assume ¬(m=1) and show contradiction
      obtain ⟨p, hpp, hpm⟩ : ∃ p, Nat.Prime p ∧ p ∣ m :=
        Nat.exists_prime_and_dvd ‹m ≠ 1›
      have : p∣c := Nat.dvd_trans hpm hmdc
      have : ¬(p∣c) := by
        have : 0 < c := by linarith
        have : 0 < m := Nat.pos_of_dvd_of_pos hmdc this
        have : p ≤ m := Nat.le_of_dvd this hpm
        have : p < c := by linarith
        exact hnpf p this hpp
      contradiction
    exact Nat.prime_def_lt.mpr ⟨‹2 ≤ c› , this⟩

-- excetuion ------------------------------------------------

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
