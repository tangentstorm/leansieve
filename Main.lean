import ASeq
import PrimeGen

structure ASeqPrimeSieve where
  ps : List NPrime      -- all primes we've used so far
  pr : Nat              -- current primorial (product of ps)
  np : NPrime           -- next prime
  ss : List ASeq        -- list of sequences
deriving Repr

instance : ToString ASeqPrimeSieve where
  toString s := s!"ps: {s.ps}, pr: {s.pr}, np: {s.np}, ss: {s.ss}"

def init : ASeqPrimeSieve := {
  ps := [], pr := 1,
  np := ⟨2,Nat.prime_two⟩,
  ss := [ASeq.mk 2 1]  }

def step (s0 : ASeqPrimeSieve) : ASeqPrimeSieve :=
  let ps := s0.ps ++ [s0.np]
  let pr := s0.pr * s0.np.val
  let ss0 := (s0.ss.map fun s => partition s s0.np.val).join
  let ss := (ss0.filter fun s => s.k % s0.np.val != 0)  -- strip out multiples of np
  let np := (List.minimum? $ ss.map fun s => (let f1:=s 0; if f1 == 1 then s 1 else f1)).get! -- series with next prime
  { ps := ps, pr := pr, np := ⟨np,sorry⟩, ss := ss }

def printStep (s : ASeqPrimeSieve) (n : Nat) : IO Unit := do
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
