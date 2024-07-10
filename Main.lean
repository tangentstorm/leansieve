import ASeq
import PrimeGen
import MathLib.Data.List.Sort

structure ASeqPrimeSieve where
  d : Nat               -- d : delta for all sequences. a primorial
  c : NPrime            -- the current prime
  ss : List ASeq        -- list of sequences
  ps : List NPrime      -- all primes we've used so far
deriving Repr

instance : ToString ASeqPrimeSieve where
  toString s :=
    let K := s.ss.map (λseq => seq.k)             -- const terms of all the sequences
    let h := s.c.val ^ 2                          -- the "horizon" (all K below this are prime)
    let q := K.filter (λk => k<h)                 -- the "queue" of identified unreported primes
    let x := K.filter (λk => k≥h) |> List.length  -- number K not in Q
    let r := s.ss.length                          -- total number of sequences
    s!"d:{s.d} c:{s.c} h:{h} |q|:{q.length} |x|:{x} |ss|:{r}"--"\nq:{q}\nps:{s.ps}"

def init : ASeqPrimeSieve := {
  ps := [], d := 1,
  c := ⟨2,Nat.prime_two⟩,
  ss := [ASeq.mk 2 1]  }

def step (s0 : ASeqPrimeSieve) : Option ASeqPrimeSieve :=
  let ps := s0.ps ++ [s0.c]
  let d := s0.d * s0.c.val
  let ss0 := (s0.ss.map fun s => partition s s0.c).join
  let ss := (ss0.filter fun s => s.k % s0.c.val != 0)  -- strip out multiples of np
  let c := (List.minimum? $ ss.map fun s => s 0).get!  -- series with next prime
  if runtime_check : Nat.Prime c then
    some { ps := ps, d := d, c := ⟨c, runtime_check⟩, ss := ss }
  else panic! "not prime"

def printStep (s : ASeqPrimeSieve) (nterms : Nat) : IO Unit := do
  IO.println "-------------------------"
  IO.println s
  s.ss.forM fun s => do
    let width := 15
    let formula := (String.pushn (toString s) ' ' width).take width
    IO.println s!"{formula}: {(terms s nterms)}"

def iters (n:Nat) : IO Unit := do
  let mut sv := init
  printStep sv 5
  for _ in [0:n] do
    match (step sv) with
    | some siv =>
        sv := siv
        printStep siv n
    | none => panic! "ran out of primes!?!"

#eval iters 5

def main : IO Unit := do iters 10
