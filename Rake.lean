-- For the purposes of this library, a "Rake" is a sorted
-- list of arithmetic sequences that share the same delta.
import ASeq
import MathLib.Data.List.Sort
import Mathlib.Tactic.Ring

def DSeq (d : Nat) := { s : ASeq // s.d = d }
instance : Inhabited (DSeq d) := ⟨⟨ASeq.mk 0 d, rfl⟩⟩
instance : CoeFun (DSeq d) fun _ => Nat → Nat := ⟨λs => s.val⟩
instance : Ord (DSeq d) where compare a b := compare a.val b.val
instance : LT (DSeq d) where lt a b := a.val.k < b.val.k
def dseq (k : Nat) (d : Nat) : DSeq d := ⟨ASeq.mk k d, rfl⟩

structure Rake where
  d : Nat
  seqs : List (DSeq d)
  hsort : List.Sorted (·<·) seqs
  hsize : seqs.length > 0

def Rake.term (r : Rake) (n : Nat) : Nat :=
  let q := r.seqs.length
  have : n%q < r.seqs.length := Nat.mod_lt _ r.hsize
  r.seqs[n%q] (n/q)

def idr : Rake := { -- the identity rake (maps n -> n)
  d := 1,
  seqs := [dseq 0 1],
  hsort := List.sorted_singleton _,
  hsize := Nat.zero_lt_one}

-- proof that idr represents the identity function
theorem idr_id (n:Nat) : (idr.term n = n) := by
  simp [Rake.term, idr]
  unfold dseq
  unfold term
  simp
