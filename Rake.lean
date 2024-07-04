-- For the purposes of this library, a "Rake" is a sorted
-- list of arithmetic sequences that share the same delta.
import ASeq
import MathLib.Data.Nat.Prime
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

def Rake.gte (r : Rake) (n : Nat) : Rake := {
  d := r.d,
  seqs := r.seqs.map (λ s => ⟨ASeq.gte s.val n, (by
    have : s.val.d = r.d := s.property
    symm at this
    simp[this]
    apply ASeq.gte_same_delta s.val n)⟩),
  hsort := (sorry),
  hsize := (by simp[List.length_mergeSort]; exact r.hsize)}

def idr : Rake := { -- the identity rake (maps n -> n)
  d := 1,
  seqs := [dseq 0 1],
  hsort := List.sorted_singleton _,
  hsize := Nat.zero_lt_one }

structure RakeMap (prop: Nat → Prop) where
  rake : Rake
  hbij : ∀ n, prop n ↔ ∃ m, rake.term m = n

-- proof that idr represents the identity function
def idrm : RakeMap (λ _ => True) := {
  rake := idr,
  hbij := by intro n; simp[Rake.term, idr]; unfold dseq; unfold term; simp }

def RakeMap.gte (self : RakeMap prop) (p: Nat) (hp: Nat.Prime p)
  : (RakeMap (λ n => prop n ∧ ¬(p∣n))) := sorry
