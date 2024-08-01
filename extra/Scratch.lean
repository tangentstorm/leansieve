import Mathlib.Tactic

#print Iff.intro


-- bayesian / fuzzy logic ---------------------------------------

inductive Bayes (E : Prop) : Type where
  | BZero
  | BConf (e : E) (c:Rat) -- { r:Rat // r>0 ∧ r ≤ 1 }
deriving Repr

open Bayes

def bAnd {P Q: Prop} (bp: Bayes P) (bq:Bayes Q) : Bayes (P ∧ Q) :=
  match (bp, bq) with
  | (BConf p pc, BConf q qc) => BConf ⟨p,q⟩ (pc*qc)
  | _ => BZero

-- you have to provide a demonstration that the fact is true
-- as if all your confidence levels were 1
def bp : Bayes (Nat.Prime 5) := BConf Nat.prime_five 1
def bq : Bayes (2 < 5) := BConf (by aesop) 0.5
def br : Bayes (2 > 5) := BZero

#eval bAnd bp bq -- confidence 1/2
#eval bAnd bq br -- confidence zero


-- proving a relation ----------------------------------------

example {x y : ℤ } (h1 : y = (x-2)*(x+2)) (h2: x ≥ 0) : y ≥ -4 :=
  calc
    y = (x-2)*(x+2) := h1
    -- _ ≥ (0-2)*(x+2) := by rel[h2]
    _ = x^2 - 4 := by ring
    _ ≥ 0^2 - 4 := by rel[h2]
    _ =      -4 := by simp


--- a lemma i needed for ASeq

lemma self_lt_mul_div_add (n d : Nat) (hd: 0 < d) : n ≤ d * (n/d + 1) := by
  have : 1 ≤ d := by aesop
  have : n ≤ d * n := by apply?
    -- n ≤ d * n        := by
    -- _ ≤ d * (n +1)   := by aesop
    -- _ ≤ d * (n/d +1) := by rel[h1]

    -- _ ≥ 1 * (n/d + 1)  := by rel[h1]

  sorry
  -- set r := n % d with hr
  -- set q := n / d with hq
  -- simp[← hq]
  -- have : d * (n/d) + (n % d) = n := Nat.div_add_mod n d
  -- have : r + d * q = n := by rw[←hq, ←hr] at this; linarith
  -- have : r < d := Nat.mod_lt n hd
  -- linarith
