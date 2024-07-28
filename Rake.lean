-- For the purposes of this library, a "Rake" is a sorted
-- list of arithmetic sequences that share the same delta.
import ASeq
import MathLib.Data.List.Sort
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Basic

structure Rake : Type where
  d     : Nat
  ks    : List Nat
  size : Nat := ks.length
  sorted: Bool := true
  hsort : sorted → List.Sorted (·<·) ks := by simp
  hsize : 0 < ks.length := by simp

namespace Rake

def zer : Rake := { d := 0, ks := [0] }
def nat : Rake := { d := 1, ks := [0] }
def ge2 : Rake := { d := 1, ks := [2] }

section « terms » -- generating output terms from the rake

def term (r: Rake) (n : Nat) : Nat :=
  let q := r.ks.length
  have : n%q < r.ks.length := Nat.mod_lt _ r.hsize
  aseq r.ks[n%q] r.d |>.term (n/q)

def terms (r: Rake) (n: Nat) : List Nat :=
  List.range n |>.map r.term

theorem term_simp (r:Rake) (n:Nat)
: (∃k, (r.term n = k + r.d * (n/r.ks.length)) ∧ ∃i: Fin r.ks.length, i=n%r.ks.length ∧ k=r.ks[i]) := by
  let i: Fin r.ks.length := ⟨n%r.ks.length, Nat.mod_lt n r.hsize⟩
  use r.ks[i]
  apply And.intro
  · dsimp[term, aseq, ASeq.term, i]
  · use i

theorem term_iff (r:Rake)
  : ∀m, (∃n, r.term n = m) ↔ (∃ k∈r.ks,  ∃x:Nat, k+x*r.d = m) := by
  intro m; apply Iff.intro
  · show (∃ n, r.term n = m) → ∃ k ∈ r.ks, ∃ x, k + x * r.d = m
    -- this is just grunt work, but it follows from the definition of term
    intro ⟨n,hn⟩; obtain ⟨k, hk₀, hk₁, hk₂, hk₃⟩ := r.term_simp n
    use k; apply And.intro
    · simp_all[List.mem_iff_get];
    · use (n/r.ks.length); subst hk₃ hn; simp_all;
      exact Nat.mul_comm (n / r.ks.length) r.d

  . show (∃ k ∈ r.ks, ∃ x, k + x * r.d = m) → ∃ n, r.term n = m
    -- in other words, given some k in our list and an arbitrary x
    -- the rake ought to produce m = k + x * r.d at some point. we prove
    -- this by working backwards to calculate what n we have to plug
    -- into (r.term n) in order to get n back out.
    intro ⟨k, hk, hx₀⟩

    -- k is a member of ks so it must have an index in ks: k=r.ks.get i
    rw[List.mem_iff_get] at hk
    obtain ⟨i: Fin r.ks.length, hi₀ : r.ks.get i = k⟩ := hk

    -- k uniquely identifies a particular arithmetic sequence within
    -- the rake, and there's some x that we can feed into this sequence
    -- to get the result m. we can obtain it:
    obtain ⟨x, hx: k + x * r.d = m⟩ := hx₀

    -- now we can choose n so that r.term n picks k=ks[ i ] as the constant.
    -- this happens ∀ n, i = n % r.ks.length ∧ x = n / r.ks.length
    have hi₁: i.val % r.ks.length = i := by exact Nat.mod_eq_of_lt i.prop
    let n := (i.val % r.ks.length) + (x * r.ks.length)

    -- now we run this definition of `n` through `r.term n` and
    -- once we deal with annoying divmod issues, out comes the result.
    use n; unfold_let; dsimp[term, aseq, ASeq.term]; simp_all[hi₁]
    rw[Nat.add_mul_div_right i.val x r.hsize, ←hi₁, Nat.mul_comm]
    simp; exact hx

end « terms »

section « sequences » -- arithmetic sequences for each k ∈ ks

def seq (r:Rake) (n:Nat) {hn:n<r.ks.length} : ASeq :=
  aseq (r.ks[n]'hn) r.d

def seqs (r: Rake) : List ASeq :=
  r.ks.map (λ k => aseq k r.d)

/-- proof that if a rake produces a term, it's because one of the sequences
    it contains produces that term. -/

theorem unused__ex_seq (r: Rake)
  : (r.term m = n) → (∃k ∈ r.ks, n = k + r.d * (m/r.ks.length)) := by
  unfold term; intro hmn; simp_all
  let q := r.ks.length
  have hmq: m%q < r.ks.length := Nat.mod_lt _ r.hsize
  let k := r.ks[m%q]; use k
  apply And.intro
  · show k ∈ r.ks
    exact List.get_mem r.ks (m % q) hmq
  · show n = k + r.d * (m/q)
    calc
      n = (aseq r.ks[m%q] r.d).term (m/q) := by simp[hmn]
      _ = (aseq k r.d).term (m/q) := by rfl
      _ = k + r.d * (m/q) := by unfold aseq ASeq.term; simp_all

end « sequences »

section « sort and dedup »

def sort_nodup (xs:List Nat) (hxs₀ : List.Nodup xs)
: { xs':List Nat // List.Sorted (·<·) xs' ∧ xs'.length = xs.length } :=
  let xs' := xs.mergeSort (·≤·)
  have hnodup : xs'.Nodup := xs.perm_mergeSort (·≤·) |>.nodup_iff |>.mpr hxs₀
  have hsorted: List.Sorted (·≤·) xs' := List.sorted_mergeSort (·≤·) xs
  have hlength := by simp_all only [List.length_mergeSort, xs']
  ⟨xs', And.intro (List.Sorted.lt_of_le hsorted hnodup) hlength⟩

def sort (r: Rake) : {r':Rake // r'.sorted } :=
  if h: r.sorted then ⟨r, h⟩
  else
    let ks₀ := r.ks
    let ks₁ := ks₀.dedup
    let ks₂ := sort_nodup ks₁ ks₀.nodup_dedup
  have hlen₁ : ks₁.length ≠ 0 := by have:=r.hsize; aesop
  have hsize := Nat.lt_of_lt_of_eq (Nat.zero_lt_of_ne_zero hlen₁) ks₂.prop.right.symm
  ⟨{ d:=r.d, ks:=ks₂, hsort:=λ_=>ks₂.prop.left, hsize := hsize}, rfl⟩

lemma length_pos_of_dedup {l:List Nat} (hlen: 0 < l.length) : 0 < l.dedup.length := by
  obtain ⟨hd, tl, hcons⟩ := List.exists_cons_of_length_pos hlen
  have : hd ∈ l := by rw[hcons]; exact List.mem_cons_self hd tl
  rw[←List.mem_dedup] at this
  exact List.length_pos_of_mem this

def zero_le_cases (n:Nat) (zeq: 0=n → P) (zlt: 0<n → P) : P :=
  if h:0=n then zeq h else zlt <| Nat.zero_lt_of_ne_zero λa=>h a.symm

lemma sorted_get (xs:List Nat) (hxs: List.Sorted (·<·) xs) (i j:Fin xs.length) (hij: i<j)
  : (xs[i] < xs[j]) := by
  conv at hxs => dsimp[List.Sorted]; rw[List.pairwise_iff_get]
  simp_all

/--
As currently defined, the terms of a sorted rake can be non-ascending in one of two ways:
- ascending sawtooth pattern if ∃k∈r.ks, k>r.d
- cyclic (and possibly constant) if r.d=0
But in all cases, if the rake is sorted, term 0 is the minimum. -/
theorem sorted_min_term_zero (r: Rake) (hr: r.sorted) : ∀ n, (r.term 0 ≤ r.term n) := by
  intro n
  obtain ⟨k₀, hk₀, i₀, hi₀⟩ := r.term_simp 0
  obtain ⟨k₁, hk₁, i₁, hi₁⟩ := r.term_simp n
  simp[hk₀, hk₁]
  suffices k₀ ≤ k₁ by exact le_add_right this
  rw[hi₀.right, hi₁.right]
  apply zero_le_cases i₁.val; all_goals intro hi
  case zeq => simp_all
  case zlt =>
    have : i₀.val < i₁.val := by aesop
    exact Nat.le_of_succ_le <| sorted_get r.ks (r.hsort hr) i₀ i₁ this

theorem sort_term_iff_term  (r:Rake) (n:Nat)
  : (∃m, r.term m = n) ↔ (∃m', r.sort.val.term m' = n) := by
  sorry

end « sort and dedup »

section « rake operations »

section « partition »
/--
Partition each sequence in the rake by partitioning their *inputs*
into equivalance classes mod n. This multiplies the number of sequences
by n. We can't allow n to be zero because then we'd have no sequences left,
and this would break the guarantee that term (n) < term n+1. -/
def partition (r: Rake) (n: Nat) (hn: 0 < n): Rake :=
  let seqs' := r.seqs.map (λ s => s.partition n) |>.join
  let ks₀ := seqs'.map (λ s => s.k)
  -- aseq.partiton n  always produces a list of length n
  have hsize := by
    have hlen₀: 0 < seqs'.length := by
      unfold_let; rw[List.length_join']; simp
      have : (List.length ∘ λs:ASeq=> s.partition n) = λ_ => n := by
        calc (List.length ∘ λ s => s.partition n)
          _ = λs:ASeq => (s.partition n).length := by rfl
          _ = λ_:ASeq => n := by conv=> lhs; simp[ASeq.length_partition]
      have : 0 < r.seqs.length := by unfold seqs; simp[List.length_map, r.hsize]
      simp_all -- this introduces "replicate" because the lengths are all the same.
      show 0 < Nat.sum (List.replicate r.seqs.length n)
      have sum_rep {x y: Nat} : Nat.sum (List.replicate x y) = x*y := by
        induction x; simp_all; case succ hx => simp[hx]; linarith
      simp_all
    have : ks₀.length = seqs'.length := List.length_map seqs' _
    aesop
  { d := r.d * n, ks := ks₀, sorted := false, hsize := hsize }

end « partition »

section « rem (remove multiples) »

/-- remove all multiples of `n`. if `n=0`, `Rake.zer` is returned. -/
def rem (r : Rake) (n : Nat) : Rake :=
  if hn₀ : n = 0 then zer
  else
    have hn : 0 < n := Nat.zero_lt_of_ne_zero hn₀
    let gcd := r.d.gcd n
    have hz : 0 < (n/gcd) := Nat.div_gcd_pos_of_pos_right r.d hn
    let r' := if n∣r.d then r else r.partition (n/gcd) hz
    let ks := r'.ks |>.filter (λk => ¬n∣k)
    if hlen: ks.length = 0 then zer
    else { d := r'.d, ks:=ks, sorted := false, hsize := Nat.zero_lt_of_ne_zero hlen }

-- `RakeMap.rem` depends on the correctness of `Rake.rem`.
-- the following theorems provide this proof.

variable (r: Rake) (p n: Nat) {hp: 0<p}

theorem rem_drop -- rem drops multiples of p
  : p∣n → ¬(∃m, (r.rem p).term m = n) := by
  sorry

theorem rem_keep -- rem keeps non-multiples of p
  : ¬(p∣n) ∧ (∃pm, r.term pm = n) → (∃m, (r.rem p).term m = n) := by
  sorry

theorem rem_same -- rem introduces no new terms
  : (∃m, (r.rem p).term m = n) → (∃pm, r.term pm = n) := by
  sorry

end « rem (remove multiples) »

section « gte (greater than or equal to) »

def gte (r: Rake) (n: Nat) : Rake  :=
  let f : ℕ → ℕ := (λk => let s := aseq k r.d; (ASeq.gte s n).k)
  { d := r.d, ks := r.ks.map f, sorted := false,
    hsize := Nat.lt_of_lt_of_eq r.hsize (r.ks.length_map _).symm }

end « gte (greater than or equal to) »

end « rake operations »
