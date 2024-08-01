-- For the purposes of this library, a "Rake" is a sorted
-- list of arithmetic sequences that share the same delta.
import ASeq
import MathLib.Data.List.Sort
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Perm

structure Rake : Type where
  d     : Nat
  ks    : List Nat
  size : Nat := ks.length
  sorted: Bool := true
  hsort : sorted → List.Sorted (·<·) ks := by simp
  huniq : sorted → ks.Nodup := by simp
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
: { xs':List Nat // List.Sorted (·<·) xs' ∧ xs'.Perm xs
    ∧ xs.length = xs'.length ∧ xs'.Nodup } :=
  let xs' := xs.mergeSort (·≤·)
  have hnodup : xs'.Nodup := xs.perm_mergeSort (·≤·) |>.nodup_iff |>.mpr hxs₀
  have hsorted: List.Sorted (·≤·) xs' := List.sorted_mergeSort (·≤·) xs
  have hlength := by simp_all only [List.length_mergeSort, xs']
  have hperm : xs'.Perm xs := List.perm_mergeSort (·≤·) xs
  ⟨xs', And.intro (List.Sorted.lt_of_le hsorted hnodup)
    (And.intro hperm (And.intro hlength hnodup))⟩

def sort (r: Rake) : {r':Rake // r'.d=r.d ∧ r'.sorted ∧ r'.ks.Perm r.ks.dedup } :=
  if hs: r.sorted then
    have hp: r.ks.Perm r.ks.dedup := by
      have := r.huniq hs
      rw[←r.ks.dedup_eq_self] at this
      rw[this]
    ⟨r, And.intro rfl <| And.intro hs hp⟩
  else
    let ks₀ := r.ks
    let ks₁ := ks₀.dedup
    let ks₂ := sort_nodup ks₁ ks₀.nodup_dedup
  have ⟨hsort, hperm, hlength, hnodup⟩  := ks₂.prop
  have hlen₁ : ks₁.length ≠ 0 := by have:=r.hsize; aesop
  have hsize := Nat.lt_of_lt_of_eq (Nat.zero_lt_of_ne_zero hlen₁) hlength
  ⟨{ d:=r.d, ks:=ks₂, hsort:=λ_=>hsort, huniq:=λ_=>hnodup, hsize:=_}, (by aesop)⟩

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
  if h: r.sorted then unfold sort; aesop
  else
    let ⟨rs, ⟨hd, hsort, hperm⟩⟩ := r.sort; simp
    have : ∀k, k∈rs.ks ↔ k∈r.ks.dedup := fun k => List.Perm.mem_iff hperm
    have hmem : ∀k, k∈r.ks ↔ k∈rs.ks := by aesop
    apply Iff.intro
    all_goals
      intro h; rw[term_iff] at h; obtain ⟨k, hk₀, hk₁⟩ := h
      specialize hmem k
      rw[term_iff]
      use k
      apply And.intro
    · rwa[←hmem]
    · rwa[hd]
    · rwa[hmem]
    · rwa[←hd]

end « sort and dedup »

section « rake operations »

section « partition »
/--
Partition each sequence in the rake by partitioning their *inputs*
into equivalance classes mod n. This multiplies the number of sequences
by n. We can't allow n to be zero because then we'd have no sequences left,
and this would break the guarantee that term (n) < term n+1. -/
def partition₀ (r: Rake) (j: Nat) (hj: 0 < j): Rake :=
  let seqs' := r.seqs.map (λ s => s.partition j) |>.join
  let ks₀ := seqs'.map (λ s => s.k)
  -- aseq.partiton n  always produces a list of length n
  have hsize := by
    have hlen₀: 0 < seqs'.length := by
      unfold_let; rw[List.length_join']; simp
      have : (List.length ∘ λs:ASeq=> s.partition j) = λ_ => j := by
        calc (List.length ∘ λ s => s.partition j)
          _ = λs:ASeq => (s.partition j).length := by rfl
          _ = λ_:ASeq => j := by conv=> lhs; simp[ASeq.length_partition]
      have : 0 < r.seqs.length := by unfold seqs; simp[List.length_map, r.hsize]
      simp_all -- this introduces "replicate" because the lengths are all the same.
      show 0 < Nat.sum (List.replicate r.seqs.length j)
      have sum_rep {x y: Nat} : Nat.sum (List.replicate x y) = x*y := by
        induction x; simp_all; case succ hx => simp[hx]; linarith
      simp_all
    have : ks₀.length = seqs'.length := List.length_map seqs' _
    aesop
  { d := r.d * j, ks := ks₀, sorted := false, hsize := hsize }

lemma List.mod_length {α : Type} (l:List α) (i:Nat) (hl: 0 < l.length)
  : (i % l.length) < l.length := by exact Nat.mod_lt (↑i) hl

def partition (r:Rake) (j: Nat) (hj:0<j:=by simp): Rake :=
  let ks' := List.range (j*r.ks.length) |>.map λi =>
    r.ks[i%r.ks.length]'(List.mod_length r.ks i r.hsize) + (i/r.ks.length) * r.d
  have : ks'.length = j*r.ks.length := by simp[ks', r.hsize]
  have := r.hsize
  { d:= r.d*j, ks := ks', sorted:=false, hsize:=by aesop }

@[simp]
theorem length_partition (r:Rake) (j: Nat) (hj:0<j)
  : (r.partition j hj).ks.length = j * r.ks.length := by simp[partition]

theorem partition_ks (r:Rake) (j: Nat) (hj:0<j) (i) (h)
  : (r.partition j hj).ks[i] =
    r.ks[i%r.ks.length]'(List.mod_length r.ks i r.hsize) + (i/r.ks.length) * r.d
  := by simp[partition]

theorem partition_term_iff  (r:Rake) (j:Nat) (hj: 0 < j)
: ∀n, (∃m, (r.partition j hj).term m = n)  ↔ (∃m, r.term m = n) := by
  intro n; rw[term_iff]
  apply Iff.intro
  all_goals
    intro h
    obtain ⟨k, hk₀, hk₁⟩ := h
  · sorry -- eventually "use m"
  · sorry -- eventually specialize the hypothesis h using (??)
-- then translate each side into the ∃ k form, and show that i can express either side in terms of the other,
-- given the formula in partition_ks and the new delta (r'.d = r.d*j).

end « partition »

section « rem (remove multiples) »

variable (r: Rake) (j: Nat) (hj: 0<j)

/-- remove all multiples of `j`. -/
def rem : Rake :=
  -- !! I was going to have be a bit smarter in the general case but
  --    this makes no difference in RakeSieve because j is always prime
  -- let gcd := r.d.gcd j
  -- have hz : 0 < (j/gcd) := Nat.div_gcd_pos_of_pos_right r.d hj
  -- let r' := if j∣r.d then r else r.partition (j/gcd) hz
  let r' := r.partition j hj
  let ks := r'.ks.filter (λk => ¬j∣k)
  if hlen: ks.length = 0 then zer
  else { d := r'.d, ks:=ks, sorted := false, hsize := Nat.zero_lt_of_ne_zero hlen }

variable (r':Rake) (hr': r' = r.rem j hj)

lemma rem_def'
  : r'=zer
  ∨ (r'.d=r.d*j ∧ r'.ks=(r.partition j hj).ks.filter (λk => ¬j∣k) ∧ 0<r'.ks.length) := by
    simp[hr',rem,partition]; split <;> simp_all[Nat.zero_lt_of_ne_zero]

theorem rem_def  (h₁: ∃n, ¬j∣n ∧ ∃m, r.term m=n)
  : r'.d=r.d*j ∧ r'.ks=(r.partition j hj).ks.filter (λk => ¬j∣k) ∧ 0<r'.ks.length := by
  obtain hzer | ⟨hd', hks', hlen'⟩ := rem_def' r j hj r' hr'
  · -- show hzer case cannot happen thanks to h₁
    -- r produces terms that don't divide k, and r.partition produces the same terms.

    -- from h1 we can obtain a k∈r.k coprime to p
    obtain ⟨n, hn, hex⟩ := h₁
    obtain ⟨k, hk, x, hx⟩ := by rwa[←r.partition_term_iff j hj n, term_iff] at hex
    have hjk : ¬j ∣ k := by
      by_contra h
      have :  j ∣     r.d * j * x := by
        have := Nat.dvd_mul_right j (r.d*x); rwa[Nat.mul_left_comm,←Nat.mul_assoc] at this
      have :  j ∣ k + r.d * j * x := by exact (Nat.dvd_add_iff_right h).mp this
      have : ¬j ∣ k + r.d * j * x := by
        have : (r.partition j hj).d = r.d * j := by aesop
        rwa[←hx, this,Nat.mul_comm] at hn
      contradiction

    -- now show that k survives the filter operation:
    set r'k := (r.partition j hj).ks.filter (λk => ¬j∣k)
    have rk: k ∈ r'k := by simp[hk, r'k, hjk, List.mem_filter]

    -- k ≠ 0 because ¬p∣k and ∀n,n∣0
    have : k ≠ 0 := by by_contra h; have := Nat.dvd_zero j; rw[h] at hjk; contradiction
    -- but that contradicts the notion that r'=hzer
    have : k = 0 := by
      set rpk := (r.partition j hj).ks.filter (λk => ¬j∣k)
      have rk: k ∈ rpk := by simp[hk, hjk, rpk, List.mem_filter]
      have : ¬ rpk.length = 0 := by have := List.ne_nil_of_mem rk; rwa[List.length_eq_zero]
      have : r'.ks = rpk := by simp[rpk] at this; simp[hr', rem, this, rpk]
      have : r'.ks = [0] := by simp[hzer, zer]
      simp_all[List.mem_singleton]
    contradiction

  · -- the other case (non hzer) just passes right through
    exact ⟨hd', hks', hlen'⟩

theorem rem_drop  -- rem drops multiples of p
  : 0<n → j∣n → ¬(∃m, r'.term m = n) := by
  -- general idea:
  --   the only way term m = n is if ∃x, ∃k∈r.ks, k + x*d = n
  --   x would have to be be n/ks.length, but i'm not sure we need that fact
  --   term_iff supplies this fact.
  intro hnpos hpn; rw[term_iff]
  -- we will show no such k exists
  push_neg; intro k hk x
  set d' := r'.d
  -- either rem returns zer, or we can extract the formulas for d and ks
  obtain hzer | ⟨hd', hks', hlen'⟩ := rem_def' r j hj r' hr'
  · -- the r=zer case solves the whole issue because zer only ever returns zero
    subst hzer
    have : k = 0 := by simp[zer] at hk; exact hk
    have : d' = 0 := by simp[d',zer]
    simp_all; exact Nat.ne_of_lt hnpos
  · -- we only have to show ¬p∣k, because `p∣d` so `x*d` cancels out mod p
    suffices ¬j∣k from by
      by_contra h
      have h₀: j ∣ k + x * d' := by rwa[h.symm] at hpn
      have h₁: j ∣ x * d' := Dvd.dvd.mul_left (Dvd.intro_left r.d hd'.symm) x
      have : j ∣ k := (Nat.dvd_add_iff_left h₁).mpr h₀
      contradiction
    show ¬j∣k
    simp_all[List.mem_filter]

theorem rem_keep  -- rem keeps non-multiples of p
  : ¬j∣n → (∃m, r.term m = n) → (∃m', r'.term m' = n) := by
  -- this follows from partition_term_iff and the nature of filter
  intro hpn ht
  have ht' := ht
  -- r produces terms that don't divide k, and r.partition produces the same terms.
  rw[←r.partition_term_iff j hj n, term_iff] at ht'
  -- since r.partition produces n, we can show ¬p∣k for the corresponding k
  obtain ⟨k, hk, x, hx⟩ := ht'
  have hex : (∃n, ¬j∣n ∧ ∃m, r.term m = n) := by use n
  obtain ⟨hd', hks'⟩ := rem_def r j hj r' hr' hex
  -- !! this duplicates some work from rem_def' ... consolidate?
  have hpk : ¬ j ∣ k := by
    by_contra h
    have : j ∣  r.d * j * x := by
      have : j ∣  j * (r.d * x) := Nat.dvd_mul_right j _
      rwa[Nat.mul_left_comm,←Nat.mul_assoc] at this
    have :  j ∣ k + r.d * j * x := by exact (Nat.dvd_add_iff_right h).mp this
    have : ¬j ∣ k + r.d * j * x := by
      have : (r.partition j hj).d = r.d * j := by aesop
      rwa[←hx, this,Nat.mul_comm] at hpn
    contradiction
  have : k ∈ r'.ks := by simp[hk, hks', hpk, List.mem_filter]
  rw[term_iff]
  use k; aesop

theorem rem_same  -- rem introduces no new terms
  : (∃n, ¬j∣n ∧ ∃m, r.term m = n) → (∃m', r'.term m' = n) → (∃m, r.term m = n) := by
  -- this follows from partition_term_iff and the nature of filter.
  intro hex h; rw[term_iff] at h; obtain ⟨k, hk, x, hx⟩ := h
  obtain ⟨hd', hks'⟩ := rem_def r j hj r' hr' hex
  have := r.partition_term_iff j hj n
  rw[term_iff] at this; rw[←this]
  have : k ∈ (r.partition j hj).ks := by simp_all; exact List.mem_of_mem_filter hk
  use k; aesop

end « rem (remove multiples) »

section « gte (greater than or equal to) »

def gte (r: Rake) (n: Nat) : Rake  :=
  let f : ℕ → ℕ := (λk => let s := aseq k r.d; (ASeq.gte s n).k)
  { d := r.d, ks := r.ks.map f, sorted := false,
    hsize := Nat.lt_of_lt_of_eq r.hsize (r.ks.length_map _).symm }

end « gte (greater than or equal to) »

end « rake operations »
