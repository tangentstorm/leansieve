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

-- i had originally planned to approach it like this:
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

theorem partition_term_eq  (r:Rake) (j:Nat) (hj: 0 < j) (xhdpos:0 < r.d)
: ∀m, (r.partition j hj).term m = r.term m := by
  intro m

  simp[partition, term, List.get, aseq, ASeq.term]
  set i := m % r.ks.length
  set k := r.ks.get ⟨i,_⟩
  set c := r.ks.length
  have : 0 < c := r.hsize
  -- now use algebra to show equivalence of the unfolded definitions,
  -- while tap-dancing around the division and subtraction rules for Nat.
  show  k + m%(j*c)/c*r.d   + r.d*j*(m/(j*c)) = k + r.d*(m/c)
  calc  k + m%(j*c)/c*r.d   + r.d*j*(m/(j*c))
    _ = k +  r.d*(m%(j*c)/c) + r.d*j*(m/(j*c)) := by rw[Nat.mul_comm]
    _ = k + (r.d*(m%(j*c)/c) + r.d*(j*(m/(j*c)))) := by rw[Nat.add_assoc, Nat.mul_assoc]
    _ = k +  r.d*(m%(j*c)/c   +      j*(m/(j*c))) := by conv => lhs; rhs; rw[←Nat.mul_add]
  simp_all -- cancel out the k + rd  * (...) on each side
  left -- ignore the `∨ r.d = 0` case, and resume the calculation:
  show     m%(j*c)/c + j*(m/(j*c))= m/c
  calc  m%(j*c)/c + j*(m/(j*c))

--    _ = (m/c)%j   + j*(m/(j*c))  := by rw[Nat.mod_mul_left_div_self]
--    _ = (m/c)%j   + (j*m)/(j*c)  := by rw?
--    _ = (m/c)%j   +   (m/c)  := by rw[Nat.mul_div_mul_left m c hj]


--- i introduced this m-m% trying to cancel out the j, but i think it makes it unprovable
    _ = m%(j*c)/c + j*((m-m%(j*c))/(j*c)) := by conv => pattern m/(j*c); rw[Nat.div_eq_sub_mod_div]
    _ = m%(j*c)/c + c*(j*((m-m%(j*c))/(j*c)))/c := by aesop
    _ = m%(j*c)/c + ((c*j)*((m-m%(j*c))/(j*c)))/c := by rw [Nat.mul_assoc]
    _ = m%(j*c)/c + ((j*c)*((m-m%(j*c))/(j*c)))/c := by rw [Nat.mul_comm]
    _ = m%(j*c)/c   +   (m-m%(j*c))/c := by rw [Nat.mul_div_cancel' (Nat.dvd_sub_mod m)]
    _ = (m%(j*c)    +    (m-m%(j*c)))/c := by sorry
    -- ^ if i could prove this line i would be set, but i don't think it's possible

  have : 0<(j*c) := by aesop
  have : m%(j*c) ≤ m := by exact Nat.mod_le m (j * c)
  aesop

  -- ideas:
  -- try to break up the subtraction
    --       Nat.div_eq_sub_mod_div    : m / n = (m - m % n) / n
    --       Nat.mod_mul_left_div_self : m % (k * n) / n <= m / n % k
--    _ = (m/c)%j   +         (m-m%(j*c))/c  := by rw[Nat.mod_mul_left_div_self]
    --  x    %a   + a*(x / a % b)
    -- theorem Nat.mod_mul : x%(a*b)=x % a + a * (x / a % b)
    --_ = (m/c)%j   + j*((m%(j*c) + m)/(j*c)) := by omega

--  calc     m%(j*c)/c + j*(m/(j*c))
--    _ = c*(m%(j*c)/c + j*(m/(j*c)))/c := by rw[Nat.mul_div_right _ r.hsize]

     --exact Eq.symm (Nat.mul_div_right (m % (j * c) / c + j * (m / (j * c))) r.hsize)
    --              m*(n/(m*k)) => n/k
    --_ = m%(j*c)/c + m/c := by rw [Nat.mul_div_mul_left]
    -- _ = m%(j*c)/c + (j*m)/(j*c) :=
      -- Nat.mul_div_mul_left{m : Nat} (n : Nat) (k : Nat) (H : 0 < m) :
      --
--    _ = j * (m % (j * c)) /(j*c) + j * (m / (j * c)) := by rw[←Nat.mul_div_mul_left (m % (j*c)) c hj]
--    _ = j *((m % (j * c))/(j*c)) + j * (m / (j * c)) := by aesop
--    _ = j * ((m % (j * c)) /(j*c) + (m / (j * c))) := by aesop

end « partition »

section « rem (remove multiples) »

/-- remove all multiples of `n`. -/
def rem (r : Rake) (n : Nat) (hn: 0<n) : Rake :=
  -- !! I was going to have be a bit smarter in the general case but
  --    this makes no difference in RakeSieve because n is always prime
  -- let gcd := r.d.gcd n
  -- have hz : 0 < (n/gcd) := Nat.div_gcd_pos_of_pos_right r.d hn
  -- let r' := if n∣r.d then r else r.partition (n/gcd) hz
  let r' := r.partition n hn
  let ks := r'.ks.filter (λk => ¬n∣k)
  if hlen: ks.length = 0 then zer
  else { d := r'.d, ks:=ks, sorted := false, hsize := Nat.zero_lt_of_ne_zero hlen }

-- `RakeMap.rem` depends on the correctness of `Rake.rem`.
-- the following theorems provide this proof.

variable (r: Rake) (p n: Nat) (hp: 0<p)

lemma rem_def (r') (h: r' = r.rem p hp)
  : r'=zer ∨ (r'.d=r.d*p ∧ r'.ks=(r.partition p hp).ks.filter (λk => ¬p∣k)) := by
    simp[h,rem,partition]; split <;> simp_all

theorem rem_drop -- rem drops multiples of p
  : 0<n → p∣n → ¬(∃m, (r.rem p hp).term m = n) := by
  -- general idea:
  --   the only way term m = n is if ∃x, ∃k∈r.ks, k + x*d = n
  --   x would have to be be n/ks.length, but i'm not sure we need that fact
  --   term_iff supplies this fact.
  intro hnpos hpn; rw[term_iff]
  -- we will show no such k exists
  push_neg; intro k hk x
  set r' := r.rem p hp; set d' := r'.d
  -- either rem returns zer, or we can extract the formulas for d and ks
  obtain hzer | ⟨hd', hks'⟩ := rem_def r p hp r' rfl
  · -- the r=zer case solves the whole issue because zer only ever returns zero
    have : k = 0 := by simp_all[zer]
    have : d' = 0 := by simp[hzer,d',zer]
    simp_all; exact Nat.ne_of_lt hnpos
  · -- we only have to show ¬p∣k, because `p∣d` so `x*d` cancels out mod p
    suffices ¬p∣k from by
      by_contra h
      have h₀: p ∣ k + x * d' := by rwa[h.symm] at hpn
      have h₁: p ∣ x * d' := Dvd.dvd.mul_left (Dvd.intro_left r.d hd'.symm) x
      have : p ∣ k := (Nat.dvd_add_iff_left h₁).mpr h₀
      contradiction
    show ¬p∣k
    simp_all[List.mem_filter]

theorem rem_keep -- rem keeps non-multiples of p
  : ¬(p∣n) → (∃m, r.term m = n) → (∃m', (r.rem p hp).term m' = n) := by
  -- this should follow from partition_term_iff and the nature of filter
  intro hpn ht
  have ht' := ht
  -- r produces terms that don't divide k, and r.partition produces the same terms.
  rw[←r.partition_term_iff p hp n, term_iff] at ht'
  -- since r.partition produces n, we can show ¬p∣k for the corresponding k
  obtain ⟨k, hk, x, hx⟩ := ht'
  set r' := r.rem p hp
  have hpk : ¬ p ∣ k := by
    by_contra h
    have : p ∣  r.d * p * x := by
      have : p ∣  p * (r.d * x) := Nat.dvd_mul_right p _
      rwa[Nat.mul_left_comm,←Nat.mul_assoc] at this
    have :  p ∣ k + r.d * p * x := by exact (Nat.dvd_add_iff_right h).mp this
    have : ¬p ∣ k + r.d * p * x := by
      have : (r.partition p hp).d = r.d * p := by aesop
      rwa[←hx, this,Nat.mul_comm] at hpn
    contradiction
  obtain hzer | ⟨hp', hks'⟩ := rem_def r p hp r' rfl
  · -- the r'=zer case can't actually happen here, because ht:r.term m = n and hpn:¬p∣n.
    -- we can't really take advantage of a `0 < n` hypothesis here, because we have to
    -- make the argument *after* applying `rem`, and in this proof, that's the conclusion.
    have h₀: k ≠ 0 := by by_contra h; have := Nat.dvd_zero p; rw[h] at hpk; contradiction
    have h₁: k = 0 := by
      set rpk := (r.partition p hp).ks.filter (λk => ¬p∣k)
      have rk: k ∈ rpk := by simp[hk, hpk, rpk, List.mem_filter]
      have : ¬ rpk.length = 0 := by have := List.ne_nil_of_mem rk; rwa[List.length_eq_zero]
      have : r'.ks = rpk := by simp[rpk] at this; simp[r', rem, this, rpk]
      have : r'.ks = [0] := by simp[hzer, zer]
      simp_all[List.mem_singleton]
    contradiction
  · -- for the normal case,
    have : k ∈ r'.ks := by simp[hk, hks', hpk, List.mem_filter]
    rw[term_iff]
    use k; aesop

theorem rem_same -- rem introduces no new terms
  : 0<n → (∃m, (r.rem p hp).term m = n) → (∃pm, r.term pm = n) := by
  -- this follows from partition_term_iff and the nature of filter.
  intro hn h; rw[term_iff] at h; obtain ⟨k, hk, x, hx⟩ := h
  set r' := r.rem p hp
  obtain hzer | ⟨hp', hks'⟩ := rem_def r p hp r' rfl
  -- hn lets us ignore the hzer case, since it would lead to a contradiction
  · have : n = 0 := by simp_all[zer]
    have : n ≠ 0 := Nat.not_eq_zero_of_lt hn
    contradiction
  -- otherwise we can use the definition in hks' to show what we want
  · have := r.partition_term_iff p hp n
    rw[term_iff] at this; rw[←this]
    have : k ∈ (r.partition p hp).ks := by simp_all; exact List.mem_of_mem_filter hk
    use k; aesop

end « rem (remove multiples) »

section « gte (greater than or equal to) »

def gte (r: Rake) (n: Nat) : Rake  :=
  let f : ℕ → ℕ := (λk => let s := aseq k r.d; (ASeq.gte s n).k)
  { d := r.d, ks := r.ks.map f, sorted := false,
    hsize := Nat.lt_of_lt_of_eq r.hsize (r.ks.length_map _).symm }

end « gte (greater than or equal to) »

end « rake operations »
