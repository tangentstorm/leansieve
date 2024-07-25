-- For the purposes of this library, a "Rake" is a sorted
-- list of arithmetic sequences that share the same delta.
-- A rake can be combined with a Prop to form a RakeMap,
-- to model a bejection between the natural numbers and a
-- subset of the natural numbers with a lower bound and
-- the multiples certain numbers removed.
import ASeq
import MathLib.Data.List.Sort
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Basic

structure Rake : Type where
  d     : Nat
  ks    : List Nat
  size : Nat := ks.length
  hsort : List.Sorted (·<·) ks
  hsize : 0 < ks.length

theorem Rake.nodup {r:Rake} : List.Nodup r.ks :=
  List.Sorted.nodup r.hsort

def sort_nodup (xs:List Nat) (hxs₀ : List.Nodup xs)
: { xs':List Nat // List.Sorted (·<·) xs' ∧ xs'.length = xs.length } :=
  let xs' := xs.mergeSort (·≤·)
  have hnodup : xs'.Nodup := xs.perm_mergeSort (·≤·) |>.nodup_iff |>.mpr hxs₀
  have hsorted: List.Sorted (·≤·) xs' := List.sorted_mergeSort (·≤·) xs
  have hlength := by simp_all only [List.length_mergeSort, xs']
  ⟨xs', And.intro (List.Sorted.lt_of_le hsorted hnodup) hlength⟩

def idr : Rake := {
  d := 1, ks := [0],
  hsort := by simp
  hsize := by simp }

def rake0 : Rake := {
  d := 0, ks := [0],
  hsort := by simp
  hsize := by simp }

def Rake.term (r: Rake) (n : Nat) : Nat :=
  let q := r.ks.length
  have : n%q < r.ks.length := Nat.mod_lt _ r.hsize
  aseq r.ks[n%q] r.d |>.term (n/q)

lemma length_pos_of_dedup {l:List Nat} (hlen: 0 < l.length) : 0 < l.dedup.length := by
  obtain ⟨hd, tl, hcons⟩ := List.exists_cons_of_length_pos hlen
  have : hd ∈ l := by rw[hcons]; exact List.mem_cons_self hd tl
  rw[←List.mem_dedup] at this
  exact List.length_pos_of_mem this

def Rake.gte (r: Rake) (n: Nat) : Rake :=
  let f : ℕ → ℕ := (λk => let s := aseq k r.d; (ASeq.gte s n).k)
  let ks₀ := r.ks.map f
  let ks₁ := ks₀.dedup
  let ks₂ := sort_nodup ks₁ ks₀.nodup_dedup
  have hsize : 0 < ks₂.val.length := by
    have h₀ : 0 < ks₀.length := Nat.lt_of_lt_of_eq r.hsize (r.ks.length_map _).symm
    have h₁ : 0 < ks₁.length := length_pos_of_dedup h₀
    have h₂: ks₂.val.length = ks₁.length := ks₁.length_mergeSort _
    exact Nat.lt_of_lt_of_eq h₁ h₂.symm
  { d := r.d, ks := ks₂
    hsort := ks₂.prop.left
    hsize := hsize }


def Rake.seq (r:Rake) (n:Nat) {hn:n<r.ks.length} : ASeq :=
  aseq (r.ks[n]'hn) r.d

def Rake.seqs (r: Rake) : List ASeq :=
  r.ks.map (λ k => aseq k r.d)

/--
Partition each sequence in the rake by partitioning their *inputs*
into equivalance classes mod n. This multiplies the number of sequences
by n. We can't allow n to be zero because then we'd have no sequences left,
and this would break the guarantee that term (n) < term n+1. -/
def Rake.partition (r: Rake) (n: Nat) (hn: 0 < n): Rake :=
  let seqs' := r.seqs.map (λ s => s.partition n) |>.join
  let ks₀ := seqs'.map (λ s => s.k)
  let ks₁ := ks₀.dedup
  let ks₂ := sort_nodup ks₁ ks₀.nodup_dedup
  have hsize : 0 < ks₂.val.length := by
    -- aseq.partiton n  always produces a list of length n
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
    -- dedup of a non-empty list produces a non-empty list
    have hlen₁: 0 < ks₁.length := by
      have : ks₀.length = seqs'.length := List.length_map seqs' _
      exact length_pos_of_dedup (Nat.lt_of_lt_of_eq hlen₀ this.symm)
    have : ks₁.length = ks₂.val.length := ks₂.prop.right.symm
    exact Nat.lt_of_lt_of_eq hlen₁ this
  { d := r.d * n, ks := ks₂
    hsort := ks₂.prop.left
    hsize := hsize }

def Rake.rem (r : Rake) (n : Nat) : Rake :=
  if hn₀ : n = 0 then r.gte 1
  else
    have hn : 0 < n := Nat.zero_lt_of_ne_zero hn₀
    let gcd := r.d.gcd n
    have hz : 0 < (n/gcd) := Nat.div_gcd_pos_of_pos_right r.d hn
    let r' := if n∣r.d then r else r.partition (n/gcd) hz
    let p := (λk => ¬n∣k)
    let ks₀ := r'.ks |>.filter p
    let ks₁ := ks₀.dedup
    if hlen₁: ks₁.length = 0 then rake0
    else let ks₂ := sort_nodup ks₁ ks₀.nodup_dedup
      { d := r'.d, ks:=ks₂
        hsort := ks₂.prop.left
        hsize := Nat.lt_of_lt_of_eq (Nat.zero_lt_of_ne_zero hlen₁) ks₂.prop.right.symm }

/-- proof that if a rake produces a term, it's because one of the sequences
    it contains produces that term. -/
lemma Rake.___unused______ex_seq (r: Rake)
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

theorem div_lt_of_lt_mod_eq {m n d:Nat} {hdpos: 0 < d} {hmn: m<n} : (m%d = n%d) → (m/d < n/d) := by
  intro hmod
  rw[←m.div_add_mod d, ←n.div_add_mod d, hmod, Nat.add_lt_add_iff_right] at hmn
  exact (Nat.mul_lt_mul_left hdpos).mp hmn

-- Example of a rake that is non-ascending.
def r10 : Rake := { d:=10, ks:=[1,21], hsort:=by simp, hsize:=by simp }
assert (List.range 4 |>.map r10.term) = [1, 21, 11, 31]

theorem Rake.ascending_terms (r:Rake) (hks: ∀k∈ r.ks, k<r.d) (hdpos: 0 < r.d) {m n : Nat} (hmn: m < n)
 : r.term m < r.term n := by
  unfold term aseq ASeq.term; simp
  set kl := r.ks.length
  set mq := m / kl; set mr := m % kl
  set nq := n / kl; set nr := n % kl
  have hmr : mr < kl := by dsimp[mr,kl]; exact Nat.mod_lt m r.hsize
  have hnr : nr < kl := by dsimp[nr,kl]; exact Nat.mod_lt n r.hsize
  show r.ks[mr]'hmr + r.d * mq < r.ks[nr]'hnr + r.d * nq
  by_cases hreq : mr = nr
  case pos =>
    -- two terms of the same sequence
    have : r.ks[mr]'hmr = r.ks[nr]'hnr := by simp_all
    simp[this, Nat.mul_lt_mul_left, hdpos]
    dsimp[mq, nq]
    have hklpos: 0 < kl := r.hsize
    dsimp[mr,nr] at hreq
    exact @div_lt_of_lt_mod_eq m n kl hklpos hmn hreq
  case neg =>
    -- mr≠nr means two different sequences.
    -- if mq = nq, we're just adding different coefficients
    -- if mq < nq, the sequences differ by at least a multiple of d
    -- !! does it matter that ks[i] can be > d ?
    have : mq ≤ nq := by dsimp[mq,nq];  sorry
    have : ∃k, mq + k = nq := by use nq-mq; omega
    obtain ⟨k,ksum⟩ := this
    rw[←ksum]
    conv => rhs; rhs; simp[Nat.mul_add, Nat.add_comm]
    conv => rhs; rw[←Nat.add_assoc]
    rw[add_lt_add_iff_right]
    have : r.ks[mr] < r.ks[nr] := by sorry -- consequence of r.hsort
    exact Nat.lt_add_right (r.d * k) this

lemma Rake.term_simp (r:Rake) (n:Nat)
: (∃k, (r.term n = k + r.d * (n/r.ks.length)) ∧ ∃i: Fin r.ks.length, i=n%r.ks.length ∧ k=r.ks[i]) := by
  let i: Fin r.ks.length := ⟨n%r.ks.length, Nat.mod_lt n r.hsize⟩
  use r.ks[i]
  apply And.intro
  · dsimp[term, aseq, ASeq.term, i]
  · use i

lemma sorted_indices (xs:List Nat) {hsort: List.Sorted (·<·) xs} (i j:Nat) (hij: i<j) (hj: j<xs.length)
  : (xs[i]'(by omega) < xs[j]'hj) := by
  conv at hsort => dsimp[List.Sorted]; rw[List.pairwise_iff_get]
  simp_all

def zero_le_cases (n:Nat) (zeq: 0=n → P) (zlt: 0<n → P) : P :=
  if h:0=n then zeq h else zlt <| Nat.zero_lt_of_ne_zero λa=>h a.symm

lemma sorted_get (xs:List Nat) (hxs: List.Sorted (·<·) xs) (i j:Fin xs.length) (hij: i<j)
  : (xs[i] < xs[j]) := by
  conv at hxs => dsimp[List.Sorted]; rw[List.pairwise_iff_get]
  simp_all

/--
As currently defined, the terms of a rake can be non-ascending in one of two ways:
- will have an ascending sawtooth pattern if ∃k∈r.ks, k>r.d
- will be cyclic (and possibly constant) if r.d=0
But in all cases, term 0 is the minimum. -/
theorem Rake.min_term_zero (r: Rake) : ∀ n, (r.term 0 ≤ r.term n) := by
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
    exact Nat.le_of_succ_le <| sorted_get r.ks r.hsort i₀ i₁ this

-- rakemap --------------------------------------------------------------------

structure RakeMap (pred: Nat → Prop) where
  rake : Rake
  hbij : ∀ n, pred n ↔ ∃ m, rake.term m = n

def RakeMap.pred {p:Nat → Prop} (_:RakeMap p) : Nat → Prop := p

/-- proof that idr.term provides a bijection from Nat → Nat
 (it happens to be an identity map, but this is not necessary for proofs) -/
def idrm : RakeMap (λ _ => True) := {
  rake := idr
  hbij := by intro n; simp[Rake.term, idr, aseq, ASeq.term]}

section gte_lemmas

  variable (rm: RakeMap prop) (p n: Nat)

  lemma RakeMap.gte_drop -- gte drops terms < p
    : n < p → ¬(∃m, (rm.rake.gte p).term m = n) := by
    sorry

  lemma RakeMap.gte_keep -- gte keeps terms ≥ p
    : n≥p ∧ (∃pm, rm.rake.term pm = n) → (∃m, (rm.rake.gte p).term m = n) := by
    sorry

  lemma RakeMap.gte_same -- gte introduces no new terms
    : (∃pm, (rm.rake.gte p).term pm = n) → (∃pm, rm.rake.term pm = n) := by
    sorry

end gte_lemmas

section rem_lemmas

  variable (rm: RakeMap prop) (p n: Nat) {hp: 0<p}

  lemma RakeMap.rem_drop -- rem drops multiples of p
    : p∣n → ¬(∃m, (rm.rake.rem p).term m = n) := by
    sorry

  lemma RakeMap.rem_keep -- rem keeps non-multiples of p
    : ¬(p∣n) ∧ (∃pm, rm.rake.term pm = n) → (∃m, (rm.rake.rem p).term m = n) := by
    sorry

  lemma RakeMap.rem_same -- rem introduces no new terms
    : (∃pm, (rm.rake.rem p).term pm = n) → (∃pm, rm.rake.term pm = n) := by
    sorry

end rem_lemmas


-- operations on RakeMap -------------------------------------------------------
-- these proofs are exactly the same except for the proposition

def RakeMap.gte (prev : RakeMap prop) (p: Nat)
  : RakeMap (λ n => prop n ∧ n ≥ p) :=
  let rake := prev.rake.gte p
  let proof := by
    intro n; symm
    let hm : Prop := (∃m, rake.term m = n)
    let hpm : Prop := (∃pm, prev.rake.term pm = n )
    have : prop n ↔ hpm := prev.hbij n
    have : n<p → ¬hm := gte_drop prev p n
    have : n≥p ∧ hpm → hm := gte_keep prev p n
    have : hm → hpm := gte_same prev p n
    by_cases n<p; all_goals aesop
  { rake := rake, hbij := proof }

def RakeMap.rem (prev : RakeMap prop) (p: Nat)
  : RakeMap (λ n => prop n ∧ ¬(p∣n)) :=
  let rake := prev.rake.rem p
  let proof := by
    intro n; symm
    let hm : Prop := (∃m, rake.term m = n)
    let hpm : Prop := (∃pm, prev.rake.term pm = n )
    have : prop n ↔ hpm := prev.hbij n
    have : p∣n → ¬hm := rem_drop prev p n
    have : ¬p∣n ∧ hpm → hm := rem_keep prev p n
    have : hm → hpm := rem_same prev p n
    by_cases p∣n; all_goals aesop
  { rake := rake, hbij := proof }
