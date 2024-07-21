-- For the purposes of this library, a "Rake" is a sorted
-- list of arithmetic sequences that share the same delta.
-- A rake can be combined with a Prop to form a RakeMap,
-- to model a bejection between the natural numbers and a
-- subset of the natural numbers with a lower bound and
-- the multiples certain numbers removed.
import ASeq
import MathLib.Data.List.Sort

def DSeq (d : Nat) := { s : ASeq // s.d = d }
instance : Inhabited (DSeq d) := ⟨⟨ASeq.mk 0 d, rfl⟩⟩
instance : CoeFun (DSeq d) fun _ => Nat → Nat := ⟨λs => s.val⟩
-- the following are necessary so that we can sort the tines
-- within the rake at each step.
instance : LE (DSeq d) where le a b := a.val.k ≤ b.val.k
instance : IsTotal (DSeq d) (·≤·) := by
  apply IsTotal.mk; intro a b; cases a; cases b; apply Nat.le_total
instance : IsTrans (DSeq d) (·≤·) := by
  apply IsTrans.mk; intro a b c; cases a; cases b; cases c; apply Nat.le_trans

def dseq (k : Nat) (d : Nat) : DSeq d := ⟨ASeq.mk k d, rfl⟩

def DSeq.compose {d₀ d₁ : Nat} (s₀ : DSeq d₀) (s₁ : DSeq d₁) : DSeq (d₀*d₁) :=
  ⟨s₀.val.compose s₁.val, (by
    unfold ASeq.compose aseq; simp
    have := s₀.prop
    have := s₁.prop
    aesop)⟩

def DSeq.partition {d₀:Nat} (ds : DSeq d₀) (n:Nat) : List (DSeq (d₀*n)) :=
  List.range n |>.map λi => ds.compose (dseq i n)

@[simp] theorem DSeq.partition_length {d₀ n:Nat} {ds : DSeq d₀} : (ds.partition n).length = n := by
  unfold partition; simp[List.length_map]

@[simp] lemma sum_rep {x y: Nat} : Nat.sum (List.replicate x y) = x*y := by
  induction x; simp_all; case succ hx => simp[hx]; linarith

structure Rake where
  d : Nat
  seqs : List (DSeq d)
  ks := seqs.map λs => s.val.k
  hmono {i j : Nat} (hij: i<j) (hj: j<ks.length) : ks[i] < ks[j]
  hsort : List.Sorted (·≤·) seqs
  hsize : ks.length > 0
  hsize': seqs.length > 0 := sorry

def idr : Rake := { -- the identity rake (maps n -> n)
  d := 1, ks := [0], seqs := [dseq 0 1]
  hmono := sorry
  hsort := by simp,
  hsize := by simp }

def Rake.term (r : Rake) (n : Nat) : Nat :=
  let q := r.seqs.length
  have : n%q < r.seqs.length := Nat.mod_lt _ r.hsize'
  r.seqs[n%q] (n/q)

def Rake.gte (r : Rake) (n : Nat) : Rake :=
  let f := (λ s => ⟨ASeq.gte s.val n, (by
    have : s.val.d = r.d := s.property
    symm at this; simp[this]
    apply ASeq.gte_same_delta s.val n)⟩)
  let seqs' := r.seqs.map f |> List.mergeSort (·≤·)
  { d := r.d
    seqs := seqs'
    hmono := sorry
    hsort := List.sorted_mergeSort (·≤·) (List.map f r.seqs)
    hsize := sorry } -- (by simp[List.length_mergeSort]; exact r.hsize')}

/--
Partition each sequence in the rake by partitioning their *inputs*
into equivalance classes mod n. This multiplies the number of sequences
by n. We can't allow n to be zero because then we'd have no sequences left,
and this would break the guarantee that term (n) < term n+1. -/
def Rake.partition (r : Rake) (n: Nat) (hn: 0 < n) : Rake :=
  let seqs' := r.seqs.map (λ s=> s.partition n) |>.join
  have not_empty : seqs'.length > 0 := by
    simp[seqs']; conv =>
      rhs; simp[List.length_join']
      rhs; arg 1; rw [@Function.comp_def]; simp
    simp_all; exact r.hsize'
  { d := r.d * n
    hmono := sorry
    seqs := seqs' |>.mergeSort (·≤·)
    hsort := by apply List.sorted_mergeSort
    hsize := by simp[List.length_mergeSort]; exact not_empty }

def Rake.rem (r : Rake) (n : Nat) : Rake :=
  -- first make sure r and n are coprime.
  let gcd := r.d.gcd n
  have hz : 0 < (n/gcd) := sorry
  let r' := if n∣r.d then r else r.partition (n/gcd) hz
  let seqs' := r'.seqs |>.filter (λ s => ¬n∣s.val.k)  |>.mergeSort (·≤·)
  { d := r'.d
    ks := seqs'.map (λs=> s.val.k)
    hmono := sorry
    seqs := seqs'
    hsort := by apply List.sorted_mergeSort
    hsize := sorry} -- (by simp[List.length_mergeSort]; exact r.hsize)}

/-- proof that if a rake produces a term, it's because one of the sequences
    it contains produces that term. -/
lemma Rake.ex_seq (rake: Rake)
  : (rake.term m = n) → (∃seq ∈ rake.seqs, ∃m₁, seq m₁ = n) := by
  unfold term; intro hseq; simp_all
  let q := rake.seqs.length
  have : m%q < rake.seqs.length := Nat.mod_lt _ rake.hsize'
  let seq := rake.seqs[m%q]; use seq
  apply And.intro
  · show seq ∈ rake.seqs
    exact List.get_mem rake.seqs (m % q) this
  · show ∃ m₁, seq m₁ = n
    dsimp[seq,q]
    use m/rake.seqs.length


theorem Rake.min_term_zero (r: Rake)
  : (0 < n) → (r.term 0 < r.term n) := by
  intro hnpos
  have : 0 < r.seqs.length := sorry
  unfold term ASeq.term
  set q := r.seqs.length
  dsimp; unfold List.get; dsimp
  simp_all
  set t0 := r.term 0
  set tn := r.term n
  sorry


-- rakemap --------------------------------------------------------------------

structure RakeMap (pred: Nat → Prop) where
  rake : Rake
  hbij : ∀ n, pred n ↔ ∃ m, rake.term m = n

def RakeMap.pred {p:Nat → Prop} (_:RakeMap p) : Nat → Prop := p

/-- proof that idr.term provides a bijection from Nat → Nat
 (it happens to be an identity map, but this is not necessary for proofs) -/
def idrm : RakeMap (λ _ => True) := {
  rake := idr
  hbij := by intro n; simp[Rake.term, idr, dseq, ASeq.term]}

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

  variable (rm: RakeMap prop) (p n: Nat)

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
