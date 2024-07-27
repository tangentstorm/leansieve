/-
This was originally used in RakeSieve to provide the condition
that the terms were all greater than or equal to 2. In the interest
of time, I have left it unverified and moved it to this file.
-/

import Rake

section gte_lemmas

  variable (rm: RakeMap prop) (p n: Nat)

  -- the gist of the argument I want to make here is that
  -- for each k (sequence), I just fast-forward it so that
  -- it skips over the discarded terms. we have these:
  -- theorem gte_term (s : ASeq) (n : Nat) : s.d > 0 → n ≤ term (s.gte n) 0
  -- theorem gte_same_delta (s : ASeq) (n : Nat) : (s.gte n).d = s.d
  -- lemma Rake.___unused______ex_seq (r: Rake) : (r.term m = n) → (∃k ∈ r.ks, n = k + r.d * (m/r.ks.length))
  -- we're /potentially/ modifying every single constant.
  -- we have to say for each sequence:
  --    - we drop only the terms we won't need
  --    - we keep all the terms we used to have
  --    - we don't add any new terms

  lemma RakeMap.gte_drop -- gte drops terms < p
    : n < p → ¬(∃m, (rm.rake.gte p).sort.val.term m = n) := by
    -- why is this true? because `gte` removes all `k∈ks, k < p` and replaces them
    -- with (d*x)+k... basically fast forwarding the sequence. but of course,
    -- this only works if d is positive.
    intro hnp; push_neg; intro m
    let ⟨r,hrs⟩  := (rm.rake.gte p).sort
    show r.term m ≠ n
    suffices p ≤ r.term 0 by have := Rake.sorted_min_term_zero r hrs m; omega
    obtain ⟨k,hk,i₀,hi₀⟩ := r.term_simp 0
    have : k ∈ r.ks := by
      have : i₀.val = 0 := by aesop
      have := List.get_mem r.ks i₀.val i₀.prop
      simp_all
    sorry

  lemma RakeMap.gte_keep -- gte keeps terms ≥ p
    : n≥p ∧ (∃pm, rm.rake.term pm = n) → (∃m, (rm.rake.gte p).sort.val.term m = n) := sorry
    -- why do I believe this?

  lemma RakeMap.gte_same -- gte introduces no new terms
    : (∃m, (rm.rake.gte p).sort.val.term m = n) → (∃pm, rm.rake.term pm = n) := by
    sorry

end gte_lemmas

-- this proof is basically the same as for Rake.rem. only the
-- lemmas above are different.
def RakeMap.gte (prev : RakeMap prop) (p: Nat)
  : RakeMap (λ n => prop n ∧ n ≥ p) :=
  let rake := (prev.rake.gte p).sort
  let proof := by
    intro n; symm
    let hm : Prop := (∃m, rake.val.term m = n)
    let hpm : Prop := (∃pm, prev.rake.term pm = n )
    have : prop n ↔ hpm := prev.hbij n
    have : n<p → ¬hm := gte_drop prev p n
    have : n≥p ∧ hpm → hm := gte_keep prev p n
    have : hm → hpm := gte_same prev p n
    by_cases n<p; all_goals aesop
  { rake := rake, hbij := proof }
