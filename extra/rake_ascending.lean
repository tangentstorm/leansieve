-- this was never actually true
-- it would be true if the sorted constants were all less than d
import Rake

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
