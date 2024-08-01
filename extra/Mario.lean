import Mathlib.Data.Nat.Prime

-- def primes (n : Nat) : Array Nat := Id.run do
--   let mut res : Array Nat := #[]
--   let mut buf : Array Bool := .mkArray n true
--   for i in [2 : n] do
--     if buf[i]! then
--       res := res.push i
--       for j in [i * i : n : i] do
--         buf := buf.set! j false
--   return res

def primes (n : Nat) : Array Nat :=
  let rec loop1 (i : {i : Nat // i > 0})
      (buf : { arr : Array Bool // arr.size = n }) (res : Array Nat) : Array Nat :=
    if hi : i < n then
      if buf.1[i.1]'(by rw [buf.2]; exact hi) then
        let rec loop2 (j : Nat)
            (buf : { arr : Array Bool // arr.size = n }) : { arr : Array Bool // arr.size = n } :=
          if hj : j < n then
            loop2 (j + i) ⟨buf.1.set ⟨j, by rw [buf.2]; exact hj⟩ false, by simp [buf.2]⟩
          else
            buf
        termination_by n - j
        loop1 ⟨i+1, Nat.succ_pos _⟩ (loop2 (i * i) buf) (res.push i)
      else loop1 ⟨i+1, Nat.succ_pos _⟩ buf res
    else
      res
  termination_by n - i.1
  loop1 ⟨2, by decide⟩ ⟨.mkArray n true, by simp⟩ #[]

  lemma mem_primes_loop2 {n i hi buf buf' j} (m)
    (eq : primes.loop1.loop2 n ⟨i, hi⟩ j buf = buf')
    (j_eq : j = i * i + m * i)
    {k} (hk : k < n) :
      buf'.1[k]'(by rw [buf'.2]; exact hk) = true ↔
      buf.1[k]'(by rw [buf.2]; exact hk) = true ∧
      (j ≤ k → ∀ m, k ≠ i * i + m * i) := by
  rw [primes.loop1.loop2] at eq; split at eq <;> rename_i hj
  · rw [mem_primes_loop2 (j := j+i) (m+1) eq (by rw [j_eq, Nat.succ_mul, add_assoc]) hk]
    simp; rw [Array.get_set (hj := by rw [buf.2]; exact hk)]; split <;> rename_i jk <;> simp
    · cases show j = k from jk
      exact fun _ => ⟨le_rfl, _, j_eq⟩
    · refine fun _ => ⟨fun H h m' eq => ?_, fun H h => H ((Nat.le_add_right ..).trans h)⟩
      refine H ?_ _ eq
      have := lt_of_le_of_ne h jk
      subst eq j_eq
      rw [add_lt_add_iff_left] at this
      have := Nat.lt_of_mul_lt_mul_right this
      rw [add_assoc, add_le_add_iff_left, ← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ this
  · subst eq; simp [hk.trans_le (not_lt.1 hj)]
termination_by n - j

lemma mem_primes_loop1 {p n i hi buf res} (i2 : 2 ≤ i) (hi' : i ≤ max 2 n)
    (hres : p ∈ res.data ↔ p < i ∧ Nat.Prime p) (sz : buf.size = n)
    (hbuf : ∀ k (h : k < n), buf[k]'(sz ▸ h) = true ↔
      ∀ q < i, q.Prime → ∀ m, k ≠ q * q + m * q) :
    p ∈ primes.loop1 n ⟨i, hi⟩ ⟨buf, sz⟩ res ↔ p < n ∧ Nat.Prime p := by
  unfold primes.loop1; simp; split <;> rename_i h1
  · have : buf[i] = true ↔ i.Prime := by
      rw [hbuf _ h1]; constructor
      · refine fun h2 => Nat.prime_def_le_sqrt.2 ⟨i2, fun m m2 hm mi => ?_⟩
        let ⟨q, pq, qm⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt m2)
        have hq := Nat.le_sqrt.1 <| (Nat.le_of_dvd (Nat.le_of_lt m2) qm).trans hm
        obtain ⟨c, rfl⟩ := qm.trans mi
        have qc := (mul_le_mul_iff_of_pos_left pq.pos).1 hq
        apply h2 q (lt_mul_right pq.pos (pq.two_le.trans qc)) pq (c - q)
        rw [← add_mul, Nat.add_sub_cancel' qc, Nat.mul_comm]
      · intro pi q qi pq m eq
        exact qi.ne' <| (pi.dvd_iff_eq pq.ne_one).1 ⟨q+m, by rw [eq, ← add_mul, mul_comm]⟩
    split <;> rename_i pi <;> simp only [this] at pi
    · generalize eq : primes.loop1.loop2 .. = buf'
      refine mem_primes_loop1 (Nat.le_succ_of_le i2) (le_max_of_le_right h1)
        ?_ buf'.2 fun k hk => ?_
      · simp [hres, Nat.lt_succ_iff_lt_or_eq, or_and_right]
        exact or_congr_right (and_iff_left_iff_imp.2 (· ▸ pi)).symm
      · rw [mem_primes_loop2 0 eq (by simp) hk, hbuf _ hk]
        simp [Nat.lt_succ_iff_lt_or_eq, or_imp, forall_and, pi]
        exact fun _ => or_iff_not_imp_left.2 fun h2 m eq => h2 (eq ▸ Nat.le_add_right ..)
    · refine mem_primes_loop1 (Nat.le_succ_of_le i2) (le_max_of_le_right h1) ?_ sz fun k hk => ?_
      · rw [hres, Nat.lt_succ_iff_lt_or_eq]
        refine and_congr_left fun pp => (or_iff_left_of_imp fun h => ?_).symm
        subst i; contradiction
      · simp [hbuf _ hk, Nat.lt_succ_iff_lt_or_eq, or_imp, forall_and, pi]
  · have := le_antisymm hi' (max_le i2 (not_lt.1 h1)); subst this
    rw [Array.mem_def, hres, lt_max_iff]
    exact and_congr_left fun pp => or_iff_right pp.two_le.not_lt
termination_by n - i

theorem mem_primes (n : Nat) {p : Nat} : p ∈ primes n ↔ p < n ∧ p.Prime :=
  mem_primes_loop1 le_rfl (le_max_left ..)
    (by simp; exact fun p2 pp => pp.two_le.not_lt p2) _
    (fun k hk => by simp; exact fun _ p2 pp => (pp.two_le.not_lt p2).elim)
