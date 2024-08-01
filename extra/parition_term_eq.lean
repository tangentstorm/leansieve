import Rake

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
