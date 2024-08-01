
---------------------------
theorem div_eq_of_lt_mod_lt: m<n → (m%d < n%d) → (m/d = n/d) := by
  intro hmn hmod
  rw[←m.div_add_mod d, ←n.div_add_mod] at hmn



-- theorem nat_div_xx₂ (hmn: m < n) : (n/d ≤ m/d) ↔ (m/d = n/d) ∧ (m % d < n % d) := by
--   n/d ≤ m/d ↔ m/d = n/d ∧ m%d < n%d
--   m/d = n/d ↔ m/d = n/d ∧ m%d < n%d
--   m/d = n/d → m%d < n%d

theorem nat_div_xx₀ : m<n → (m/d < n/d) ≠ ((m/d=n/d) ∧ (m%d < n%d)) := by
  intro hmn
  set q₀ := m/d; set r₀ := m%d
  set q₁ := n/d; set r₁ := n%d
  have hdu₀ := @Nat.div_mod_unique n d r₀ q₀ hdpos
  have hdu₁ := @Nat.div_mod_unique n d r₁ q₁ hdpos
  by_cases h : q₀ < q₁
  case pos => intro hqq; aesop
  case neg =>
    simp[not_iff]
    apply Iff.intro
    case mpr => aesop
    case mp =>
      intro hqq
      simp_all
      apply And.intro
      · show q₀ = q₁
        have : r₀ < d := by exact Nat.mod_lt m hdpos
        have : r₁ < d := by exact Nat.mod_lt n hdpos
        simp_all
        sorry
      · show r₀ < r₁
        sorry

  -- by_cases h:m/d=n/d
  -- case pos =>
  --   simp_all
  --   sorry
  -- case neg =>
  --   simp_all
  --   by_contra
  --   set k := n -m; have hk: n = m + k := by omega
  --   have : n/d ≤ m/d := by omega
  --   have :




#print xor


-- Reference
------------------------------------------------------------------------
-- this is the cause of the trouble:
#print Nat.div_eq_of_lt          -- a < b → a / b = 0

#print Nat.div_mul_cancel        -- n ∣ m → m / n * n   = m
#print Nat.mod_add_div           -- m % k + k * (m / k) = m
#print Nat.mul_div_cancel        -- 0 < n → m * n / n   = m
#print Nat.mul_div_cancel'       -- n ∣ m → n * (m / n) = m
#print Nat.mul_div_cancel_left   -- 0 < n → n * m / n = m
#print Nat.mul_div_cancel_left'  -- a ∣ b → a * (b / a) = b
#print Nat.mod_eq_of_lt          -- a < b → a % b = a
#print Nat.mod_le                -- x % y ≤ x
#print Nat.mod_lt                -- y > 0 → x % y < y
#print Nat.mod_add_mod           -- (m % n + k) % n = (m + k) % n
#print Nat.div_le_div            -- a ≤ b → d ≤ c → d ≠ 0 → a / c ≤ b / d
#print Nat.div_le_self           -- n / k ≤ n
#print Nat.div_eq_of_lt_le       -- k * n ≤ m → m < k.succ * n → m / n = k
#print Nat.lt_of_div_lt_div      -- a / c < b / c → a < b
#print Nat.mul_le_of_le_div      -- x ≤ y / k → x * k ≤ y
#print Nat.add_div_le_add_div    -- a / c + b / c ≤ (a + b) / c
#print Nat.add_div_of_dvd_right  -- c ∣ a → (a + b) / c = a / c + b / c
#print Nat.div_mod_unique        -- 0 < b → (a / b = d ∧ a % b = c ↔ c + b * d = a ∧ c < b)
#print Nat.div_le_div_right      -- a ≤ b → a / c ≤ b / c
#print Nat.le_of_mod_lt          -- a % b < a → b ≤ a
#print Nat.add_mod_of_add_mod_lt -- a % c + b % c < c → (a + b) % c = a % c + b % c
#print Nat.div_add_mod           -- n * (m / n) + m % n = m
#print Nat.div_add_mod'          -- a / b * b + a % b = a
#print Nat.add_lt_add_iff_left   -- k + n < k + m ↔ n < m
-- but... this is just too hard

-- example (m n d : Nat) (hmn : m < n) (hmnd : m / d = n / d) : m % d < n % d := by
--   rwa [← m.div_add_mod d, ← n.div_add_mod d, hmnd, Nat.add_lt_add_iff_left] at hmn


  -- have : m/d ≤ n/d := by refine Nat.div_le_div_right ?h; omega
theorem nat_div_xx₁ : m<n → (m/d = n/d) → (m%d < n%d) := by
  intro hmn hdiv
  show m%d < n%d
  set k := n - m
  have hnk: n = m + k := by omega
  have : m/d = (m+k)/d := by rwa[hnk] at hdiv
  have : d*(m/d) = d*((m+k)/d) := by exact congrArg (HMul.hMul d) this
  have : d*(m/d) = m-m%d := @nat_div_mod m d
  simp[*]
  sorry

theorem xxy : k=m%d → d*(m+(d-k))/d = (m+1)/d := by
  intro hk
  have : k ≤ m := by simp[hk]; exact @Nat.mod_le m d
  have : k < d := by simp[hk]; exact @Nat.mod_lt m d hdpos
  let j := d-k
  have : j ≤ d := by omega
  have : (m+d)/d = (m+(j+k))/d := by omega
  simp_all
  have : m < d → k < m := by
    intro md; simp[hk]
    sorry --exact?

  have : d = m + k := by sorry -- exact?
  have : d*((m+k)/d) = (m+k)-(m+k)%d := by exact nat_div_mod
  aesop
  omega

  simp[hk]
  slim_check
  sorry


example :=
  let x := d*(m/d)
  calc x*x
    _ = (d*(m/d)) * (m-m%d) := by aesop
    _ = (d*(m/d)*m)  - (d*(m/d))*(m%d) := by exact Nat.mul_sub_left_distrib (d * (m / d)) m (m % d)

theorem xx1 : m/d = (m-k)/d → d*(k+m) = d*d := by intro md; sorry

#print Nat.mod_eq_of_lt
#print Nat.le_of_mod_lt
#print Nat.mod_le



    -- -- subst show m%d < (m+k)%d

    -- -- we want to argue that
    -- ---  m < n    n = m + k ,  0 < k
    -- ---  m  < m+k
    -- --- d*m < d*(m+k)
    -- --- d*m < d*m + d*k
    -- --  0 < d*k

    -- --- m-(m-m%d) < (m+k)-((m+k)%d))
    -- have : k < d := by sorry
    -- have : d*(m/d) = d*(n/d) := by aesop
    -- have : d*(m/d) = m-m%d := by simp
    -- have : d*(n/d) = m-m%d := by omega
    -- have : m-m%d = n-n%d := by aesop
    -- have : n = m+k := by omega
    -- have : d*(m/d) = d*((m+k)/d) := by simp_all
    -- have : d*(n/d) = (m+k)-(m+k)%d := by simp_all
    -- by_contra



    -- have : m < n := hmn
    -- have hmd₀:    m/d  =   (m-m%d)/d  := by exact Nat.div_eq_sub_mod_div
    -- have hmd₁: d*(m/d) =d*((m-m%d)/d) := by exact congrArg (HMul.hMul d) hmd₀


    -- /--
    --   m/d < n/d
    --   d*(m/d) < d*(n/d)

    -- -/
    -- have : d*(m/d) = d*(n/d) := by aesop
    -- have : m - m%d = n - n%d := by simpa[nat_div_mod]
    -- have : d*(m/d) = d*(n/d) := by aesop
    -- have := @nat_div_mod n d
    -- have hmd₀: m/d=(m-m%d)/d := by exact Nat.div_eq_sub_mod_div
    -- have hnd₀: n/d=(n-n%d)/d := by exact Nat.div_eq_sub_mod_div
    -- have hmd₁: d*(m/d)=d*((m-m%d)/d) := by exact congrArg (HMul.hMul d) hmd₀
    -- have : (m-m%d)/d = (n-n%d)/d := by aesop
    -- simp_all[nat_div_mod]
    -- have h1: d*((m-m%d)/d) = (m-m%d) := by
    --   have : d∣(m-m%d) := by exact Nat.dvd_sub_mod m
    --   exact Nat.mul_div_cancel' this
    -- have hnd: n/d=(n-n%d)/d := by exact Nat.div_eq_sub_mod_div
    -- have h2: d*((n-n%d)/d) = (n-n%d) := by
    --   have : d∣(n-n%d) := by exact Nat.dvd_sub_mod n
    --   exact Nat.mul_div_cancel' this
    -- have : d*(m/d) = m-m%d := by aesop
    -- have : d*(n/d) = n-n%d := by aesop
    -- simp_all
    -- omega
