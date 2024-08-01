import Batteries.Data.List.Lemmas

structure ARS (p: α → α → Prop) : Prop where
  hrefl : ∀ x:α, p x x

-- initial system only has the reflexive rules
def init : ARS (λa z:α=>a=z) := {hrefl:= by simp}

-- we can add new rules to it explicitly at the type level:
def ARS.rw (sys: ARS (p:α → α → Prop)) (x y:α) : ARS (λa z:α=> (a,z)=(x,y) ∨ p a z)
  := { hrefl:= (by intro a; right; exact sys.hrefl a)}

-- and we can talk about infinite sequences:
structure InfSeq (α:Type) (p:α → α → Prop) (sys:ARS p) (xs:List α) : Prop where
  -- hinf : ∀n:Nat, n<xs.length
  hpws : List.Pairwise p xs

-- here's a cons to an infinite sequence:
def InfSeq.cons (seq:InfSeq α p sys xs) (x:α)
    {hp': p' = λa z:α => (a=x ∧ z∈ xs) ∨ p a z}
  : InfSeq α p' sys' (x::xs) := {
    -- hinf := by intro n; exact Nat.lt_succ_of_lt (seq.hinf n)
    hpws := by
      rw[xs.pairwise_cons]
      have hxs₀ := seq.hpws
      simp_all
      have : ∀ {x y:α}, p x y → p' x y := by simp_all
      rw[hp'] at this
      exact List.Pairwise.imp this hxs₀}

-- example : ¬ InfSeq α p sys xs := fun nh ↦
--   Nat.lt_irrefl _ (nh.hinf xs.length)

#lint
