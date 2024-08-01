-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Code.20review.3A.20proof.20about.20Array.20map

#print Array.map

def FloatArray.map' (x : FloatArray) (f: Float->Float): FloatArray := ⟨ x.data.map f ⟩
def x : FloatArray := ⟨#[0.5, 0.324, 0.65345345]⟩
#eval x.map' (·+1)




@[specialize, inline]
def FloatArray.mapAux (A C:FloatArray) (f:Float→Float) (d:Nat) (hd:C.size+d=A.size)
  : FloatArray :=
    if h: d = 0 then C
    else
      let C' := C.push <| f (A[C.size])
      have : C'.size = C.size.succ := Array.size_push C.data _
      have : C'.size + (d-1) = A.size := by omega
      FloatArray.mapAux A C' f (d-1) this

@[inline]
def FloatArray.map (A:FloatArray) (f:Float→Float) : FloatArray :=
  let C := (FloatArray.mkEmpty A.size)
  have : C.size = 0 := by rfl
  A.mapAux C f A.size (by omega)

open FloatArray

theorem size_mapAux (A: FloatArray) (f: Float→Float) (d:Nat)
  : (C:FloatArray) → (hd:C.size+d=A.size) → (A.mapAux C f d hd).size = A.size := by
    induction d
    unfold mapAux
    case zero => simp
    case succ d' ih =>
      unfold mapAux
      simp_all

theorem size_map (A : FloatArray) (f: Float→Float)
  : A.size = (A.map f).size := by
    unfold FloatArray.map
    have : (mkEmpty A.size).size = 0 := by rfl
    have : (mkEmpty A.size).size + A.size = A.size := by omega
    have aux_eq := size_mapAux A f A.size (mkEmpty A.size) this
    rw [aux_eq]
