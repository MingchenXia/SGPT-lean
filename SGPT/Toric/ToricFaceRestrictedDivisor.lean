import SGPT.Toric.ToricFaceQuotientFan

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The LITERAL original restricted divisor: its coefficient at a genuine
quotient-fan ray is D_ρ+⟨mσ,uρ⟩ for the internally produced original ray ρ.
The genuine quotient-fan independence theorem supplies coherence for every
original D; no nefness or desired restricted-divisor certificate is assumed. -/
def toricFaceRestrictedDivisor (D : ToricDivisor γ hs)
    (v : latticePolytopeVertices γ) (J : Set (Fin n)) (mσ : Fin n → ℤ) :
    ToricDivisor (toricFaceProjectedFamily (hs := hs) v J)
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J) :=
  fun ρ => D (toricFaceRayLift (hs := hs) v J ρ) +
    intPairing mσ (toricFaceRayLift (hs := hs) v J ρ).val

/-- The literal restricted coefficient read back in EVERY actual chart. -/
theorem toricFaceRestrictedDivisor_native (D : ToricDivisor γ hs)
    (v : latticePolytopeVertices γ) (J : Set (Fin n)) (mσ : Fin n → ℤ)
    (w : ToricNativeFaceVertex (hs := hs) v J) (k : Fin (toricFaceDimension J)) :
    toricFaceRestrictedDivisor D v J mσ
      (polytopeToricRay (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
        (toricFaceVertexEquiv (hs := hs) v J w) k) =
      D (polytopeToricRay γ hs w.val (toricFaceNativeFreeIndex v J w k)) +
        intPairing mσ (polytopeToricRayGenerator γ hs w.val (toricFaceNativeFreeIndex v J w k)) := by
  unfold toricFaceRestrictedDivisor
  rw [toricFaceRayLift_native]
  rfl

/-- The ACTUAL native Cartier datum of the actual restricted divisor is
the literal Mσ-coordinate image of the ORIGINAL frame character m_D(w)−mσ.
This proves its actual Cartier coherence for arbitrary original valid mσ. -/
theorem toricFaceRestrictedDivisor_cartier (D : ToricDivisor γ hs)
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (mσ : Fin n → ℤ) (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v '' J) mσ)
    (w : ToricNativeFaceVertex (hs := hs) v J) :
    toricCartierDatum (toricFaceRestrictedDivisor D v J mσ)
      (toricFaceVertexEquiv (hs := hs) v J w) =
      toricFaceCharacterCoordinates (hs := hs) v J
        (toricFaceRestrictedFrameCharacter D v J mσ hσ w) := by
  apply eq_of_intPairing_rayGenerator_eq (toricFaceVertexEquiv (hs := hs) v J w)
  intro k
  rw [toricCartierDatum_pairing, toricFaceNativeRay_pairing, toricFaceRestrictedDivisor_native]
  change -(_ + _) = intPairing (toricCartierDatum D w.val - mσ) _
  rw [intPairing_sub, toricCartierDatum_pairing]
  omega

/-- Literal target transition character is the Mσ-coordinate image of the
ORIGINAL source Cartier transition character. This is exactly the rational
frame transition of (χ^mσ s_D)|Y; mσ cancels from every overlap. -/
theorem toricFaceRestrictedDivisor_cartier_sub (D : ToricDivisor γ hs)
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (mσ : Fin n → ℤ) (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v '' J) mσ)
    (w w' : ToricNativeFaceVertex (hs := hs) v J) :
    toricCartierDatum (toricFaceRestrictedDivisor D v J mσ) (toricFaceVertexEquiv v J w) -
        toricCartierDatum (toricFaceRestrictedDivisor D v J mσ) (toricFaceVertexEquiv v J w') =
      toricFaceCharacterCoordinates (hs := hs) v J
        ⟨toricCartierDatum D w.val - toricCartierDatum D w'.val,
          sub_mem_toricStratumCharacterLattice_of_Cartier_data
            (isToricCartierDatumAlong_face_vertex D v J w)
            (isToricCartierDatumAlong_face_vertex D v J w')⟩ := by
  rw [toricFaceRestrictedDivisor_cartier D v J mσ hσ w,
    toricFaceRestrictedDivisor_cartier D v J mσ hσ w', ← map_sub]
  apply congrArg (toricFaceCharacterCoordinates (hs := hs) v J)
  apply Subtype.ext
  change (toricCartierDatum D w.val - mσ) - (toricCartierDatum D w'.val - mσ) = _
  exact sub_sub_sub_cancel_right _ _ _

end SGPT.Toric
