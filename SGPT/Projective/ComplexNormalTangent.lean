import SGPT.Projective.ComplexNormalCoordinates
import SGPT.Projective.ComplexNormalTail
import SGPT.Projective.ComplexNormalDeterminant

/-! The ACTUAL original tangent map factors through the manufactured unitary and literal tail.
Blueprint: `complex-normal-wedge.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.ComplexNormalTangent

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending StronglyPositiveForms
open ComplexNormalForm ComplexNormalCoordinates ComplexNormalTail ComplexNormalDeterminant
open scoped InnerProductSpace

variable {m : ℕ}

/-- The ACTUAL square tangent factor, using only the original D and manufactured normal coordinates. -/
def tangentFactor (ℓ : ComplexModel (m + 1) →L[ℂ] ℂ) (hℓ : ℓ ≠ 0)
    (D : ComplexModel m →L[ℂ] ComplexModel (m + 1)) : ComplexModel m →L[ℂ] ComplexModel m :=
  (tailProjection m).comp
    ((normalCoordinates ℓ hℓ).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp D)

/-- The ORIGINAL actual conormal equation forces the literal transported first coordinate to vanish. -/
theorem transported_head_zero (ℓ : ComplexModel (m + 1) →L[ℂ] ℂ) (hℓ : ℓ ≠ 0)
    (D : ComplexModel m →L[ℂ] ComplexModel (m + 1)) (hD : ℓ.comp D = 0)
    (z : ComplexModel m) : (normalCoordinates ℓ hℓ).symm (D z) 0 = 0 := by
  have hz := congrArg (fun F : ComplexModel m →L[ℂ] ℂ => F z) hD
  change ℓ (D z) = 0 at hz
  have h := normalCoordinates_value ℓ hℓ ((normalCoordinates ℓ hℓ).symm (D z))
  rw [LinearIsometryEquiv.apply_symm_apply, hz] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hℓ))

/-- The SAME original tangent vector, with no supplied factorization certificate. -/
theorem tangentFactor_readback (ℓ : ComplexModel (m + 1) →L[ℂ] ℂ) (hℓ : ℓ ≠ 0)
    (D : ComplexModel m →L[ℂ] ComplexModel (m + 1)) (hD : ℓ.comp D = 0)
    (z : ComplexModel m) :
    normalCoordinates ℓ hℓ (tailInclusion m (tangentFactor ℓ hℓ D z)) = D z := by
  change normalCoordinates ℓ hℓ (tailInclusion m
    (tailProjection m ((normalCoordinates ℓ hℓ).symm (D z)))) = D z
  rw [tailInclusion_tailProjection_of_head_zero m _ (transported_head_zero ℓ hℓ D hD z)]
  exact LinearIsometryEquiv.apply_symm_apply _ _

/-- The ENTIRE actual original complex tangent map is the SAME manufactured unitary/tail composition. -/
theorem tangentFactor_comp (ℓ : ComplexModel (m + 1) →L[ℂ] ℂ) (hℓ : ℓ ≠ 0)
    (D : ComplexModel m →L[ℂ] ComplexModel (m + 1)) (hD : ℓ.comp D = 0) :
    D = (normalCoordinates ℓ hℓ).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((tailInclusion m).comp (tangentFactor ℓ hℓ D)) := by
  apply ContinuousLinearMap.ext
  intro z
  exact (tangentFactor_readback ℓ hℓ D hD z).symm

/-- The ACTUAL original tangent and square factor have exactly the SAME original complex Gram form. -/
theorem tangentFactor_inner (ℓ : ComplexModel (m + 1) →L[ℂ] ℂ) (hℓ : ℓ ≠ 0)
    (D : ComplexModel m →L[ℂ] ComplexModel (m + 1)) (hD : ℓ.comp D = 0)
    (x y : ComplexModel m) :
    ⟪D x, D y⟫_ℂ = ⟪tangentFactor ℓ hℓ D x, tangentFactor ℓ hℓ D y⟫_ℂ := by
  calc
    _ = ⟪normalCoordinates ℓ hℓ (tailInclusion m (tangentFactor ℓ hℓ D x)),
        normalCoordinates ℓ hℓ (tailInclusion m (tangentFactor ℓ hℓ D y))⟫_ℂ := by
      rw [tangentFactor_readback ℓ hℓ D hD x, tangentFactor_readback ℓ hℓ D hD y]
    _ = _ := (normalCoordinates ℓ hℓ).inner_map_map _ _
    _ = _ := tailInclusion_inner m _ _

/-- The actual original normal Jacobian is the POSITIVE real determinant of the SAME manufactured factor. -/
theorem tangentFactor_normDet (ℓ : ComplexModel (m + 1) →L[ℂ] ℂ) (hℓ : ℓ ≠ 0)
    (D : ComplexModel m →L[ℂ] ComplexModel (m + 1)) (hD : ℓ.comp D = 0) :
    (D.restrictScalars ℝ).toLinearMap.normDet = ((tangentFactor ℓ hℓ D).restrictScalars ℝ).det :=
  normDet_eq_real_det_of_complex_inner D (tangentFactor ℓ hℓ D) (tangentFactor_inner ℓ hℓ D hD)

/-- Pullback of EVERY actual original real form uses the literal SAME actual unitary/tail/tangent factor. -/
theorem tangentFactor_pullback {q : ℕ} (ℓ : ComplexModel (m + 1) →L[ℂ] ℂ) (hℓ : ℓ ≠ 0)
    (D : ComplexModel m →L[ℂ] ComplexModel (m + 1)) (hD : ℓ.comp D = 0)
    (η : RealForm (m + 1) q) :
    η.compContinuousLinearMap (D.restrictScalars ℝ) =
      ((η.compContinuousLinearMap
        ((normalCoordinates ℓ hℓ).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)).compContinuousLinearMap
          ((tailInclusion m).restrictScalars ℝ)).compContinuousLinearMap
            ((tangentFactor ℓ hℓ D).restrictScalars ℝ) := by
  ext v
  change η (fun i => D (v i)) = η (fun i =>
    normalCoordinates ℓ hℓ (tailInclusion m (tangentFactor ℓ hℓ D (v i))))
  apply congrArg η
  funext i
  exact (tangentFactor_readback ℓ hℓ D hD (v i)).symm

end SGPT.Projective.NumEq.CompleteIntersections.ComplexNormalTangent
