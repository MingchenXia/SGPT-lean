import SGPT.Projective.ComplexNormalTangent

/-! The ACTUAL full complementary normal wedge equals the SAME original complex tangent area.
Blueprint: `complex-normal-wedge.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.ComplexNormalWedge

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending StronglyPositiveForms ConstantFormProducts TopDegreeDensity
open ComplexNormalForm ComplexNormalCoordinates ComplexNormalTail ComplexNormalDeterminant ComplexNormalTangent

/-- **The FULL original normalized normal wedge is the actual original tangent-area density**,
for every complementary real form, every complex dimension, and every actual complex tangent
map killed by the original nonzero conormal. No graph, area, factorization or orientation
certificate is an input; the actual unitary and square tangent factor are manufactured internally. -/
theorem normal_wedge_area {m : ℕ} (ℓ : ComplexModel (m + 1) →L[ℂ] ℂ) (hℓ : ℓ ≠ 0)
    (D : ComplexModel m →L[ℂ] ComplexModel (m + 1)) (hD : ℓ.comp D = 0)
    (η : RealForm (m + 1) (2 * m)) :
    (D.restrictScalars ℝ).toLinearMap.normDet *
        topDensity (wedgeTo (by omega : 2 + 2 * m = 2 * (m + 1)) (normalForm ℓ) η) =
      topDensity (η.compContinuousLinearMap (D.restrictScalars ℝ)) := by
  let U := normalCoordinates ℓ hℓ
  let UR : ComplexModel (m + 1) →L[ℝ] ComplexModel (m + 1) :=
    U.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  have hdet : LinearMap.det UR.toLinearMap = 1 := by
    change (U.toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ).det = 1
    exact unitary_real_det_eq_one U
  have hcov : topDensity (wedgeTo (by omega : 2 + 2 * m = 2 * (m + 1)) (normalForm ℓ) η) =
      topDensity ((η.compContinuousLinearMap UR).compContinuousLinearMap
        ((tailInclusion m).restrictScalars ℝ)) := by
    calc
      _ = topDensity ((wedgeTo (by omega : 2 + 2 * m = 2 * (m + 1))
          (normalForm ℓ) η).compContinuousLinearMap UR) := by
        rw [topDensity_compContinuousLinearMap, hdet, one_mul]
      _ = topDensity (wedgeTo (by omega : 2 + 2 * m = 2 * (m + 1))
          ((normalForm ℓ).compContinuousLinearMap UR) (η.compContinuousLinearMap UR)) := by
        rw [wedgeTo_compContinuousLinearMap]
      _ = topDensity (wedgeTo (by omega : 2 + 2 * m = 2 * (m + 1))
          (normalForm (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin (m + 1))))
          (η.compContinuousLinearMap UR)) := by
        rw [normalCoordinates_normalForm]
      _ = _ := normalForm_coordinate_wedge_tail m (η.compContinuousLinearMap UR)
  rw [tangentFactor_normDet ℓ hℓ D hD, hcov, tangentFactor_pullback ℓ hℓ D hD η,
    topDensity_compContinuousLinearMap]

end SGPT.Projective.NumEq.CompleteIntersections.ComplexNormalWedge
