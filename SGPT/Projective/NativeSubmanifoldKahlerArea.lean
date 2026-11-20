import SGPT.Projective.NativeSubmanifoldArea
import SGPT.Foundations.Analysis.Pending.IntegrationCurrentChart

/-! The actual intrinsic Kähler-volume integral on the WHOLE native
submanifold patch equals its original ambient Hausdorff area reading.
Blueprint: `native-submanifold-kahler-area.tex`. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open IntegrationCurrent ClosedTopCurrents TopDegreeDensity

variable {n m : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {W : Set X} (hk : m + 1 ≤ n)
  (hW : ∀ x ∈ W, RegularAtDim (n := n) W x (m + 1)) [CompactSpace W]

/-- Actual intrinsic integral = actual ambient Hausdorff area on the SAME
native member patch. Every inverse, Jacobian and normalization is produced. -/
theorem exists_native_kahler_chart_area_reading :
    letI := SubmanifoldChartedSpace.chartedSpace hk hW
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW
    letI : MeasurableSpace W := borel W
    letI : BorelSpace W := ⟨rfl⟩
    let hι := SubmanifoldChartedSpace.contMDiff_val hk hW
    ∀ (κ : KahlerBackground (m + 1) W)
      (e : ComplexChart (m + 1) W) (a : ComplexChart n X),
      ∃ A : ComplexModel n → ComplexModel (m + 1),
        ∀ (γ : SmoothRealForm n X (2 * (m + 1)))
          (K : Set (ComplexModel (m + 1))) (_hK : IsCompact K)
          (_hKU : K ⊆ coordinateDomain (Subtype.val : W → X) e a),
          ∫ x in e.val.symm '' K,
              topRatio κ.form.val (SmoothRealForm.pullback hι γ) x ∂(kahlerVolume κ) =
            ∫ y in coordinateMap (Subtype.val : W → X) e a '' K,
              topDensity ((SmoothRealForm.pullback hι γ).coeff e (A y)) /
                (fderiv ℝ (coordinateMap (Subtype.val : W → X) e a) (A y) :
                  ComplexModel (m + 1) →ₗ[ℝ] ComplexModel n).normDet
                ∂(μHE[2 * (m + 1)] : Measure (ComplexModel n)) := by
  let := SubmanifoldChartedSpace.chartedSpace hk hW
  have := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  let hι := SubmanifoldChartedSpace.contMDiff_val hk hW
  dsimp only
  intro κ e a
  obtain ⟨A, hA⟩ := exists_native_chart_area_reading hk hW e a
  refine ⟨A, fun γ K hK hKU => ?_⟩
  calc
    _ = ∫ z in K, topDensity ((SmoothRealForm.pullback hι γ).coeff e z) := by
      rw [setIntegral_kahlerVolume_image κ e hK.measurableSet (fun z hz => (hKU hz).1)
        (continuous_topRatio κ.isKahler.1 (SmoothRealForm.pullback hι γ))]
      apply setIntegral_congr_fun hK.measurableSet
      intro z hz
      have hzt := (hKU hz).1
      dsimp only
      erw [topRatio_eq_chartRatio κ.isKahler.1 (SmoothRealForm.pullback hι γ)
        (e.val.map_target hzt), e.val.right_inv hzt, chartRatio]
      change volDensity κ e z *
        (topDensity ((SmoothRealForm.pullback hι γ).coeff e z) / volDensity κ e z) = _
      exact mul_div_cancel₀ _ (volDensity_pos κ e hzt).ne'
    _ = _ := (hA γ K hK hKU).symm

end SGPT.Projective.NumEq.CompleteIntersections
