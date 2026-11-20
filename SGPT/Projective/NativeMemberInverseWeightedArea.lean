import SGPT.Projective.NativeMemberWeightedArea

/-! Retain the SAME actual native inverse through weighted intrinsic/area
comparison. Blueprint: `native-member-inverse-weighted-area.tex`. -/

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
open IntegrationCurrent ClosedTopCurrents TopDegreeDensity ProductTestForms

variable {n m : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {W : Set X} (hk : m + 1 ≤ n)
  (hW : ∀ x ∈ W, RegularAtDim (n := n) W x (m + 1)) [CompactSpace W]

/-- Actual chart-area equality for the SAME genuine native inverse.
Continuity and inverse laws are ordinary geometric data, not integral
certificates; the next producer manufactures them from the original charts. -/
theorem native_kahler_chart_area_same_inverse :
    letI := SubmanifoldChartedSpace.chartedSpace hk hW
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW
    letI : MeasurableSpace W := borel W
    letI : BorelSpace W := ⟨rfl⟩
    let hι := SubmanifoldChartedSpace.contMDiff_val hk hW
    ∀ (κ : KahlerBackground (m + 1) W)
      (e : ComplexChart (m + 1) W) (c : ComplexChart n X)
      (A : ComplexModel n → ComplexModel (m + 1))
      (_hA : ContinuousOn A (coordinateMap (Subtype.val : W → X) e c ''
        coordinateDomain (Subtype.val : W → X) e c))
      (_hAG : ∀ z ∈ coordinateDomain (Subtype.val : W → X) e c,
        A (coordinateMap (Subtype.val : W → X) e c z) = z)
      (γ : SmoothRealForm n X (2 * (m + 1)))
      (K : Set (ComplexModel (m + 1))) (_hK : IsCompact K)
      (_hKU : K ⊆ coordinateDomain (Subtype.val : W → X) e c),
      ∫ x in e.val.symm '' K, topRatio κ.form.val (SmoothRealForm.pullback hι γ) x
          ∂(kahlerVolume κ) =
        ∫ y in coordinateMap (Subtype.val : W → X) e c '' K,
          topDensity ((SmoothRealForm.pullback hι γ).coeff e (A y)) /
            (fderiv ℝ (coordinateMap (Subtype.val : W → X) e c) (A y) :
              ComplexModel (m + 1) →ₗ[ℝ] ComplexModel n).normDet
            ∂(μHE[2 * (m + 1)] : Measure (ComplexModel n)) := by
  let := SubmanifoldChartedSpace.chartedSpace hk hW
  have := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  let hι := SubmanifoldChartedSpace.contMDiff_val hk hW
  dsimp only
  intro κ e c A hA hAG γ K hK hKU
  have hr : ContinuousOn
      (fun z => topDensity ((SmoothRealForm.pullback hι γ).coeff e z))
      (coordinateDomain (Subtype.val : W → X) e c) :=
    (continuous_topDensity.comp_continuousOn
      ((SmoothRealForm.pullback hι γ).smooth e).continuousOn).mono (fun _ hz => hz.1)
  have harea := integral_image_density_div_normDet _ (coordinateDomain_isOpen hι e c)
    (coordinateMap_contDiffOn_real hι e c)
    (SubmanifoldKahlerRestriction.injective_fderiv_coordinateMap_val hk hW e c)
    A hA hAG (fun z => topDensity ((SmoothRealForm.pullback hι γ).coeff e z)) hr hK hKU
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
    _ = _ := harea.symm

/-- One actual inverse is chosen ONCE, proved genuine, and retained in the
SAME entire weighted whole-member Hausdorff area formula for every form. -/
theorem exists_native_member_weighted_area_with_inverse :
    letI := SubmanifoldChartedSpace.chartedSpace hk hW
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW
    letI : MeasurableSpace W := borel W
    letI : BorelSpace W := ⟨rfl⟩
    let hι := SubmanifoldChartedSpace.contMDiff_val hk hW
    ∀ (κ : KahlerBackground (m + 1) W)
      (e : ComplexChart (m + 1) W) (c : ComplexChart n X)
      (χ : X → ℝ) (hχ : ChartSmooth (n := n) χ)
      (_hχc : IsCompact (tsupport χ)) (_hχa : tsupport χ ⊆ c.val.source)
      (_hχe : ∀ y : W, y.1 ∈ tsupport χ → y ∈ e.val.source),
      ∃ A : ComplexModel n → ComplexModel (m + 1),
        (∀ z ∈ coordinateDomain (Subtype.val : W → X) e c,
          A (coordinateMap (Subtype.val : W → X) e c z) = z) ∧
        ∀ γ : SmoothRealForm n X (2 * (m + 1)),
          ∫ x : W, topRatio κ.form.val (SmoothRealForm.pullback hι (smulFun χ hχ γ)) x
              ∂(kahlerVolume κ) =
            ∫ y in c.val '' (W ∩ tsupport χ),
              topDensity ((SmoothRealForm.pullback hι (smulFun χ hχ γ)).coeff e (A y)) /
                (fderiv ℝ (coordinateMap (Subtype.val : W → X) e c) (A y) :
                  ComplexModel (m + 1) →ₗ[ℝ] ComplexModel n).normDet
                ∂(μHE[2 * (m + 1)] : Measure (ComplexModel n)) := by
  let := SubmanifoldChartedSpace.chartedSpace hk hW
  have := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  let hι := SubmanifoldChartedSpace.contMDiff_val hk hW
  dsimp only
  intro κ e c χ hχ hχc hχa hχe
  let P := e.val '' ((Subtype.val : W → X) ⁻¹' tsupport χ)
  obtain ⟨hPc, hPdomain, hPimage, hPinv⟩ :=
    native_member_compact_patch hk hW e c (tsupport χ) hχc hχa hχe
  obtain ⟨A, hA, hAG⟩ := exists_native_chart_inverse hk hW e c
  refine ⟨A, hAG, fun γ => ?_⟩
  have hzero : ∀ x : W, x ∉ e.val.symm '' P →
      topRatio κ.form.val (SmoothRealForm.pullback hι (smulFun χ hχ γ)) x = 0 := by
    intro x hx
    have hxχ : x.1 ∉ tsupport χ := by
      intro hxχ
      apply hx
      rw [hPinv]
      exact hxχ
    have hχ0 : χ x.1 = 0 := image_eq_zero_of_notMem_tsupport hxχ
    rw [pullback_smulFun hι, topRatio_smulFun, hχ0, zero_mul]
  calc
    _ = ∫ x in e.val.symm '' P,
        topRatio κ.form.val (SmoothRealForm.pullback hι (smulFun χ hχ γ)) x
          ∂(kahlerVolume κ) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ = ∫ y in coordinateMap (Subtype.val : W → X) e c '' P,
        topDensity ((SmoothRealForm.pullback hι (smulFun χ hχ γ)).coeff e (A y)) /
          (fderiv ℝ (coordinateMap (Subtype.val : W → X) e c) (A y) :
            ComplexModel (m + 1) →ₗ[ℝ] ComplexModel n).normDet
          ∂(μHE[2 * (m + 1)] : Measure (ComplexModel n)) :=
      native_kahler_chart_area_same_inverse hk hW κ e c A hA hAG (smulFun χ hχ γ)
        P hPc hPdomain
    _ = _ := by rw [hPimage]

end SGPT.Projective.NumEq.CompleteIntersections
