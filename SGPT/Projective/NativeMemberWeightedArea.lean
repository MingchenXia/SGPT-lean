import SGPT.Projective.NativeMemberCompactPatch

/-! Actual global weighted whole-member integration as its SAME original
Hausdorff patch reading. Blueprint: `native-member-weighted-area.tex`. -/

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
open IntegrationCurrent TopDegreeDensity ProductTestForms

/-- Literal scalar multiplication of the actual top-density ratio. -/
theorem topRatio_smulFun {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (w : SmoothRealForm n M 2) (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ)
    (γ : SmoothRealForm n M (2 * n)) (x : M) :
    topRatio w (smulFun χ hχ γ) x = χ x * topRatio w γ x := by
  unfold topRatio chartRatio
  rw [smulFun_coeff, topDensity_smul,
    (complexChartAt (n := n) x).val.left_inv (mem_complexChartAt_source x)]
  exact mul_div_assoc _ _ _

variable {n m : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {W : Set X} (hk : m + 1 ≤ n)
  (hW : ∀ x ∈ W, RegularAtDim (n := n) W x (m + 1)) [CompactSpace W]

/-- The integral over the WHOLE native member of an actual weighted
ambient form is its SAME original Hausdorff area reading on exactly the
whole-member support. The actual inverse/Jacobian is manufactured internally. -/
theorem exists_native_member_weighted_area :
    letI := SubmanifoldChartedSpace.chartedSpace hk hW
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW
    letI : MeasurableSpace W := borel W
    letI : BorelSpace W := ⟨rfl⟩
    let hι := SubmanifoldChartedSpace.contMDiff_val hk hW
    ∀ (κ : KahlerBackground (m + 1) W)
      (e : ComplexChart (m + 1) W) (a : ComplexChart n X)
      (χ : X → ℝ) (hχ : ChartSmooth (n := n) χ)
      (_hχc : IsCompact (tsupport χ)) (_hχa : tsupport χ ⊆ a.val.source)
      (_hχe : ∀ y : W, y.1 ∈ tsupport χ → y ∈ e.val.source),
      ∃ A : ComplexModel n → ComplexModel (m + 1),
        ∀ γ : SmoothRealForm n X (2 * (m + 1)),
          ∫ x : W, topRatio κ.form.val (SmoothRealForm.pullback hι (smulFun χ hχ γ)) x
              ∂(kahlerVolume κ) =
            ∫ y in a.val '' (W ∩ tsupport χ),
              topDensity ((SmoothRealForm.pullback hι (smulFun χ hχ γ)).coeff e (A y)) /
                (fderiv ℝ (coordinateMap (Subtype.val : W → X) e a) (A y) :
                  ComplexModel (m + 1) →ₗ[ℝ] ComplexModel n).normDet
                ∂(μHE[2 * (m + 1)] : Measure (ComplexModel n)) := by
  let := SubmanifoldChartedSpace.chartedSpace hk hW
  have := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  let hι := SubmanifoldChartedSpace.contMDiff_val hk hW
  dsimp only
  intro κ e a χ hχ hχc hχa hχe
  let P := e.val '' ((Subtype.val : W → X) ⁻¹' tsupport χ)
  obtain ⟨hPc, hPdomain, hPimage, hPinv⟩ :=
    native_member_compact_patch hk hW e a (tsupport χ) hχc hχa hχe
  obtain ⟨A, hA⟩ := exists_native_kahler_chart_area_reading hk hW κ e a
  refine ⟨A, fun γ => ?_⟩
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
    _ = ∫ y in coordinateMap (Subtype.val : W → X) e a '' P,
        topDensity ((SmoothRealForm.pullback hι (smulFun χ hχ γ)).coeff e (A y)) /
          (fderiv ℝ (coordinateMap (Subtype.val : W → X) e a) (A y) :
            ComplexModel (m + 1) →ₗ[ℝ] ComplexModel n).normDet
          ∂(μHE[2 * (m + 1)] : Measure (ComplexModel n)) :=
      hA (smulFun χ hχ γ) P hPc hPdomain
    _ = _ := by rw [hPimage]

end SGPT.Projective.NumEq.CompleteIntersections
