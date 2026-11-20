import SGPT.Projective.NativeSubmanifoldArea
import SGPT.Foundations.Analysis.Pending.ProductTestForms
import SGPT.Foundations.Analysis.Pending.ConstantFormProducts
import SGPT.Foundations.Analysis.FirstPass.CurrentPairing

/-! Exact actual weighted test/native pullback coefficient identity.
Blueprint: `native-member-test-pullback.tex`. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open ProductTestForms StronglyPositiveForms ConstantFormProducts
open _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {n k : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {W : Set X} (hk : k ≤ n) (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k)

/-- The SAME genuine weighted test, with only its actual complementary
degree cast undone, reads the SAME original inclusion pullback coefficient. -/
theorem native_weighted_test_pullback_coeff :
    letI := SubmanifoldChartedSpace.chartedSpace hk hW
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW
    let hι := SubmanifoldChartedSpace.contMDiff_val hk hW
    ∀ (e : ComplexChart k W) (c : ComplexChart n X)
      (χ : X → ℝ) (hχ : ChartSmooth (n := n) χ)
      (γ : SmoothRealForm n X (2 * k)) (q : ℕ) (h : 2 * k = q)
      (Ω : Opens (ComplexModel n)) (η : TestForm Ω q)
      (_hη : ∀ y, η y = c.val.target.indicator
        (fun z => χ (c.val.symm z) • (h ▸ γ : SmoothRealForm n X q).coeff c z) y)
      (z : ComplexModel k) (_hz : z ∈ coordinateDomain (Subtype.val : W → X) e c),
      (SmoothRealForm.pullback hι (smulFun χ hχ γ)).coeff e z =
        (castForm h.symm (η (coordinateMap (Subtype.val : W → X) e c z))).compContinuousLinearMap
          (fderiv ℝ (coordinateMap (Subtype.val : W → X) e c) z) := by
  let := SubmanifoldChartedSpace.chartedSpace hk hW
  have := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW
  let hι := SubmanifoldChartedSpace.contMDiff_val hk hW
  dsimp only
  intro e c χ hχ γ q h Ω η hη z hz
  have hcf : castForm h.symm (η (coordinateMap (Subtype.val : W → X) e c z)) =
      (smulFun χ hχ γ).coeff c (coordinateMap (Subtype.val : W → X) e c z) := by
    have hy := hη (coordinateMap (Subtype.val : W → X) e c z)
    rw [indicator_of_mem (coordinateMap_mem_target hz)] at hy
    subst q
    simpa only [castForm_self, smulFun_coeff] using hy
  exact (SmoothRealForm.pullback_coeff hι (smulFun χ hχ γ) e c hz).trans
    (congrArg (fun A => A.compContinuousLinearMap
      (fderiv ℝ (coordinateMap (Subtype.val : W → X) e c) z)) hcf.symm)

end SGPT.Projective.NumEq.CompleteIntersections
