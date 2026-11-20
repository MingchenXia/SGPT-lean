import SGPT.Foundations.Analysis.Pending.ChartPartition
import SGPT.Foundations.Analysis.Pending.CompactAffineCurveRegions

set_option autoImplicit false

/-! # Actual smooth affine time tests on a curve chart -/

open Set
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.AffineCurveSmoothTests

open FirstPass CompactAffineCurveCharts CompactAffineCurveRegions ChartPartition

noncomputable section

/-- Actual extension by zero of the affine model test; the definition is total,
while smooth support transport below requires the genuine nonzero scale and fit. -/
def affineCurveTest {T : Type*} [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T]
    (e : ComplexChart 1 T) (z0 : ComplexModel 1) (δ : ℝ) (ψ : ℂ → ℝ) : T → ℝ :=
  chartExtend e (fun z => ψ (curveModelEquiv (δ⁻¹ • (z - z0))))

private theorem model_test_support (z0 : ComplexModel 1) {δ : ℝ} (hδ : δ ≠ 0)
    {ψ : ℂ → ℝ} (hψc : IsCompact (tsupport ψ)) :
    IsCompact (tsupport (fun z : ComplexModel 1 => ψ (curveModelEquiv (δ⁻¹ • (z - z0))))) ∧
      tsupport (fun z : ComplexModel 1 => ψ (curveModelEquiv (δ⁻¹ • (z - z0)))) ⊆
        (fun ζ => z0 + δ • curveModelEquiv.symm ζ) '' tsupport ψ := by
  let F : ℂ → ComplexModel 1 := fun ζ => z0 + δ • curveModelEquiv.symm ζ
  have hF : Continuous F := by fun_prop
  have hFc : IsCompact (F '' tsupport ψ) := hψc.image hF
  have hs : Function.support (fun z : ComplexModel 1 => ψ (curveModelEquiv (δ⁻¹ • (z - z0)))) ⊆
      F '' tsupport ψ := by
    intro z hz
    exact ⟨curveModelEquiv (δ⁻¹ • (z - z0)), subset_tsupport ψ hz,
      model_affine_right_inverse z0 z hδ⟩
  have hts := closure_minimal hs hFc.isClosed
  exact ⟨hFc.of_isClosed_subset isClosed_closure hts, hts⟩

variable {T : Type*} [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T]
  [IsComplexManifold 1 T]

/-- Actual compact support fitting, rather than a zero-extension certificate,
produces smoothness of the signed test in every actual curve chart. -/
theorem chartSmooth_affineCurveTest (e : ComplexChart 1 T) (z0 : ComplexModel 1)
    {δ : ℝ} (hδ : δ ≠ 0) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : IsCompact (tsupport ψ))
    (hfit : ∀ ζ ∈ tsupport ψ, z0 + δ • curveModelEquiv.symm ζ ∈ e.val.target) :
    ChartSmooth (n := 1) (affineCurveTest e z0 δ ψ) := by
  obtain ⟨hβc, hβsub⟩ := model_test_support z0 hδ hψc
  have hA : ContDiff ℝ ∞
      (fun z : ComplexModel 1 => curveModelEquiv (δ⁻¹ • (z - z0))) :=
    (curveModelEquiv.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp
      ((contDiff_id.sub contDiff_const).const_smul δ⁻¹)
  apply chartSmooth_chartExtend e (hψ.comp hA) hβc
  intro z hz
  obtain ⟨ζ, hζ, rfl⟩ := hβsub hz
  exact hfit ζ hζ

/-- The genuine model inverse identities and compact chart fit transport the
topological support inside the actual compact inverse-chart image. -/
theorem tsupport_affineCurveTest_subset (e : ComplexChart 1 T) (z0 : ComplexModel 1)
    {δ : ℝ} (hδ : δ ≠ 0) {ψ : ℂ → ℝ} (hψc : IsCompact (tsupport ψ))
    (hfit : ∀ ζ ∈ tsupport ψ, z0 + δ • curveModelEquiv.symm ζ ∈ e.val.target) :
    tsupport (affineCurveTest e z0 δ ψ) ⊆
      (fun ζ => e.val.symm (z0 + δ • curveModelEquiv.symm ζ)) '' tsupport ψ := by
  obtain ⟨-, hβsub⟩ := model_test_support z0 hδ hψc
  let F : ℂ → ComplexModel 1 := fun ζ => z0 + δ • curveModelEquiv.symm ζ
  have hF : Continuous F := by fun_prop
  have hKT : IsCompact ((fun ζ => e.val.symm (F ζ)) '' tsupport ψ) := by
    apply hψc.image_of_continuousOn
    simpa only [Function.comp_def] using e.val.symm.continuousOn.comp hF.continuousOn hfit
  apply (support_chartExtend_subset e).trans
  apply closure_minimal ?_ hKT.isClosed
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨ζ, hζ, rfl⟩ := hβsub hz
  exact ⟨ζ, hζ, rfl⟩

omit [IsComplexManifold 1 T] in
/-- The actual original test is recovered only on the genuinely fitted chart
image; no inverse-chart identity at an unfitted point is asserted. -/
theorem affineCurveTest_inverse_eq (e : ComplexChart 1 T) (z0 : ComplexModel 1)
    {δ : ℝ} (hδ : δ ≠ 0) (ψ : ℂ → ℝ) {ζ : ℂ}
    (hfit : z0 + δ • curveModelEquiv.symm ζ ∈ e.val.target) :
    affineCurveTest e z0 δ ψ (e.val.symm (z0 + δ • curveModelEquiv.symm ζ)) = ψ ζ := by
  change chartExtend e _ (e.val.symm (z0 + δ • curveModelEquiv.symm ζ)) = ψ ζ
  rw [chartExtend_of_mem (e.val.map_target hfit), e.val.right_inv hfit]
  rw [model_affine_left_inverse z0 hδ]

end

end SGPT.Foundations.Analysis.Pending.AffineCurveSmoothTests
