import SGPT.Foundations.Analysis.Pending.NaturalChartTestGeometricExtension
import SGPT.Foundations.Analysis.Pending.CompactDifferentialOverlap
import SGPT.Foundations.Analysis.Pending.XiaoComplexDifferential

/-! # Actual zero extensions commute with the original full differentials

The five complete mathematical statements and ENTIRE proofs precede source.
Compact support proves a genuine whole coefficient zero germ at each chart
boundary; all operator identities retain the original normalizations.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalChartExtensionDifferentials

open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents StronglyPositiveForms
  NaturalSupportedChartFormExtension NaturalChartTestGeometricExtension
  CompactDifferentialTests XiaoComplexDifferential

variable {n q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Compact support yields the actual zero germ across every original overlap boundary. -/
theorem testExtension_coeff_eventually_zero (e f : ComplexChart n M)
    (η : TestForm (chartTarget e) q) {z : ComplexModel n}
    (hz : z ∈ f.val.target) (hx : f.val.symm z ∉ e.val.source) :
    (testExtension e η).coeff f =ᶠ[𝓝 z] fun _ => 0 := by
  let C : Set M := e.val.symm '' tsupport (η : ComplexModel n → RealForm n q)
  have hC : IsCompact C :=
    η.hasCompactSupport.image_of_continuousOn (e.val.symm.continuousOn.mono η.tsupport_subset)
  have hnC : f.val.symm z ∉ C := by
    rintro ⟨y, hy, hxy⟩
    apply hx
    rw [← hxy]
    exact e.val.map_target (η.tsupport_subset hy)
  have hcont : ContinuousAt f.val.symm z :=
    f.val.symm.continuousOn.continuousAt (f.val.open_target.mem_nhds hz)
  have hn : ∀ᶠ y in 𝓝 z, f.val.symm y ∉ C :=
    hcont.eventually (hC.isClosed.isOpen_compl.mem_nhds hnC)
  filter_upwards [hn] with y hy
  change transportedCoeff e f η y = 0
  by_cases ho : y ∈ (chartTransition f e).source
  · have hzero : η (chartTransition f e y) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro ha
      apply hy
      exact ⟨chartTransition f e y, ha, e.val.left_inv ho.2⟩
    simp only [transportedCoeff, indicator_of_mem ho, hzero]
    ext v
    rfl
  · exact indicator_of_notMem ho _

/-- Genuine exterior differentiation and the native full LF extension commute geometrically. -/
theorem exterior_testExtension_geometricallyEq (e : ComplexChart n M)
    (η : TestForm (chartTarget e) q) :
    (testExtension e η).exteriorDerivative.GeometricallyEq
      (testExtension e (exteriorTestCLM η)) := by
  intro f z hz
  by_cases hx : f.val.symm z ∈ e.val.source
  · have ho : z ∈ (chartTransition f e).source := ⟨hz, hx⟩
    have hy : chartTransition f e z ∈ e.val.target := e.val.map_source hx
    have heq : (testExtension e η).coeff e =ᶠ[𝓝 (chartTransition f e z)]
        (η : ComplexModel n → RealForm n q) := by
      filter_upwards [e.val.open_target.mem_nhds hy] with y hy'
      exact extend_coeff_self e η η.contDiff η.hasCompactSupport η.tsupport_subset hy'
    have hself : (testExtension e η).exteriorDerivative.coeff e (chartTransition f e z) =
        (testExtension e (exteriorTestCLM η)).coeff e (chartTransition f e z) := by
      have hread := extend_coeff_self e (exteriorTestCLM η) (exteriorTestCLM η).contDiff
        (exteriorTestCLM η).hasCompactSupport (exteriorTestCLM η).tsupport_subset hy
      change (testExtension e (exteriorTestCLM η)).coeff e (chartTransition f e z) =
        exteriorTestCLM η (chartTransition f e z) at hread
      rw [SmoothRealForm.exteriorDerivative_coeff, heq.extDeriv_eq, hread, exteriorTestCLM_apply]
    ext v
    rw [(testExtension e η).exteriorDerivative.compatible f e z ho,
      (testExtension e (exteriorTestCLM η)).compatible f e z ho, hself]
  · have heq := testExtension_coeff_eventually_zero e f η hz hx
    have hright : (testExtension e (exteriorTestCLM η)).coeff f z = 0 :=
      extend_coeff_eq_zero e f (exteriorTestCLM η) (exteriorTestCLM η).contDiff
        (exteriorTestCLM η).hasCompactSupport (exteriorTestCLM η).tsupport_subset hx
    rw [SmoothRealForm.exteriorDerivative_coeff, heq.extDeriv_eq, hright]
    exact _root_.SGPT.Foundations.Analysis.extDeriv_const_apply 0 z

/-- The exact original real scalar action commutes with actual native chart extension. -/
theorem smul_testExtension_geometricallyEq (e : ComplexChart n M)
    (η : TestForm (chartTarget e) q) (c : ℝ) :
    (c • testExtension e η).GeometricallyEq (testExtension e (c • η)) := by
  intro f z hz
  change c • transportedCoeff e f η z = transportedCoeff e f (c • η) z
  by_cases ho : z ∈ (chartTransition f e).source
  · simp only [transportedCoeff, indicator_of_mem ho]
    ext v
    rfl
  · simp only [transportedCoeff, indicator_of_notMem ho, smul_zero]

/-- Original holomorphic chart derivatives give the exact full complex twist commutation. -/
theorem twist_testExtension_geometricallyEq (e : ComplexChart n M)
    (η : TestForm (chartTarget e) q) :
    (complexTwist (testExtension e η)).GeometricallyEq
      (testExtension e (TestFunction.postcompCLM
        (ContinuousAlternatingMap.compContinuousLinearMapCLM (modelComplexStructure n)) η)) := by
  intro f z hz
  change (transportedCoeff e f η z).compContinuousLinearMap (modelComplexStructure n) =
    transportedCoeff e f (TestFunction.postcompCLM
      (ContinuousAlternatingMap.compContinuousLinearMapCLM (modelComplexStructure n)) η) z
  by_cases ho : z ∈ (chartTransition f e).source
  · simp only [transportedCoeff, indicator_of_mem ho]
    ext v
    change η (chartTransition f e z)
      (fun i => chartTransitionDerivative f e z (Complex.I • v i)) =
        η (chartTransition f e z) (fun i => Complex.I • chartTransitionDerivative f e z (v i))
    congr 1
    funext i
    exact chartTransitionDerivative_complex_smul f e z ho Complex.I (v i)
  · simp only [transportedCoeff, indicator_of_notMem ho]
    ext v
    rfl

/-- The actual two twists, derivative and exact scalar give the original normalized complex commutation. -/
theorem dc_testExtension_geometricallyEq (e : ComplexChart n M)
    (η : TestForm (chartTarget e) q) :
    (dc (testExtension e η)).GeometricallyEq (testExtension e (localDcTestCLM η)) := by
  let ηJ : TestForm (chartTarget e) q := TestFunction.postcompCLM
    (ContinuousAlternatingMap.compContinuousLinearMapCLM (modelComplexStructure n)) η
  let ηD : TestForm (chartTarget e) (q + 1) := exteriorTestCLM ηJ
  let ηJD : TestForm (chartTarget e) (q + 1) := TestFunction.postcompCLM
    (ContinuousAlternatingMap.compContinuousLinearMapCLM (modelComplexStructure n)) ηD
  have hj : (complexTwist (testExtension e η)).GeometricallyEq (testExtension e ηJ) :=
    twist_testExtension_geometricallyEq e η
  have hd : (complexTwist (testExtension e η)).exteriorDerivative.GeometricallyEq
      (testExtension e ηD) := hj.exteriorDerivative.trans (exterior_testExtension_geometricallyEq e ηJ)
  have ht : (complexTwist (complexTwist (testExtension e η)).exteriorDerivative).GeometricallyEq
      (complexTwist (testExtension e ηD)) := by
    intro f z hz
    simp only [complexTwist_coeff, hd f hz]
  have hall : (complexTwist (complexTwist (testExtension e η)).exteriorDerivative).GeometricallyEq
      (testExtension e ηJD) := ht.trans (twist_testExtension_geometricallyEq e ηD)
  let c : ℝ := (-1 : ℝ) ^ (q + 1) / (4 * Real.pi)
  have hs := smul_testExtension_geometricallyEq e ηJD c
  intro f z hz
  change c • (complexTwist (complexTwist (testExtension e η)).exteriorDerivative).coeff f z =
    (testExtension e (c • ηJD)).coeff f z
  rw [← hs f hz]
  change c • (complexTwist (complexTwist (testExtension e η)).exteriorDerivative).coeff f z =
    c • (testExtension e ηJD).coeff f z
  rw [hall f hz]

/-- The original positive second test differential and global second differential commute geometrically. -/
theorem ddc_testExtension_geometricallyEq (e : ComplexChart n M)
    (η : TestForm (chartTarget e) q) :
    (ddc (testExtension e η)).GeometricallyEq (testExtension e (localDdcTestCLM η)) :=
  (dc_testExtension_geometricallyEq e η).exteriorDerivative.trans
    (exterior_testExtension_geometricallyEq e (localDcTestCLM η))

end SGPT.Foundations.Analysis.Pending.NaturalChartExtensionDifferentials
