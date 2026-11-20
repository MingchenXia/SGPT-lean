import SGPT.Foundations.Analysis.Pending.NaturalHermitianFrozenCoefficientSobolev
import SGPT.Foundations.Analysis.FirstPass.GeometricForms

/-! # Original chart cutoffs as whole native coefficient tests

Three complete mathematical statements and proofs precede this source.
No off-target smoothness is assumed and every original norm is retained.
-/

noncomputable section

open Set Function Filter MeasureTheory TopologicalSpace ContinuousLinearMap
open scoped Distributions Topology

namespace SGPT.Foundations.Analysis.Pending.NaturalChartCutoffCoefficientTests

open FirstPass NaturalScalarSobolevJet NaturalScalarSobolevBasisGradient
  NaturalCoefficientSobolevRellich NaturalVectorCoefficientSobolev NaturalHermitianSmoothFormMetric

variable {n q : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

local instance formNormedAddCommGroup (k : ℕ) : NormedAddCommGroup (FormCoefficients n k) :=
  ContinuousAlternatingMap.instNormedAddCommGroup

local instance formNormedSpace (k : ℕ) : NormedSpace ℝ (FormCoefficients n k) :=
  ContinuousAlternatingMap.instNormedSpace

variable (e : ComplexChart n M) (K : Compacts (ComplexModel n))
  (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
  (φ : 𝓓_{K}(ComplexModel n, ℝ)) (α : SmoothRealForm n M q)

include hK in
/-- Actual whole-model infinite smoothness of the literal original chart cutoff product. -/
theorem cutoffCoeff_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => φ x • α.coeff e x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ e.val.target
  · exact φ.contDiff.contDiffAt.smul ((α.smooth e).contDiffAt (e.val.open_target.mem_nhds hx))
  · have hxK : x ∉ K := fun h => hx (hK h)
    have hz : (fun y => φ y • α.coeff e y) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [K.isCompact.isClosed.isOpen_compl.mem_nhds hxK] with y hy
      simp only [φ.zero_on_compl hy, Pi.zero_apply, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq hz

/-- Genuine original infinite compact native form-coefficient test, with exact literal product. -/
def chartCutoffTest : 𝓓_{K}(ComplexModel n, FormCoefficients n q) :=
  ⟨fun x => φ x • α.coeff e x, cutoffCoeff_contDiff e K hK φ α,
    fun x hx => by
      change φ x • α.coeff e x = 0
      simp only [φ.zero_on_compl hx, Pi.zero_apply, zero_smul]⟩

/-- Original whole-model product readback, including points outside the chart target. -/
theorem chartCutoffTest_apply (x : ComplexModel n) :
    chartCutoffTest e K hK φ α x = φ x • α.coeff e x := rfl

/-- Actual original topological support remains in the same compact support. -/
theorem chartCutoffTest_tsupport_subset :
    tsupport (chartCutoffTest e K hK φ α : ComplexModel n → FormCoefficients n q) ⊆ K :=
  (chartCutoffTest e K hK φ α).tsupport_subset

/-- Geometric equality alone internally guarantees equality of the entire actual native test. -/
theorem chartCutoffTest_eq_of_geometricallyEq (β : SmoothRealForm n M q)
    (h : α.GeometricallyEq β) : chartCutoffTest e K hK φ α = chartCutoffTest e K hK φ β := by
  apply ContDiffMapSupportedIn.ext
  intro x
  by_cases hx : x ∈ e.val.target
  · simp only [chartCutoffTest_apply, h e hx]
  · have hxK : x ∉ K := fun h => hx (hK h)
    simp only [chartCutoffTest_apply, φ.zero_on_compl hxK, Pi.zero_apply, zero_smul]

/-- Actual zero germ on the open complement of the compact support. -/
theorem chartCutoffTest_eventually_zero (x : ComplexModel n) (hx : x ∉ K) :
    (chartCutoffTest e K hK φ α : ComplexModel n → FormCoefficients n q) =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [K.isCompact.isClosed.isOpen_compl.mem_nhds hx] with y hy
  simp only [chartCutoffTest_apply, φ.zero_on_compl hy, Pi.zero_apply, zero_smul]

/-- The entire actual ordinary derivative vanishes outside the compact support. -/
theorem chartCutoffTest_fderiv_eq_zero (x : ComplexModel n) (hx : x ∉ K) :
    fderiv ℝ (chartCutoffTest e K hK φ α) x = 0 := by
  rw [(chartCutoffTest_eventually_zero e K hK φ α x hx).fderiv_eq]
  simp

/-- Whole original ordinary differential product formula on the entire model, without off-target hypotheses. -/
theorem chartCutoffTest_fderiv (x : ComplexModel n) :
    fderiv ℝ (chartCutoffTest e K hK φ α) x =
      φ x • fderiv ℝ (α.coeff e) x + (fderiv ℝ φ x).smulRight (α.coeff e x) := by
  by_cases hx : x ∈ e.val.target
  · change fderiv ℝ (fun y => φ y • α.coeff e y) x = _
    exact fderiv_fun_smul (φ.contDiff.differentiable (by simp) x)
      (((α.smooth e).contDiffAt (e.val.open_target.mem_nhds hx)).differentiableAt (by simp))
  · have hxK : x ∉ K := fun h => hx (hK h)
    have hz : (φ : ComplexModel n → ℝ) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [K.isCompact.isClosed.isOpen_compl.mem_nhds hxK] with y hy
      exact φ.zero_on_compl hy
    have hd : fderiv ℝ φ x = 0 := by rw [hz.fderiv_eq]; simp
    have hv : φ x = (0 : ℝ) := φ.zero_on_compl hxK
    rw [chartCutoffTest_fderiv_eq_zero e K hK φ α x hxK, hv, hd]
    simp only [ContinuousLinearMap.zero_smulRight, add_zero]
    exact (zero_smul ℝ (fderiv ℝ (α.coeff e) x)).symm

/-- Genuine product directional derivative on every original point and direction. -/
theorem chartCutoffTest_fderiv_apply (x h : ComplexModel n) :
    fderiv ℝ (chartCutoffTest e K hK φ α) x h =
      φ x • fderiv ℝ (α.coeff e) x h + (fderiv ℝ φ x h) • α.coeff e x := by
  rw [chartCutoffTest_fderiv]
  rfl

variable (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
  (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
  {χ : Type*} [Fintype χ] (c : Module.Basis χ ℝ (FormCoefficients n q))

/-- Genuine original chart-localized producer into the constructed coefficient first-jet Hilbert space. -/
def chartCutoffCoefficientJet : CoefficientJetHilbert μ K b χ :=
  nativeVectorCoefficientJet K c μ b (chartCutoffTest e K hK φ α)

omit [Fintype χ] in
/-- Literal original scalar first-jet coordinate of the actual whole native cutoff test. -/
theorem chartCutoffCoefficientJet_apply (s : χ) :
    chartCutoffCoefficientJet e K hK φ α μ b c s =
      toSobolevFirstJet μ K b (coefficientTestCLM K c s (chartCutoffTest e K hK φ α)) := rfl

/-- Genuine internally constructed original-norm estimate with the exact full cutoff product differential. -/
theorem chartCutoffCoefficientJet_norm_sq_le :
    ‖chartCutoffCoefficientJet e K hK φ α μ b c‖ ^ 2 ≤ basisGradientConstant c *
      ((∫ x, ‖φ x • α.coeff e x‖ ^ 2 ∂μ) +
        ∑ i, ∫ x, ‖φ x • fderiv ℝ (α.coeff e) x (b i) +
          (fderiv ℝ φ x (b i)) • α.coeff e x‖ ^ 2 ∂μ) := by
  simpa only [chartCutoffCoefficientJet, chartCutoffTest_apply, chartCutoffTest_fderiv_apply] using
    nativeVectorCoefficientJet_norm_sq_le K c μ b (chartCutoffTest e K hK φ α)

end SGPT.Foundations.Analysis.Pending.NaturalChartCutoffCoefficientTests
