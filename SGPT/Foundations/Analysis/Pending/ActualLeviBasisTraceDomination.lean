import SGPT.Foundations.Analysis.Pending.ActualDistributionalLeviBasisBound
import SGPT.Foundations.Analysis.Pending.ActualScalarCurrentKahlerTracePairing
import SGPT.Foundations.Analysis.Pending.LocalPositiveCurrentGluing
import SGPT.Foundations.Analysis.Pending.SmoothTestMeasureSeparation

set_option autoImplicit false

/-! # Actual complex-basis Levi measures dominate the complete local trace

Natural scalar Levi positivity and an actual complex basis internally produce
the regular basis measures and a finite positive full-trace domination scalar.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace Module
open scoped Topology Distributions ContDiff InnerProductSpace CompactlySupported
namespace SGPT.Foundations.Analysis.Pending.ActualLeviBasisTraceDomination
open FirstPass FirstPass.MongeAmpere LocalProductCurrents LocalBedfordTaylorProducts ScalarLeviPositiveCurrent
  LocalPositiveCurrentGluing ActualDistributionalLeviBasisBound
  ActualScalarCurrentKahlerTracePairing SmoothTestMeasureSeparation

variable {m : ℕ} {U : Opens (ComplexModel (m + 1))}

private theorem compact_test_integrable {n : ℕ} {A : Opens (ComplexModel n)}
    (μ : Measure A) [IsLocallyFiniteMeasure μ] (φ : 𝓓(A, ℝ)) :
    Integrable (fun x : A => φ x) μ := by
  let g : C_c(A, ℝ) := testFunctionToCompactlySupportedLM A φ
  exact (g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport).congr
    (Eventually.of_forall fun x => by simp [g])

/-- Genuine Levi positivity and an actual complex basis internally produce
regular directional measures and a positive domination of the full trace. -/
theorem exists_basis_measures_dominate_trace
    (T : 𝓓'(U, ℝ)) (hT : HasNonnegativeDistributionalLevi T)
    (b : Basis (Fin (m + 1)) ℂ (ComplexModel (m + 1))) :
    let hC := isPositive_ddc_scalarTopCurrent hT
    ∃ C : NNReal, 0 < C ∧ ∃ μ : Fin (m + 1) → Measure U,
      (∀ i, (μ i).Regular ∧ IsLocallyFiniteMeasure (μ i) ∧
        ∀ φ : 𝓓(U, ℝ), (∫ x : U, φ x ∂μ i) = distributionalLeviCLM (b i) T φ) ∧
      hC.traceMeasureOn ≤ C • ∑ i, μ i := by
  classical
  intro hC
  have hex (i : Fin (m + 1)) : ∃ μ : Measure U,
      μ.Regular ∧ IsLocallyFiniteMeasure μ ∧
        ∀ φ : 𝓓(U, ℝ), (∫ x : U, φ x ∂μ) = distributionalLeviCLM (b i) T φ :=
    (hT (b i)).exists_regular_measure
  choose μ hregular hlocal hrep using hex
  choose A hA hbound using fun j : Fin (m + 1) =>
    exists_pos_bound_from_complex_basis T hT b (coordinateVector j)
  let H : ℝ := 1 + ∑ j, A j
  have hH : 0 < H := by
    have hsum : 0 ≤ ∑ j, A j := Finset.sum_nonneg fun j _ => (hA j).le
    dsimp [H]
    linarith
  have hfactor : 0 < (m.factorial : ℝ) / Real.pi := by positivity
  let C : NNReal := ⟨(m.factorial : ℝ) / Real.pi * H, (mul_pos hfactor hH).le⟩
  let (i : Fin (m + 1)) : IsLocallyFiniteMeasure (μ i) := hlocal i
  let : IsLocallyFiniteMeasure (∑ i, μ i) :=
    Measure.isLocallyFiniteMeasure_finset_sum Finset.univ μ (fun i _ => hlocal i)
  let : IsLocallyFiniteMeasure hC.traceMeasureOn :=
    hC.isLocallyFiniteMeasure_traceMeasureOn
  refine ⟨C, by exact_mod_cast mul_pos hfactor hH, μ,
    fun i => ⟨hregular i, hlocal i, hrep i⟩, ?_⟩
  apply SmoothTestMeasureSeparation.Measure.le_of_testFunction_integral_le
  intro φ hφ
  rw [hC.integral_traceMeasureOn, ddc_scalarTopCurrent_kahlerPower_eq_sum_levi,
    integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul,
    integral_finsetSum_measure (fun i _ => compact_test_integrable (μ i) φ)]
  simp_rw [hrep]
  change (m.factorial : ℝ) / Real.pi *
      ∑ j, distributionalLeviCLM (coordinateVector j) T φ ≤
    ((m.factorial : ℝ) / Real.pi * H) * ∑ i, distributionalLeviCLM (b i) T φ
  have hn : 0 ≤ ∑ i, distributionalLeviCLM (b i) T φ :=
    Finset.sum_nonneg fun i _ => hT (b i) φ hφ
  calc
    (m.factorial : ℝ) / Real.pi *
        ∑ j, distributionalLeviCLM (coordinateVector j) T φ ≤
      (m.factorial : ℝ) / Real.pi *
        ∑ j, A j * ∑ i, distributionalLeviCLM (b i) T φ := by
      apply mul_le_mul_of_nonneg_left _ hfactor.le
      exact Finset.sum_le_sum fun j _ => hbound j φ hφ
    _ = (m.factorial : ℝ) / Real.pi *
        ((∑ j, A j) * ∑ i, distributionalLeviCLM (b i) T φ) := by
      rw [Finset.sum_mul]
    _ ≤ (m.factorial : ℝ) / Real.pi *
        (H * ∑ i, distributionalLeviCLM (b i) T φ) := by
      apply mul_le_mul_of_nonneg_left _ hfactor.le
      apply mul_le_mul_of_nonneg_right _ hn
      dsimp [H]
      linarith
    _ = _ := by ring

end SGPT.Foundations.Analysis.Pending.ActualLeviBasisTraceDomination
