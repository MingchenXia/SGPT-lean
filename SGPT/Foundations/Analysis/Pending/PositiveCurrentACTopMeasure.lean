import SGPT.Foundations.Analysis.Pending.LocalCurrentPullback
import SGPT.Foundations.Analysis.FirstPass.CoordinateWedgePullback

/-! # The actual absolutely continuous top measure of a positive current

The complete statement and entire mathematical proof are in the owned
blueprint file `positive-current-ac-top-measure.tex`.  This coordinate
construction has no analytic-singularity or finite-mass hypothesis.
-/

set_option autoImplicit false

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions

namespace SGPT.Foundations.Analysis.Pending.PositiveCurrentACTopMeasure

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalCurrentDeterminant LocalCurrentDensityMatrix LocalCurrentPullback BedfordTaylor

variable {m : ℕ} {U : Opens (ComplexModel (m + 1))}
  {T : LocalProductCurrent (m + 1) U m}

/-- The actual top-power density of the canonical coefficientwise AC form,
restricted to the current's open domain.  Its mass is allowed to be infinite. -/
def acTopMeasure (hT : IsPositive T) : Measure (ComplexModel (m + 1)) :=
  (volume.withDensity fun x => ENNReal.ofReal (actualTopPowerDensity (acForm hT x))).restrict U

/-- The genuine exterior-power density, including its chosen values off the
current's domain, is measurable without an analytic-singularity hypothesis. -/
theorem measurable_acTopDensity (hT : IsPositive T) :
    Measurable fun x => actualTopPowerDensity (acForm hT x) := by
  have hpoint (x : ComplexModel (m + 1)) :
      actualTopPowerDensity (acForm hT x) =
        ((m + 1).factorial : ℝ) / Real.pi ^ (m + 1) * (acMatrix hT x).det.re := by
    rw [actualTopPowerDensity_eq_normalizedTopPowerDensity _ (isOneOne_acForm hT x),
      normalizedTopPowerDensity, complexTopCoefficient_eq]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rfl
  simp_rw [hpoint]
  exact (Complex.measurable_re.comp (measurable_det_acMatrix hT)).const_mul _

/-- The entire actual AC top measure transforms by the genuine inverse
biholomorphism, with no finite-integral or closedness premise. -/
theorem map_acTopMeasure_eq
    {A B : Opens (ComplexModel (m + 1))}
    {τ σ : ComplexModel (m + 1) → ComplexModel (m + 1)}
    (h : IsBiholomorphicPair A B τ σ) {S : LocalProductCurrent (m + 1) B m}
    (hS : IsPositive S) :
    (acTopMeasure hS).map (onOpen B σ) =
      acTopMeasure (isPositive_pullback h hS) := by
  unfold acTopMeasure
  rw [map_withDensity_restrict h, restrict_withDensity A.isOpen.measurableSet]
  apply withDensity_congr_ae
  filter_upwards [(ae_restrict_iff' A.isOpen.measurableSet).2 (ae_acForm_pullback h hS),
    ae_restrict_mem A.isOpen.measurableSet] with x hx hxA
  rw [onOpen_of_mem hxA, hx,
    actualTopPowerDensity_compContinuousLinearMap]
  change ENNReal.ofReal |(fderiv ℝ τ x).det| *
      ENNReal.ofReal (actualTopPowerDensity (acForm hS (τ x))) =
    ENNReal.ofReal (((fderiv ℂ τ x).restrictScalars ℝ).det *
      actualTopPowerDensity (acForm hS (τ x)))
  rw [fderiv_real_eq h hxA, det_restrictScalars_eq_normSq,
    abs_of_nonneg (Complex.normSq_nonneg _),
    ENNReal.ofReal_mul (Complex.normSq_nonneg _)]

end SGPT.Foundations.Analysis.Pending.PositiveCurrentACTopMeasure
