import SGPT.PSH.HermitianProductsHomogeneity
import SGPT.Foundations.Analysis.Pending.SmoothTestMeasureSeparation

/-! # Scalar homogeneity of the actual positive Hermitian trace measures -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorForms LocalBedfordTaylorCollar
open scoped Topology Distributions ContDiff

variable {n : ℕ} {U : Opens (ComplexModel n)}

/-- Positive scalar multiplication commutes with the genuine Riesz trace,
including the zero scalar. -/
theorem traceMeasure_smul_nnreal {r : ℕ} {T : LocalProductCurrent n U r}
    (hT : IsPositive T) (c : NNReal) :
    (hT.smul c.coe_nonneg).traceMeasure = c • hT.traceMeasure := by
  let hS : IsPositive ((c : ℝ) • T) := hT.smul c.coe_nonneg
  let _ := hS.isLocallyFiniteMeasure_traceMeasureOn
  let _ := hT.isLocallyFiniteMeasure_traceMeasureOn
  have heq (φ : 𝓓(U, ℝ)) : ∫ x : U, φ x ∂hS.traceMeasureOn =
      ∫ x : U, φ x ∂(c • hT.traceMeasureOn) := by
    rw [integral_smul_nnreal_measure, hS.integral_traceMeasureOn, hT.integral_traceMeasureOn]
    simp only [LinearMap.smul_apply, _root_.smul_apply, NNReal.smul_def, smul_eq_mul]
  have hOn : hS.traceMeasureOn = c • hT.traceMeasureOn := by
    apply le_antisymm
    · apply SmoothTestMeasureSeparation.Measure.le_of_testFunction_integral_le
      intro φ _
      exact (heq φ).le
    · apply SmoothTestMeasureSeparation.Measure.le_of_testFunction_integral_le
      intro φ _
      exact (heq φ).symm.le
  change hS.traceMeasureOn.map Subtype.val = c • hT.traceMeasureOn.map Subtype.val
  rw [hOn, Measure.map_smul]

theorem traceMeasure_eq_smul_of_current_eq {r : ℕ}
    {S T : LocalProductCurrent n U r} (hS : IsPositive S) (hT : IsPositive T)
    (c : NNReal) (heq : S = (c : ℝ) • T) :
    hS.traceMeasure = c • hT.traceMeasure := by
  subst S
  exact traceMeasure_smul_nnreal hT c

/-- Scalar homogeneity itself produces positivity of the scaled genuine
Hermitian product from the original full one-one factor inequalities. -/
theorem isPositive_backgroundExpansion_pos_smul
    {m : ℕ} {U : Opens (ComplexModel (m + 1))}
    (p r : ℕ) (T : LocalProductCurrent (m + 1) U (r + p))
    (hT : IsPositive T) (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel (m + 1) → ℝ)
    (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hσ11 : ∀ z ∈ U, IsOneOne (σ z))
    (hfactor : ∀ i, IsPositive
      (ddcMul (oneCurrent U) (v i) + wedgeForm rfl (oneCurrent U) hσ))
    {c : ℝ} (hc : 0 < c) :
    IsPositive (backgroundExpansion p r (fun i z => c * v i z) (hσ.const_smul c) T) := by
  rw [backgroundExpansion_pos_smul p r T hT hTc v hv hσ
    (fun z hz => oneOne_mem_formSpan (hσ11 z hz)) hc]
  exact (isPositive_backgroundExpansion p r T hT hTc v hv hσ hσ11 hfactor).smul
    (pow_nonneg hc.le p)

/-- The actual canonical trace measure scales by the degree power; neither
measure positivity nor a homogeneity conclusion is supplied as a premise. -/
theorem traceMeasure_backgroundExpansion_pos_smul
    {m : ℕ} {U : Opens (ComplexModel (m + 1))}
    (p r : ℕ) (T : LocalProductCurrent (m + 1) U (r + p))
    (hT : IsPositive T) (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel (m + 1) → ℝ)
    (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hσ11 : ∀ z ∈ U, IsOneOne (σ z))
    (hfactor : ∀ i, IsPositive
      (ddcMul (oneCurrent U) (v i) + wedgeForm rfl (oneCurrent U) hσ))
    {c : ℝ} (hc : 0 < c) :
    (isPositive_backgroundExpansion_pos_smul p r T hT hTc v hv hσ hσ11 hfactor hc).traceMeasure =
      Real.toNNReal (c ^ p) •
        (isPositive_backgroundExpansion p r T hT hTc v hv hσ hσ11 hfactor).traceMeasure :=
  by
    apply traceMeasure_eq_smul_of_current_eq _ _ (Real.toNNReal (c ^ p))
    simpa only [Real.coe_toNNReal _ (pow_nonneg hc.le p)] using
      backgroundExpansion_pos_smul p r T hT hTc v hv hσ
        (fun z hz => oneOne_mem_formSpan (hσ11 z hz)) hc

end SGPT.PSH.HermitianProducts
