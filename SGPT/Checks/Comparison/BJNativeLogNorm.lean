import SGPT.Checks.Comparison.BJNativeSectionNorm
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-! Literal source negative valuations agree with logarithms of ACTUAL
native proper-model section norms, including all zero/polar cases. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.NAPotential.BJ
open scoped NNReal ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.NAPotential.BJ.NativePicard
open SGPT.Foundations.Envelope.SchemeGlobalSectionModelNormIsometries

theorem ennreal_log_expNegNN (a : WithTop ℝ) :
    ENNReal.log (expNegNN a : ℝ≥0∞)=negativeValue a := by
  cases a with
  | top => simp only [expNegNN_top,ENNReal.coe_zero,ENNReal.log_zero,negativeValue_top]
  | coe r =>
    rw [← ENNReal.ofReal_coe_nnreal]
    change ENNReal.log (ENNReal.ofReal (Real.exp (-r)))=(((-r):ℝ):EReal)
    rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _),Real.log_exp]

variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProper p]

/-- Every actual original power section has exactly the original log norm
in the native model norm, at every original point including its poles. -/
theorem nativeGlobalSectionLogNorm_eq_source {L : X.Modules} (a : LineBundleAtlas L)
    (n : ℕ) (s : bundlePowerGlobalSections L n) (v : BerkovichPoint p) :
    ENNReal.log (globalSectionNorm Valuation.one_apply_le_one (pointEquiv p v)
      (bundleTensorPower L n) (isInvertible_of_atlas (powerAtlas a n)) s : ℝ≥0∞)=
      sectionLogNorm a n s v := by
  rw [nativeGlobalSectionNorm_eq_powerSectionValue,ennreal_log_expNegNN]
  rfl

end SGPT.NAPotential.BJ
