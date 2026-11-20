import SGPT.Foundations.Analysis.Pending.DivisorRegularLocus
import SGPT.Foundations.Analysis.Pending.CoordinateWedgeAssoc

/-! The ACTUAL normalized conormal real two-form and its manufactured positive unit normal.
Blueprint: `complex-normal-form.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.ComplexNormalForm

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending StronglyPositiveForms CoordinateWedgeAssoc
open scoped ComplexConjugate InnerProductSpace

variable {n : ℕ}

/-- The genuine original normalized normal two-form, built from actual real covectors. -/
def normalForm (ℓ : ComplexModel n →L[ℂ] ℂ) : RealForm n 2 :=
  (‖ℓ‖ ^ 2)⁻¹ • coordinateWedge
    (oneForm n (Complex.reCLM.comp (ℓ.restrictScalars ℝ)))
    (oneForm n (Complex.imCLM.comp (ℓ.restrictScalars ℝ)))

/-- Its WHOLE actual alternating coefficient is exactly the unchanged original lineForm. -/
theorem normalForm_apply (ℓ : ComplexModel n →L[ℂ] ℂ) (v : Fin 2 → ComplexModel n) :
    normalForm ℓ v = DivisorRegularLocus.lineForm ℓ (v 0) (v 1) := by
  rw [normalForm, ContinuousAlternatingMap.smul_apply, coordinateWedge_one_one_apply]
  simp only [oneForm_apply, ContinuousLinearMap.comp_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul, DivisorRegularLocus.lineForm,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, div_eq_mul_inv]
  change (‖ℓ‖ ^ 2)⁻¹ * ((ℓ (v 0)).re * (ℓ (v 1)).im - (ℓ (v 1)).re * (ℓ (v 0)).im) =
    ((ℓ (v 0)).re * (ℓ (v 1)).im + -(ℓ (v 0)).im * (ℓ (v 1)).re) * (‖ℓ‖ ^ 2)⁻¹
  ring

theorem normalForm_pair (ℓ : ComplexModel n →L[ℂ] ℂ) (v w : ComplexModel n) :
    normalForm ℓ ![v, w] = DivisorRegularLocus.lineForm ℓ v w := by
  rw [normalForm_apply]
  rfl

/-- The ORIGINAL actual kernel kills the first normal-form slot. -/
theorem normalForm_pair_left_kernel (ℓ : ComplexModel n →L[ℂ] ℂ) (v w : ComplexModel n)
    (hv : ℓ v = 0) : normalForm ℓ ![v, w] = 0 := by
  simp [normalForm_pair, DivisorRegularLocus.lineForm, hv]

/-- The ORIGINAL actual kernel kills the second normal-form slot. -/
theorem normalForm_pair_right_kernel (ℓ : ComplexModel n →L[ℂ] ℂ) (v w : ComplexModel n)
    (hw : ℓ w = 0) : normalForm ℓ ![v, w] = 0 := by
  simp [normalForm_pair, DivisorRegularLocus.lineForm, hw]

/-- The actual positive unit normal is manufactured from the ORIGINAL Riesz dual. -/
def normalVector (ℓ : ComplexModel n →L[ℂ] ℂ) : ComplexModel n :=
  ((‖ℓ‖⁻¹ : ℝ) : ℂ) • (InnerProductSpace.toDual ℂ (ComplexModel n)).symm ℓ

theorem normalVector_norm (ℓ : ComplexModel n →L[ℂ] ℂ) (hℓ : ℓ ≠ 0) :
    ‖normalVector ℓ‖ = 1 := by
  rw [normalVector, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg ℓ)), LinearIsometryEquiv.norm_map]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hℓ)

/-- The original Riesz identity with the internally normalized positive normal. -/
theorem inner_normalVector (ℓ : ComplexModel n →L[ℂ] ℂ) (w : ComplexModel n) :
    ⟪normalVector ℓ, w⟫_ℂ = ((‖ℓ‖⁻¹ : ℝ) : ℂ) * ℓ w := by
  rw [normalVector, inner_smul_left, InnerProductSpace.toDual_symm_apply]
  simp

/-- The original covector reads the actual manufactured positive normal as its original norm. -/
theorem normalVector_value (ℓ : ComplexModel n →L[ℂ] ℂ) (hℓ : ℓ ≠ 0) :
    ℓ (normalVector ℓ) = ((‖ℓ‖ : ℝ) : ℂ) := by
  rw [normalVector, map_smul, smul_eq_mul]
  have hd := InnerProductSpace.toDual_symm_apply
    (x := (InnerProductSpace.toDual ℂ (ComplexModel n)).symm ℓ) (y := ℓ)
  rw [← hd, inner_self_eq_norm_sq_to_K, LinearIsometryEquiv.norm_map]
  have hr : (‖ℓ‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hℓ
  have hc : ((‖ℓ‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  push_cast
  field_simp
  rfl

/-- The SAME original covector is exactly norm times pairing with its actual positive unit normal. -/
theorem covector_eq_norm_mul_inner_normalVector (ℓ : ComplexModel n →L[ℂ] ℂ) (hℓ : ℓ ≠ 0)
    (w : ComplexModel n) : ℓ w = ((‖ℓ‖ : ℝ) : ℂ) * ⟪normalVector ℓ, w⟫_ℂ := by
  rw [inner_normalVector, ← mul_assoc]
  have hc : ((‖ℓ‖ : ℝ) : ℂ) * ((‖ℓ‖⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hℓ), Complex.ofReal_one]
  rw [hc, one_mul]

/-- The actual original normal two-form has positive unit value on its complex normal plane. -/
theorem normalForm_normalVector_I (ℓ : ComplexModel n →L[ℂ] ℂ) (hℓ : ℓ ≠ 0) :
    normalForm ℓ ![normalVector ℓ, Complex.I • normalVector ℓ] = 1 := by
  rw [normalForm_pair, DivisorRegularLocus.lineForm_apply_I, normalVector_value ℓ hℓ]
  simp only [Complex.norm_real, norm_norm]
  exact div_self (pow_ne_zero _ (norm_ne_zero_iff.mpr hℓ))

end SGPT.Projective.NumEq.CompleteIntersections.ComplexNormalForm
