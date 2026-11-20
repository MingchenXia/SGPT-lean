import SGPT.PSH.BookCurrentProducts

/-! Actual (1,0) covectors canonically produced from real covectors. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentDraft
open SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.BookCurrent
variable {n m : ℕ}

private theorem complex_smul_split (c : ℂ) (v : ComplexModel n) :
    c • v=c.re • v+c.im • (Complex.I • v) := by
  calc
    c • v=((c.re : ℂ)+(c.im : ℂ)*Complex.I) • v :=
      congrArg (fun a : ℂ => a • v) (Complex.re_add_im c).symm
    _ = _ := by rw [add_smul,mul_smul,Complex.coe_smul,Complex.coe_smul]

/-- The actual complex-linear covector df-i df∘J, with full physical value.
It is NOT an arbitrary supplied (1,0) field or a type/reality certificate. -/
def realCovectorComplexLift (L : ComplexModel n →L[ℝ] ℝ) : ComplexModel n →L[ℂ] ℂ where
  toFun v := (L v : ℂ)-Complex.I*(L (Complex.I • v) : ℂ)
  map_add' v w := by
    simp only [smul_add,map_add,Complex.ofReal_add]
    ring
  map_smul' c v := by
    rw [complex_smul_split c v,smul_add,smul_comm Complex.I c.re,
      smul_comm Complex.I c.im,smul_smul,Complex.I_mul_I,neg_one_smul]
    simp only [map_add,map_smul,map_neg,smul_eq_mul,Complex.ofReal_add,
      Complex.ofReal_mul,Complex.ofReal_neg]
    (apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]); ring
  cont := by
    exact (Complex.ofRealCLM.continuous.comp L.continuous).sub
      (continuous_const.mul (Complex.ofRealCLM.continuous.comp
        (L.continuous.comp (continuous_const_smul Complex.I))))

/-- Genuine continuous real-linear conversion of actual cotangent fibers. -/
def realCovectorComplexLiftCLM (n : ℕ) :
    (ComplexModel n →L[ℝ] ℝ) →L[ℝ] (ComplexModel n →L[ℂ] ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := realCovectorComplexLift
      map_add' := by
        intro L K
        ext v
        change (((L+K) v : ℝ) : ℂ)-Complex.I*((L+K) (Complex.I • v) : ℂ)=
          ((L v : ℂ)-Complex.I*(L (Complex.I • v) : ℂ))+
            ((K v : ℂ)-Complex.I*(K (Complex.I • v) : ℂ))
        simp only [_root_.add_apply,Complex.ofReal_add]
        ring
      map_smul' := by
        intro c L
        ext v
        change (((c • L) v : ℝ) : ℂ)-Complex.I*((c • L) (Complex.I • v) : ℂ)=
          c • ((L v : ℂ)-Complex.I*(L (Complex.I • v) : ℂ))
        simp only [_root_.smul_apply,smul_eq_mul,Complex.ofReal_mul,Complex.real_smul]
        ring }

/-- Every actual source complex covector is recovered from its REAL part. -/
theorem realCovectorComplexLift_reForm (b : ComplexModel n →L[ℂ] ℂ) :
    realCovectorComplexLift (reForm b)=b := by
  ext v
  apply Complex.ext <;> simp [realCovectorComplexLift,reForm,Complex.mul_re,Complex.mul_im]

/-- Actual holomorphic tensor pullback preserves the produced (1,0) field. -/
theorem realCovectorComplexLift_comp (L : ComplexModel n →L[ℝ] ℝ)
    (F : ComplexModel m →L[ℝ] ComplexModel n)
    (hF : ∀ v,F (Complex.I • v)=Complex.I • F v) (v : ComplexModel m) :
    realCovectorComplexLift (L.comp F) v=realCovectorComplexLift L (F v) := by
  change (L (F v) : ℂ)-Complex.I*(L (F (Complex.I • v)) : ℂ)=
    (L (F v) : ℂ)-Complex.I*(L (Complex.I • F v) : ℂ)
  rw [hF]

end SGPT.PSH.ComplexCurrentDraft
