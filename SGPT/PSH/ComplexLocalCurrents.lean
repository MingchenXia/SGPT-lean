import SGPT.PSH.ComplexCurrentTestForms

/-! GENUINE complex-linear continuous LF current functionals and their
canonical real/imaginary current dictionary, with no reality assumption. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.LocalCurrents
open scoped Topology Distributions
variable {n q : ℕ} (U : Opens (ComplexModel n))

/-- An ACTUAL complex current functional on ALL genuine complex LF tests.
Its values may be nonreal; reality is NOT a field or hypothesis. -/
abbrev ComplexLocalFunctional (q : ℕ) := ComplexTestForm U q →L[ℂ] ℂ

/-- The existing genuine real LF current functional at the SAME test degree. -/
abbrev RealLocalFunctional (q : ℕ) := TestForm U q →L[ℝ] ℝ

/-- Actual real-part current, internally continuous by scalar restriction
and genuine LF real-test embedding; no real presentation is supplied. -/
def currentRe (T : ComplexLocalFunctional U q) : RealLocalFunctional U q :=
  Complex.reCLM.comp ((T.restrictScalars ℝ).comp (testOfRealCLM U))

/-- Actual imaginary current, not assumed zero. -/
def currentIm (T : ComplexLocalFunctional U q) : RealLocalFunctional U q :=
  Complex.imCLM.comp ((T.restrictScalars ℝ).comp (testOfRealCLM U))

/-- Arbitrary actual real/imaginary current functionals EXTEND to a genuine
COMPLEX-linear continuous current on ALL genuine complex test forms.
Both complex linearity and LF continuity are proved from actual test maps. -/
def extendComplexCurrent (A B : RealLocalFunctional U q) : ComplexLocalFunctional U q where
  toFun alpha := (A (testReCLM U alpha) : ℂ)-(B (testImCLM U alpha) : ℂ)+
    Complex.I*((B (testReCLM U alpha) : ℂ)+(A (testImCLM U alpha) : ℂ))
  map_add' alpha beta := by
    simp only [map_add,Complex.ofReal_add]
    ring
  map_smul' a alpha := by
    rw [testRe_complex_smul,testIm_complex_smul]
    simp only [map_add,map_sub,map_smul,smul_eq_mul,Complex.ofReal_add,
      Complex.ofReal_sub,Complex.ofReal_mul]
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring
  cont := by
    have hAR := (Complex.ofRealCLM.comp (A.comp (testReCLM U))).continuous
    have hBI := (Complex.ofRealCLM.comp (B.comp (testImCLM U))).continuous
    have hBR := (Complex.ofRealCLM.comp (B.comp (testReCLM U))).continuous
    have hAI := (Complex.ofRealCLM.comp (A.comp (testImCLM U))).continuous
    exact (hAR.sub hBI).add (continuous_const.mul (hBR.add hAI))

/-- Full actual formula on EVERY complex test. -/
theorem extendComplexCurrent_apply (A B : RealLocalFunctional U q) (alpha : ComplexTestForm U q) :
    extendComplexCurrent U A B alpha=(A (testReCLM U alpha) : ℂ)-(B (testImCLM U alpha) : ℂ)+
      Complex.I*((B (testReCLM U alpha) : ℂ)+(A (testImCLM U alpha) : ℂ)) := rfl

/-- Genuine real/imaginary value readback on every embedded REAL test. -/
theorem current_re_im_value (T : ComplexLocalFunctional U q) (phi : TestForm U q) :
    (currentRe U T phi : ℂ)+Complex.I*(currentIm U T phi : ℂ)=T (testOfRealCLM U phi) := by
  change ((T (testOfRealCLM U phi)).re : ℂ)+
    Complex.I*((T (testOfRealCLM U phi)).im : ℂ)=T (testOfRealCLM U phi)
  exact Complex.ext (by simp) (by simp)

/-- The ACTUAL extension recovers its entire real current on ALL real tests. -/
theorem currentRe_extend (A B : RealLocalFunctional U q) :
    currentRe U (extendComplexCurrent U A B)=A := by
  ext phi
  change (((A (testReCLM U (testOfRealCLM U phi)) : ℂ)-
    (B (testImCLM U (testOfRealCLM U phi)) : ℂ)+
      Complex.I*((B (testReCLM U (testOfRealCLM U phi)) : ℂ)+
        (A (testImCLM U (testOfRealCLM U phi)) : ℂ)))).re=A phi
  simp [testRe_ofReal,testIm_ofReal]

/-- The ACTUAL extension recovers its arbitrary imaginary current, so
complex currents have NOT been restricted to real currents by definition. -/
theorem currentIm_extend (A B : RealLocalFunctional U q) :
    currentIm U (extendComplexCurrent U A B)=B := by
  ext phi
  change (((A (testReCLM U (testOfRealCLM U phi)) : ℂ)-
    (B (testImCLM U (testOfRealCLM U phi)) : ℂ)+
      Complex.I*((B (testReCLM U (testOfRealCLM U phi)) : ℂ)+
        (A (testImCLM U (testOfRealCLM U phi)) : ℂ)))).im=B phi
  simp [testRe_ofReal,testIm_ofReal]

/-- EVERY genuine complex LF current is reconstructed on ALL complex tests
from its internally produced real/imaginary actual current functionals. -/
theorem extend_current_re_im (T : ComplexLocalFunctional U q) :
    extendComplexCurrent U (currentRe U T) (currentIm U T)=T := by
  ext alpha
  calc
    _ = ((currentRe U T (testReCLM U alpha) : ℂ)+Complex.I*(currentIm U T (testReCLM U alpha) : ℂ))+
        Complex.I*((currentRe U T (testImCLM U alpha) : ℂ)+Complex.I*(currentIm U T (testImCLM U alpha) : ℂ)) := by
      rw [extendComplexCurrent_apply]
      (apply Complex.ext <;> simp); ring
    _ = T (testOfRealCLM U (testReCLM U alpha))+Complex.I*T (testOfRealCLM U (testImCLM U alpha)) := by
      rw [current_re_im_value,current_re_im_value]
    _ = T (testOfRealCLM U (testReCLM U alpha)+Complex.I • testOfRealCLM U (testImCLM U alpha)) := by
      rw [map_add,map_smul,smul_eq_mul]
    _ = T alpha := congrArg T (complexTest_decomposition U alpha)

/-- GENUINE complete current dictionary, BEFORE positivity/reality, with
actual continuous COMPLEX-linear LF functionals as its original domain. -/
def complexLocalCurrentEquivRealPair : ComplexLocalFunctional U q ≃
    (RealLocalFunctional U q × RealLocalFunctional U q) where
  toFun T := (currentRe U T,currentIm U T)
  invFun p := extendComplexCurrent U p.1 p.2
  left_inv := extend_current_re_im U
  right_inv := by
    rintro ⟨A,B⟩
    exact Prod.ext (currentRe_extend U A B) (currentIm_extend U A B)

end SGPT.PSH.ComplexCurrentDraft
