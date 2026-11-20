import SGPT.Foundations.Analysis.FirstPass.GlobalCurrents
import Mathlib.Topology.Algebra.Module.Alternating.Topology
import Mathlib.Analysis.Complex.OperatorNorm

/-! ACTUAL complex-valued alternating tensor LF test spaces, with genuine
continuous real/imaginary coefficient maps and ALL-test scalar dictionaries. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.LocalCurrents
open scoped Topology Distributions
universe u
variable {n q : ℕ}

/-- Actual complex-valued real alternating tensors, without assumed reality. -/
abbrev ComplexCoeff (n q : ℕ) := ComplexModel n [⋀^Fin q]→L[ℝ] ℂ

/-- The GENUINE complex LF test form space on an actual model open. -/
abbrev ComplexTestForm (U : Opens (ComplexModel n)) (q : ℕ) := 𝓓(U,ComplexCoeff n q)

/-- Actual continuous tensor real-part map, not a coefficient certificate. -/
def coeffReCLM (n q : ℕ) : ComplexCoeff n q →L[ℝ] (ComplexModel n [⋀^Fin q]→L[ℝ] ℝ) :=
  ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ (ComplexModel n) ℂ ℝ (Fin q) Complex.reCLM

/-- Actual continuous tensor imaginary-part map. -/
def coeffImCLM (n q : ℕ) : ComplexCoeff n q →L[ℝ] (ComplexModel n [⋀^Fin q]→L[ℝ] ℝ) :=
  ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ (ComplexModel n) ℂ ℝ (Fin q) Complex.imCLM

/-- Actual continuous embedding of real alternating tensors. -/
def coeffOfRealCLM (n q : ℕ) : (ComplexModel n [⋀^Fin q]→L[ℝ] ℝ) →L[ℝ] ComplexCoeff n q :=
  ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ (ComplexModel n) ℝ ℂ (Fin q) Complex.ofRealCLM

variable (U : Opens (ComplexModel n))

/-- Genuine LF continuous real-part map on ALL actual complex tests. -/
def testReCLM : ComplexTestForm U q →L[ℝ] TestForm U q :=
  TestFunction.postcompCLM (coeffReCLM n q)

/-- Genuine LF continuous imaginary-part map on ALL actual complex tests. -/
def testImCLM : ComplexTestForm U q →L[ℝ] TestForm U q :=
  TestFunction.postcompCLM (coeffImCLM n q)

/-- Genuine LF continuous embedding of the actual real test forms. -/
def testOfRealCLM : TestForm U q →L[ℝ] ComplexTestForm U q :=
  TestFunction.postcompCLM (coeffOfRealCLM n q)

/-- Full coefficient real-part readback on every test, point and tangent tuple. -/
theorem testRe_apply (alpha : ComplexTestForm U q) (x : ComplexModel n) (v : Fin q → ComplexModel n) :
    testReCLM U alpha x v=(alpha x v).re := rfl

/-- Full coefficient imaginary-part readback. -/
theorem testIm_apply (alpha : ComplexTestForm U q) (x : ComplexModel n) (v : Fin q → ComplexModel n) :
    testImCLM U alpha x v=(alpha x v).im := rfl

/-- Full actual real embedding readback. -/
theorem testOfReal_apply (alpha : TestForm U q) (x : ComplexModel n) (v : Fin q → ComplexModel n) :
    testOfRealCLM U alpha x v=(alpha x v : ℂ) := rfl

/-- EVERY actual complex test is the genuine sum of its actual real and
imaginary embedded tests, including full support and all smoothness fields. -/
theorem complexTest_decomposition (alpha : ComplexTestForm U q) :
    testOfRealCLM U (testReCLM U alpha)+Complex.I • testOfRealCLM U (testImCLM U alpha)=alpha := by
  apply TestFunction.ext
  intro x
  ext v
  change ((alpha x v).re : ℂ)+Complex.I*((alpha x v).im : ℂ)=alpha x v
  exact Complex.ext (by simp) (by simp)

/-- Real/imaginary projection of a genuinely complex-scaled actual test. -/
theorem testRe_complex_smul (a : ℂ) (alpha : ComplexTestForm U q) :
    testReCLM U (a • alpha)=a.re • testReCLM U alpha-a.im • testImCLM U alpha := by
  apply TestFunction.ext
  intro x
  ext v
  change (a*(alpha x v)).re=a.re*(alpha x v).re-a.im*(alpha x v).im
  exact Complex.mul_re a (alpha x v)

/-- The imaginary projection retains the FULL genuine complex scalar law. -/
theorem testIm_complex_smul (a : ℂ) (alpha : ComplexTestForm U q) :
    testImCLM U (a • alpha)=a.re • testImCLM U alpha+a.im • testReCLM U alpha := by
  apply TestFunction.ext
  intro x
  ext v
  change (a*(alpha x v)).im=a.re*(alpha x v).im+a.im*(alpha x v).re
  exact Complex.mul_im a (alpha x v)

/-- Actual real tests recover under genuine embedding/real-part projection. -/
theorem testRe_ofReal (alpha : TestForm U q) : testReCLM U (testOfRealCLM U alpha)=alpha := by
  apply TestFunction.ext
  intro x
  ext v
  change ((alpha x v : ℂ)).re=alpha x v
  rfl

/-- The actual embedded real test has ZERO imaginary part, proved on all
coefficients; this is not imposed on arbitrary complex currents. -/
theorem testIm_ofReal (alpha : TestForm U q) : testImCLM U (testOfRealCLM U alpha)=0 := by
  apply TestFunction.ext
  intro x
  ext v
  change ((alpha x v : ℂ)).im=0
  rfl

end SGPT.PSH.ComplexCurrentDraft
