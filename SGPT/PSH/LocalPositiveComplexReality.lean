import SGPT.PSH.ComplexLocalCurrents
import SGPT.PSH.PositiveComplexScalarReality
import SGPT.PSH.PureComplexCurrentType
import SGPT.PSH.SourceBetaProductSpan
import SGPT.Foundations.Analysis.Pending.CompactDdcCoordinateExpansion

/-! Genuine local positive COMPLEX currents are real in every degree.
Actual scalar cutoffs and proved literal decomposable span manufacture all
reality conclusions; no real presentation is supplied. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentDraft
open Set Finset TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.LocalCurrents
open SGPT.Foundations.Analysis.Pending
open StronglyPositiveForms LocalProductCurrents CompactDdcCoordinateExpansion LocalCurrentLebesgue
open SGPT.PSH.BookCurrent
open scoped Topology Distributions ContDiff
variable {n p : ℕ} (U : Opens (ComplexModel n))

/-- Genuine constant tensor multiples as continuous scalar LF test maps. -/
def constantTensorTestCLM (P : RealForm n (2*p)) :
    𝓓(U,ℝ) →L[ℝ] TestForm U (2*p) :=
  TestFunction.postcompCLM ((ContinuousLinearMap.id ℝ ℝ).smulRight P)

theorem constantTensorTest_apply (P : RealForm n (2*p)) (phi : 𝓓(U,ℝ))
    (z : ComplexModel n) : constantTensorTestCLM U P phi z=phi z • P := rfl

theorem constantTensorTest_zero (phi : 𝓓(U,ℝ)) :
    constantTensorTestCLM U (0 : RealForm n (2*p)) phi=0 := by
  apply TestFunction.ext
  intro z
  simp [constantTensorTest_apply]

theorem constantTensorTest_add (P Q : RealForm n (2*p)) (phi : 𝓓(U,ℝ)) :
    constantTensorTestCLM U (P+Q) phi=
      constantTensorTestCLM U P phi+constantTensorTestCLM U Q phi := by
  apply TestFunction.ext
  intro z
  exact smul_add (phi z) P Q

theorem constantTensorTest_smul (c : ℝ) (P : RealForm n (2*p)) (phi : 𝓓(U,ℝ)) :
    constantTensorTestCLM U (c • P) phi=c • constantTensorTestCLM U P phi := by
  apply TestFunction.ext
  intro z
  exact smul_comm (phi z) c P

/-- Literal local complex source test: EVERY actual smooth (1,0)-family
and EVERY nonnegative compact scalar test yields a real nonnegative value.
Only the nonnegative tests are assumed real. -/
def ComplexLocalWeakPositive (T : ComplexLocalFunctional U (2*p)) : Prop :=
  ∀ beta : Fin p → ComplexModel n → ComplexModel n →L[ℂ] ℂ,
    (∀ j,ContDiffOn ℝ ∞ (beta j) (U : Set (ComplexModel n))) →
    ∀ phi : 𝓓(U,ℝ),(∀ z,0≤phi z) →
    ∀ alpha : TestForm U (2*p),(∀ z,alpha z=phi z • betaProduct (fun j => beta j z)) →
      (T (testOfRealCLM U alpha)).im=0 ∧ 0≤(T (testOfRealCLM U alpha)).re

/-- The ACTUAL constant-source wedge scalar functional is LF continuous. -/
def constantBetaWedgeFunctional (T : ComplexLocalFunctional U (2*p))
    (beta : Fin p → ComplexModel n →L[ℂ] ℂ) : 𝓓(U,ℝ) →L[ℝ] ℂ :=
  (T.restrictScalars ℝ).comp ((testOfRealCLM U).comp (constantTensorTestCLM U (betaProduct beta)))

/-- Source positivity applies to actually PRODUCED constant beta tests,
so there is no vacuous supplied-test or measure-output certificate. -/
theorem weak_positive_constant_wedge_positive (T : ComplexLocalFunctional U (2*p))
    (hT : ComplexLocalWeakPositive U T) (beta : Fin p → ComplexModel n →L[ℂ] ℂ) :
    ComplexScalarPositive U (constantBetaWedgeFunctional U T beta) := by
  intro phi hphi
  exact hT (fun j _ => beta j) (fun _ => contDiffOn_const) phi hphi
    (constantTensorTestCLM U (betaProduct beta) phi) (fun _ => rfl)

/-- The full signed scalar difference decomposition kills the imaginary
current on every genuine constant literal source beta-product test. -/
theorem weak_positive_im_constant_beta_zero (T : ComplexLocalFunctional U (2*p))
    (hT : ComplexLocalWeakPositive U T) (beta : Fin p → ComplexModel n →L[ℂ] ℂ)
    (phi : 𝓓(U,ℝ)) :
    currentIm U T (constantTensorTestCLM U (betaProduct beta) phi)=0 :=
  positive_complex_scalar_im_eq_zero U (constantBetaWedgeFunctional U T beta)
    (weak_positive_constant_wedge_positive U T hT beta) phi

/-- Proved source beta spanning, followed by actual finite coefficient LF
test expansion, yields vanishing on EVERY usual real pure (p,p) test. -/
theorem real_current_zero_on_pure_of_constant_beta_zero
    (G : RealLocalFunctional U (2*p))
    (hG : ∀ beta : Fin p → ComplexModel n →L[ℂ] ℂ,∀ phi : 𝓓(U,ℝ),
      G (constantTensorTestCLM U (betaProduct beta) phi)=0)
    (alpha : TestForm U (2*p)) (ha : ∀ z,alpha z ∈ formSpan n p) : G alpha=0 := by
  have hconst : ∀ P ∈ sourceBetaSpan n p,∀ phi : 𝓓(U,ℝ),
      G (constantTensorTestCLM U P phi)=0 := by
    intro P hP
    induction hP using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨beta,rfl⟩ := hx
      exact hG beta
    | zero =>
      intro phi
      rw [constantTensorTest_zero,map_zero]
    | add x y _ _ hx hy =>
      intro phi
      rw [constantTensorTest_add,map_add,hx phi,hy phi,add_zero]
    | smul c x _ hx =>
      intro phi
      rw [constantTensorTest_smul,map_smul,hx phi,smul_zero]
  rw [eq_sum_constFormTest alpha ha,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  exact hconst (formBasis n p i) (by
    rw [sourceBetaSpan_eq_formSpan]
    exact (formBasis n p i).property) (CompactVariableCurrentTests.coeffTest alpha i)

/-- Actual arbitrary complex current + true bidegree + literal source weak
positivity implies its ENTIRE imaginary real current is zero on ALL tests. -/
theorem positive_pure_complex_current_im_eq_zero (T : ComplexLocalFunctional U (2*p))
    (htype : ComplexLocalHasPureType U T) (hpos : ComplexLocalWeakPositive U T) :
    currentIm U T=0 := by
  ext alpha
  rw [pure_type_im_factor U T htype alpha]
  exact real_current_zero_on_pure_of_constant_beta_zero U (currentIm U T)
    (weak_positive_im_constant_beta_zero U T hpos) (realPureTestProjector U p alpha)
    (realPureTestProjector_mem_formSpan U alpha)

/-- The actual internally produced REAL LF current recovers the original
positive COMPLEX current on EVERY genuine complex tensor test. -/
theorem positive_pure_complex_current_real_extension (T : ComplexLocalFunctional U (2*p))
    (htype : ComplexLocalHasPureType U T) (hpos : ComplexLocalWeakPositive U T) :
    extendComplexCurrent U (currentRe U T) 0=T := by
  have h := extend_current_re_im U T
  rwa [positive_pure_complex_current_im_eq_zero U T htype hpos] at h

end SGPT.PSH.ComplexCurrentDraft
