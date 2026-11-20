import SGPT.PSH.ComplexLocalCurrents
import SGPT.Foundations.Analysis.Pending.NaturalSmoothPPProjector
import SGPT.Foundations.Analysis.Pending.NaturalRealPPPositiveSpanDictionary

/-! The actual normalized natural pure-(p,p) projector, not an arbitrary
chosen span complement, on genuine LF tests and complex current type. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentDraft
open Set TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.LocalCurrents
open SGPT.Foundations.Analysis.Pending
open NaturalSmoothPPProjector NaturalRealPPPositiveSpanDictionary
open scoped Topology Distributions
variable {n p : ℕ} (U : Opens (ComplexModel n))

/-- Genuine continuous LF pure-test projector, induced by the normalized
usual pure-bidegree tensor projector. No arbitrary formSpan complement. -/
def realPureTestProjector (p : ℕ) : TestForm U (2*p) →L[ℝ] TestForm U (2*p) :=
  TestFunction.postcompCLM (realProjectorCLM n p)

theorem realPureTestProjector_apply (alpha : TestForm U (2*p)) (z : ComplexModel n) :
    realPureTestProjector U p alpha z = realProjector (alpha z) := rfl

theorem realPureTestProjector_mem_formSpan (alpha : TestForm U (2*p)) (z : ComplexModel n) :
    realPureTestProjector U p alpha z ∈ LocalProductCurrents.formSpan n p :=
  (mem_formSpan_iff_pureRealPP _).mpr (realProjector_isPure _)

theorem realPureTestProjector_idempotent (alpha : TestForm U (2*p)) :
    realPureTestProjector U p (realPureTestProjector U p alpha) = realPureTestProjector U p alpha := by
  apply TestFunction.ext
  intro z
  exact realProjector_idempotent (alpha z)

/-- ACTUAL complexification of the genuine normalized pure-type projector.
It acts on unrestricted complex LF tests; no current realness is involved. -/
def complexPureTest (alpha : ComplexTestForm U (2*p)) : ComplexTestForm U (2*p) :=
  testOfRealCLM U (realPureTestProjector U p (testReCLM U alpha))+
    Complex.I • testOfRealCLM U (realPureTestProjector U p (testImCLM U alpha))

/-- Exact full tensor evaluation of the actual complex pure-type operation. -/
theorem complexPureTest_apply (alpha : ComplexTestForm U (2*p))
    (z : ComplexModel n) (v : Fin (2*p) → ComplexModel n) :
    complexPureTest U alpha z v =
      (realProjector (coeffReCLM n (2*p) (alpha z)) v : ℂ)+
        Complex.I*(realProjector (coeffImCLM n (2*p) (alpha z)) v : ℂ) := rfl

/-- Original (m,m) type on dual complementary degree 2p: the current pairs
only with the actual normalized usual pure-(p,p) part of EVERY complex test.
This is a bidegree condition and assumes NO reality/positivity conclusion. -/
def ComplexLocalHasPureType (T : ComplexLocalFunctional U (2*p)) : Prop :=
  ∀ alpha : ComplexTestForm U (2*p),T alpha=T (complexPureTest U alpha)

theorem complexPureTest_ofReal (alpha : TestForm U (2*p)) :
    complexPureTest U (testOfRealCLM U alpha)=
      testOfRealCLM U (realPureTestProjector U p alpha) := by
  simp [complexPureTest,testRe_ofReal,testIm_ofReal]

/-- The imaginary current retains the ACTUAL complementary bidegree, with
its all-real-test factorization PROVED from the original complex type. -/
theorem pure_type_im_factor (T : ComplexLocalFunctional U (2*p))
    (hT : ComplexLocalHasPureType U T) (alpha : TestForm U (2*p)) :
    currentIm U T alpha=currentIm U T (realPureTestProjector U p alpha) := by
  have h := hT (testOfRealCLM U alpha)
  rw [complexPureTest_ofReal] at h
  exact congrArg Complex.im h

theorem pure_type_re_factor (T : ComplexLocalFunctional U (2*p))
    (hT : ComplexLocalHasPureType U T) (alpha : TestForm U (2*p)) :
    currentRe U T alpha=currentRe U T (realPureTestProjector U p alpha) := by
  have h := hT (testOfRealCLM U alpha)
  rw [complexPureTest_ofReal] at h
  exact congrArg Complex.re h

/-- Every real pure test is FIXED by the true natural projector. -/
theorem realPureTestProjector_eq_self (alpha : TestForm U (2*p))
    (ha : ∀ z,alpha z ∈ LocalProductCurrents.formSpan n p) :
    realPureTestProjector U p alpha=alpha := by
  apply TestFunction.ext
  intro z
  exact realProjector_of_isPure _ ((mem_formSpan_iff_pureRealPP _).mp (ha z))

end SGPT.PSH.ComplexCurrentDraft
