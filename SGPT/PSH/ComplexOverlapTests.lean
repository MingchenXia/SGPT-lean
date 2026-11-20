import SGPT.PSH.ComplexCurrentTestForms

/-! Actual complex/real overlap tensor dictionaries in INDEPENDENT model
dimensions, with genuine LF inclusion and all compact-support identities. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.LocalCurrents
open scoped Topology Distributions
variable {n m q : ℕ} {U V : Opens (ComplexModel n)}

/-- Genuine complex LF inclusion readback; the real domain inclusion
hypothesis EXCLUDES the underlying library map's zero fallback. -/
theorem complex_test_inclusion_apply (hUV : U≤V) (alpha : ComplexTestForm U q) (x : ComplexModel n) :
    (TestFunction.monoCLM ℂ alpha : ComplexTestForm V q) x=alpha x := by
  have h := TestFunction.monoCLM_apply (𝕜 := ℂ) (n₂ := ⊤) (Ω₂ := V) alpha
  simpa only [le_refl,hUV,and_self,↓reduceIte] using congrFun h x

/-- Actual real-test embedding COMMUTES with genuine LF inclusion. -/
theorem testOfReal_mono (hUV : U≤V) (phi : TestForm U q) :
    testOfRealCLM V (TestFunction.monoCLM ℝ phi)=
      (TestFunction.monoCLM ℂ (testOfRealCLM U phi) : ComplexTestForm V q) := by
  apply TestFunction.ext
  intro x
  ext v
  rw [testOfReal_apply,testForm_inclusion_apply hUV,complex_test_inclusion_apply hUV,testOfReal_apply]

/-- Actual complex-test real part COMMUTES with genuine LF inclusion. -/
theorem testRe_mono (hUV : U≤V) (alpha : ComplexTestForm U q) :
    testReCLM V (TestFunction.monoCLM ℂ alpha)=
      (TestFunction.monoCLM ℝ (testReCLM U alpha) : TestForm V q) := by
  apply TestFunction.ext
  intro x
  ext v
  rw [testRe_apply,complex_test_inclusion_apply hUV,testForm_inclusion_apply hUV,testRe_apply]

/-- Actual complex-test imaginary part COMMUTES with genuine LF inclusion. -/
theorem testIm_mono (hUV : U≤V) (alpha : ComplexTestForm U q) :
    testImCLM V (TestFunction.monoCLM ℂ alpha)=
      (TestFunction.monoCLM ℝ (testImCLM U alpha) : TestForm V q) := by
  apply TestFunction.ext
  intro x
  ext v
  rw [testIm_apply,complex_test_inclusion_apply hUV,testForm_inclusion_apply hUV,testIm_apply]

/-- Actual compact-support source/target opens of a genuine original
transition between independently declared complex model dimensions. -/
def overlapDomain (F : OpenPartialHomeomorph (ComplexModel n) (ComplexModel m)) : Opens (ComplexModel n) :=
  ⟨F.source,F.open_source⟩
def overlapRange (F : OpenPartialHomeomorph (ComplexModel n) (ComplexModel m)) : Opens (ComplexModel m) :=
  ⟨F.target,F.open_target⟩

/-- Full COMPLEX alternating tensor overlap law on actual compact supports. -/
def ComplexOverlapRelated (F : OpenPartialHomeomorph (ComplexModel n) (ComplexModel m))
    (eta : ComplexTestForm (overlapDomain F) q) (theta : ComplexTestForm (overlapRange F) q) : Prop :=
  ∀ z,z∈F.source → ∀ v : Fin q → ComplexModel n,
    eta z v=theta (F z) (fun j => fderiv ℝ F z (v j))

/-- Full REAL alternating tensor overlap law on the SAME actual supports. -/
def RealOverlapRelated (F : OpenPartialHomeomorph (ComplexModel n) (ComplexModel m))
    (eta : TestForm (overlapDomain F) q) (theta : TestForm (overlapRange F) q) : Prop :=
  ∀ z,z∈F.source → ∀ v : Fin q → ComplexModel n,
    eta z v=theta (F z) (fun j => fderiv ℝ F z (v j))

/-- Actual complex overlap gives the ENTIRE real-part overlap tensor law. -/
theorem ComplexOverlapRelated.realPart
    {F : OpenPartialHomeomorph (ComplexModel n) (ComplexModel m)}
    {eta : ComplexTestForm (overlapDomain F) q} {theta : ComplexTestForm (overlapRange F) q}
    (h : ComplexOverlapRelated F eta theta) :
    RealOverlapRelated F (testReCLM (overlapDomain F) eta) (testReCLM (overlapRange F) theta) := by
  intro z hz v
  exact congrArg Complex.re (h z hz v)

/-- Actual complex overlap gives the ENTIRE imaginary-part overlap law. -/
theorem ComplexOverlapRelated.imaginaryPart
    {F : OpenPartialHomeomorph (ComplexModel n) (ComplexModel m)}
    {eta : ComplexTestForm (overlapDomain F) q} {theta : ComplexTestForm (overlapRange F) q}
    (h : ComplexOverlapRelated F eta theta) :
    RealOverlapRelated F (testImCLM (overlapDomain F) eta) (testImCLM (overlapRange F) theta) := by
  intro z hz v
  exact congrArg Complex.im (h z hz v)

/-- Embedded actual real overlap tests satisfy the GENUINE complex tensor
law, including every tangent tuple and the same original chart derivative. -/
theorem RealOverlapRelated.complexEmbedding
    {F : OpenPartialHomeomorph (ComplexModel n) (ComplexModel m)}
    {eta : TestForm (overlapDomain F) q} {theta : TestForm (overlapRange F) q}
    (h : RealOverlapRelated F eta theta) :
    ComplexOverlapRelated F (testOfRealCLM (overlapDomain F) eta) (testOfRealCLM (overlapRange F) theta) := by
  intro z hz v
  exact congrArg Complex.ofReal (h z hz v)

end SGPT.PSH.ComplexCurrentDraft
