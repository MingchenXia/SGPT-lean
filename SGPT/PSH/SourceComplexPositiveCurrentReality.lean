import SGPT.PSH.SourceGlobalComplexCurrentPositivity
import SGPT.PSH.OriginalGlobalConstantBetaLocalization
import SGPT.PSH.OriginalPositiveComplexReality

/-! LITERAL original GLOBAL-beta source positivity ⇒ actual realness of
arbitrary complex (m,m) currents, without a local-positivity hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.LocalCurrents
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.BookCurrent
open scoped Topology Distributions ContDiff
universe u
variable {X : Type u} [TopologicalSpace X] (A : VariableComplexAtlas X) (p : ℕ)

/-- Actual GLOBAL smooth covector localization on each compact test support
turns the literal book predicate into genuine constant beta wedge positivity.
No stronger all-local-beta source premise is inserted. -/
theorem original_source_positive_constant_beta_wedge [T2Space X]
    (T : OriginalComplexCurrent A (2*p)) (hT : OriginalSourceComplexPositive A p T)
    (i : A.Index) (beta : Fin p → ComplexModel (A.dimension i) →L[ℂ] ℂ) :
    ComplexScalarPositive (originalCurrentTarget A i)
      (constantBetaWedgeFunctional (originalCurrentTarget A i) (T.val i) beta) := by
  intro phi hphi
  let K : Compacts (ComplexModel (A.dimension i)) := ⟨tsupport phi,phi.hasCompactSupport⟩
  obtain ⟨B,hB⟩ := original_global_beta_family_constant_on_compact A i K phi.tsupport_subset p beta
  have htest : variableBetaTestCLM (originalCurrentTarget A i) (fun j => (B j).coeff i)
      (fun j => (B j).smooth i) phi=
        constantTensorTestCLM (originalCurrentTarget A i) (betaProduct beta) phi := by
    apply TestFunction.ext
    intro z
    change phi z • betaProduct (fun j => (B j).coeff i z)=phi z • betaProduct beta
    by_cases hz : z∈(K : Set _)
    · have he : (fun j => (B j).coeff i z)=beta := funext (fun j => hB j z hz)
      rw [he]
    · have hzero : phi z=0 := image_eq_zero_of_notMem_tsupport hz
      rw [hzero,zero_smul,zero_smul]
  have h := hT B i phi hphi
  change (T.val i (testOfRealCLM (originalCurrentTarget A i)
      (variableBetaTestCLM (originalCurrentTarget A i) (fun j => (B j).coeff i)
        (fun j => (B j).smooth i) phi))).im=0 ∧
    0≤(T.val i (testOfRealCLM (originalCurrentTarget A i)
      (variableBetaTestCLM (originalCurrentTarget A i) (fun j => (B j).coeff i)
        (fun j => (B j).smooth i) phi))).re at h
  rw [htest] at h
  exact h

/-- Literal book GLOBAL-beta positivity kills the entire original imaginary
current on ALL tests, using actual globalized constants, signed scalar-test
decomposition, genuine pure tensor spanning and the actual bidegree projector. -/
theorem original_source_positive_complex_im_zero [T2Space X]
    (T : OriginalComplexCurrent A (2*p)) (htype : OriginalComplexHasPureType A p T)
    (hT : OriginalSourceComplexPositive A p T) : originalCurrentIm A (2*p) T=0 := by
  apply Subtype.ext
  funext i
  ext alpha
  change currentIm (originalCurrentTarget A i) (T.val i) alpha=0
  rw [pure_type_im_factor (originalCurrentTarget A i) (T.val i) (htype i) alpha]
  apply real_current_zero_on_pure_of_constant_beta_zero (originalCurrentTarget A i)
      (currentIm (originalCurrentTarget A i) (T.val i))
  · intro beta phi
    exact positive_complex_scalar_im_eq_zero (originalCurrentTarget A i)
      (constantBetaWedgeFunctional (originalCurrentTarget A i) (T.val i) beta)
      (original_source_positive_constant_beta_wedge A p T hT i beta) phi
  · exact realPureTestProjector_mem_formSpan (originalCurrentTarget A i) alpha

/-- The literal original positive COMPLEX current is the complexification of
its internally produced actual compatible original REAL current on ALL tests. -/
theorem original_source_positive_complex_real_extension [T2Space X]
    (T : OriginalComplexCurrent A (2*p)) (htype : OriginalComplexHasPureType A p T)
    (hT : OriginalSourceComplexPositive A p T) :
    originalExtendComplexCurrent A (2*p) (originalCurrentRe A (2*p) T) 0=T := by
  have h := originalExtend_current_re_im A (2*p) T
  rwa [original_source_positive_complex_im_zero A p T htype hT] at h

/-- The ACTUAL original real source current exists uniquely; no supplied
presentation, local-beta positivity, global native atlas or output certificate. -/
theorem original_source_positive_exists_unique_real [T2Space X]
    (T : OriginalComplexCurrent A (2*p)) (htype : OriginalComplexHasPureType A p T)
    (hT : OriginalSourceComplexPositive A p T) :
    ∃! S : OriginalRealCurrent A (2*p),originalExtendComplexCurrent A (2*p) S 0=T := by
  refine ⟨originalCurrentRe A (2*p) T,
    original_source_positive_complex_real_extension A p T htype hT,?_⟩
  intro S hS
  have h := congrArg (originalCurrentRe A (2*p)) hS
  rwa [originalCurrentRe_extend] at h

/-- EVERY actual original real test has real value, as the book recalls.
This is an output, never a field of the original unrestricted complex current. -/
theorem original_source_positive_real_on_real_tests [T2Space X]
    (T : OriginalComplexCurrent A (2*p)) (htype : OriginalComplexHasPureType A p T)
    (hT : OriginalSourceComplexPositive A p T) (i : A.Index)
    (alpha : TestForm (originalCurrentTarget A i) (2*p)) :
    (T.val i (testOfRealCLM (originalCurrentTarget A i) alpha)).im=0 := by
  have h := original_source_positive_complex_im_zero A p T htype hT
  exact congrArg (fun S : OriginalRealCurrent A (2*p) => S.val i alpha) h

/-- The manufactured real current retains the ENTIRE actual original pure
type, with every real test projector equality proved internally. -/
theorem original_source_real_current_has_pure_type
    (T : OriginalComplexCurrent A (2*p)) (htype : OriginalComplexHasPureType A p T)
    (i : A.Index) (alpha : TestForm (originalCurrentTarget A i) (2*p)) :
    (originalCurrentRe A (2*p) T).val i alpha=
      (originalCurrentRe A (2*p) T).val i (realPureTestProjector (originalCurrentTarget A i) p alpha) :=
  pure_type_re_factor (originalCurrentTarget A i) (T.val i) (htype i) alpha

end SGPT.PSH.ComplexCurrentDraft
