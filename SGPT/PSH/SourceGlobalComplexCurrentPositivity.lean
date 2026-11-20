import SGPT.PSH.OriginalGlobalOneZeroForms
import SGPT.PSH.OriginalComplexGlobalCurrents
import SGPT.PSH.SmoothVariableBetaTests
import SGPT.PSH.PositiveComplexScalarReality

/-! LITERAL GLOBAL smooth-beta source positivity with actual LF wedge
distributions and internally produced regular positive measures. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentDraft
open Set Filter TopologicalSpace MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas
open scoped Topology Distributions ContDiff
universe u
variable {X : Type u} [TopologicalSpace X] (A : VariableComplexAtlas X) (p : ℕ)

/-- ACTUAL chart distribution of the original current wedged with a family
of GENUINE GLOBAL smooth (1,0) forms. Full LF continuity is produced by the
actual variable-beta testing map; source forms are not just local families. -/
def originalGlobalBetaWedgeFunctional (T : OriginalComplexCurrent A (2*p))
    (beta : Fin p → OriginalGlobalOneZeroForm A) (i : A.Index) :
    𝓓(originalCurrentTarget A i,ℝ) →L[ℝ] ℂ :=
  ((T.val i).restrictScalars ℝ).comp
    ((testOfRealCLM (originalCurrentTarget A i)).comp
      (variableBetaTestCLM (originalCurrentTarget A i) (fun j => (beta j).coeff i)
        (fun j => (beta j).smooth i)))

/-- LITERAL source GLOBAL-beta weak positivity at complementary degree 2p.
Only positive scalar-test values are assumed real/nonnegative; reality of
the original complex current is not part of the object or the predicate. -/
def OriginalSourceComplexPositive (T : OriginalComplexCurrent A (2*p)) : Prop :=
  ∀ beta : Fin p → OriginalGlobalOneZeroForm A,∀ i : A.Index,
    ComplexScalarPositive (originalCurrentTarget A i)
      (originalGlobalBetaWedgeFunctional A p T beta i)

/-- Full literal physical wedge distribution readback on EVERY scalar test. -/
theorem originalGlobalBetaWedgeFunctional_apply (T : OriginalComplexCurrent A (2*p))
    (beta : Fin p → OriginalGlobalOneZeroForm A) (i : A.Index)
    (phi : 𝓓(originalCurrentTarget A i,ℝ)) :
    originalGlobalBetaWedgeFunctional A p T beta i phi=
      T.val i (testOfRealCLM (originalCurrentTarget A i)
        (variableBetaTestCLM (originalCurrentTarget A i) (fun j => (beta j).coeff i)
          (fun j => (beta j).smooth i) phi)) := rfl

/-- ACTUAL regular locally finite positive measure of EVERY literal global
source beta wedge, with exact equality on ALL signed smooth scalar tests.
No wedge measure or real distribution output is an assumption. -/
theorem original_source_positive_actual_wedge_measure
    (T : OriginalComplexCurrent A (2*p)) (hT : OriginalSourceComplexPositive A p T)
    (beta : Fin p → OriginalGlobalOneZeroForm A) (i : A.Index) :
    ∃ nu : Measure (originalCurrentTarget A i),nu.Regular ∧ IsLocallyFiniteMeasure nu ∧
      ∀ phi : 𝓓(originalCurrentTarget A i,ℝ),
        originalGlobalBetaWedgeFunctional A p T beta i phi=((∫ x : originalCurrentTarget A i,phi x ∂nu : ℝ) : ℂ) := by
  obtain ⟨S,hS,hread⟩ := positive_complex_scalar_exists_real_distribution
    (originalCurrentTarget A i) (originalGlobalBetaWedgeFunctional A p T beta i) (hT beta i)
  obtain ⟨nu,hnu,hloc,hint⟩ := hS.exists_regular_measure
  refine ⟨nu,hnu,hloc,fun phi => ?_⟩
  rw [hread phi,← hint phi]

/-- The source predicate is EQUIVALENT to actual regular positive wedge
measure representations for EVERY global beta family and original chart. -/
theorem original_source_positive_iff_actual_wedge_measures
    (T : OriginalComplexCurrent A (2*p)) :
    OriginalSourceComplexPositive A p T ↔
      ∀ beta : Fin p → OriginalGlobalOneZeroForm A,∀ i : A.Index,
        ∃ nu : Measure (originalCurrentTarget A i),nu.Regular ∧ IsLocallyFiniteMeasure nu ∧
          ∀ phi : 𝓓(originalCurrentTarget A i,ℝ),
            originalGlobalBetaWedgeFunctional A p T beta i phi=
              ((∫ x : originalCurrentTarget A i,phi x ∂nu : ℝ) : ℂ) := by
  constructor
  · exact original_source_positive_actual_wedge_measure A p T
  · intro h beta i phi hphi
    obtain ⟨nu,_,_,hread⟩ := h beta i
    rw [hread phi]
    constructor
    · simp
    · simp only [Complex.ofReal_re]
      exact integral_nonneg (fun x => hphi x)

end SGPT.PSH.ComplexCurrentDraft
