import SGPT.PSH.OriginalComplexGlobalCurrents
import SGPT.PSH.LocalPositiveComplexReality

/-! Full original atlas positive-complex-current reality: no global native
manifold, countable-atlas, connectedness or supplied real-current premise. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentDraft
open Set TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.LocalCurrents
open SGPT.PSH.VariableComplexAtlas
open scoped Topology Distributions
universe u
variable {X : Type u} [TopologicalSpace X] (A : VariableComplexAtlas X) (p : ℕ)

/-- The true original complementary bidegree uses the normalized actual
(p,p) tensor projector in EVERY original chart. No reality hypothesis. -/
def OriginalComplexHasPureType (T : OriginalComplexCurrent A (2*p)) : Prop :=
  ∀ i : A.Index,ComplexLocalHasPureType (originalCurrentTarget A i) (T.val i)

/-- Literal original smooth beta weak positivity on all actual atlas charts. -/
def OriginalComplexWeakPositive (T : OriginalComplexCurrent A (2*p)) : Prop :=
  ∀ i : A.Index,ComplexLocalWeakPositive (originalCurrentTarget A i) (T.val i)

/-- ACTUAL original pure complementary complex currents as a subtype of
unrestricted complex-linear LF currents, never a supplied real presentation. -/
abbrev OriginalPureComplexCurrent :=
  {T : OriginalComplexCurrent A (2*p) // OriginalComplexHasPureType A p T}

/-- The positive source current's entire imaginary current vanishes globally,
by the actual local decomposable span proof at EACH original chart. -/
theorem original_positive_pure_complex_im_zero (T : OriginalComplexCurrent A (2*p))
    (htype : OriginalComplexHasPureType A p T) (hpos : OriginalComplexWeakPositive A p T) :
    originalCurrentIm A (2*p) T=0 := by
  apply Subtype.ext
  funext i
  exact positive_pure_complex_current_im_eq_zero (originalCurrentTarget A i)
    (T.val i) (htype i) (hpos i)

/-- Actual source realness on EVERY original real test, PRODUCED from weak
positivity. It was not a field of the initial complex current object. -/
theorem original_positive_pure_complex_real_on_real_tests
    (T : OriginalComplexCurrent A (2*p)) (htype : OriginalComplexHasPureType A p T)
    (hpos : OriginalComplexWeakPositive A p T) (i : A.Index)
    (alpha : TestForm (originalCurrentTarget A i) (2*p)) :
    (T.val i (testOfRealCLM (originalCurrentTarget A i) alpha)).im=0 := by
  have h := original_positive_pure_complex_im_zero A p T htype hpos
  exact congrArg (fun S : OriginalRealCurrent A (2*p) => S.val i alpha) h

/-- The internally produced GENUINE original compatible real current
complexifies to the full original positive complex current on ALL tests. -/
theorem original_positive_pure_complex_is_real_extension
    (T : OriginalComplexCurrent A (2*p)) (htype : OriginalComplexHasPureType A p T)
    (hpos : OriginalComplexWeakPositive A p T) :
    originalExtendComplexCurrent A (2*p) (originalCurrentRe A (2*p) T) 0=T := by
  have h := originalExtend_current_re_im A (2*p) T
  rwa [original_positive_pure_complex_im_zero A p T htype hpos] at h

/-- Existence and UNIQUENESS of the actual original compatible real current;
no real current, local reality flag, native atlas or output is an assumption. -/
theorem original_positive_pure_complex_exists_unique_real
    (T : OriginalComplexCurrent A (2*p)) (htype : OriginalComplexHasPureType A p T)
    (hpos : OriginalComplexWeakPositive A p T) :
    ∃! S : OriginalRealCurrent A (2*p),originalExtendComplexCurrent A (2*p) S 0=T := by
  refine ⟨originalCurrentRe A (2*p) T,
    original_positive_pure_complex_is_real_extension A p T htype hpos,?_⟩
  intro S hS
  have h := congrArg (originalCurrentRe A (2*p)) hS
  rwa [originalCurrentRe_extend] at h

/-- Full current readback on EVERY original complex tensor test. -/
theorem original_positive_pure_complex_all_test_readback
    (T : OriginalComplexCurrent A (2*p)) (htype : OriginalComplexHasPureType A p T)
    (hpos : OriginalComplexWeakPositive A p T) (i : A.Index)
    (alpha : ComplexTestForm (originalCurrentTarget A i) (2*p)) :
    T.val i alpha=
      (originalCurrentRe A (2*p) T).val i (testReCLM (originalCurrentTarget A i) alpha)+
        Complex.I*((originalCurrentRe A (2*p) T).val i
          (testImCLM (originalCurrentTarget A i) alpha) : ℂ) := by
  have h := congrArg (fun G : OriginalComplexCurrent A (2*p) => G.val i alpha)
    (original_positive_pure_complex_is_real_extension A p T htype hpos)
  simpa [originalExtendComplexCurrent,extendComplexCurrent_apply] using h.symm

end SGPT.PSH.ComplexCurrentDraft
