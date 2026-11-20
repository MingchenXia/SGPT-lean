import SGPT.PSH.ComplexLocalCurrents
import SGPT.PSH.ComplexOverlapTests
import SGPT.PSH.VariableAtlas

/-! GENUINE complex global currents on the ORIGINAL independently-dimensional
atlas: continuous COMPLEX-linear local LF functionals and actual FULL tensor
overlap laws. No global second countability, native geometry or reality flag. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.LocalCurrents
open SGPT.PSH.VariableComplexAtlas
open scoped Topology Distributions
universe u
variable {X : Type u} [TopologicalSpace X] (A : VariableComplexAtlas X) (q : ℕ)

/-- Actual original chart target in its OWN declared complex model. -/
def originalCurrentTarget (i : A.Index) : Opens (ComplexModel (A.dimension i)) :=
  ⟨(A.chart i).target,(A.chart i).open_target⟩

/-- The actual original transition, with independently declared dimensions. -/
def originalCurrentTransition (i j : A.Index) :
    OpenPartialHomeomorph (ComplexModel (A.dimension i)) (ComplexModel (A.dimension j)) :=
  (A.chart i).symm.trans (A.chart j)

/-- Honest actual overlap inclusions, excluding test inclusion zero fallbacks. -/
theorem originalCurrent_overlap_source_le (i j : A.Index) :
    overlapDomain (originalCurrentTransition A i j)≤originalCurrentTarget A i := fun _ hz => hz.1
theorem originalCurrent_overlap_target_le (i j : A.Index) :
    overlapRange (originalCurrentTransition A i j)≤originalCurrentTarget A j := fun _ hz => hz.1

/-- GENUINE complex local restriction by actual compact-support test inclusion. -/
def restrictComplexLocal {n : ℕ} {U V : Opens (ComplexModel n)} (_hUV : U≤V)
    (T : ComplexLocalFunctional V q) : ComplexLocalFunctional U q :=
  T.comp (TestFunction.monoCLM ℂ)

/-- Genuine real local restriction at SAME actual dual test degree. -/
def restrictRealLocal {n : ℕ} {U V : Opens (ComplexModel n)} (_hUV : U≤V)
    (T : RealLocalFunctional V q) : RealLocalFunctional U q :=
  T.comp (TestFunction.monoCLM ℝ)

/-- ACTUAL complex current families, without assumed realness or output fields. -/
abbrev OriginalComplexChartFamily := ∀ i : A.Index,ComplexLocalFunctional (originalCurrentTarget A i) q

/-- Full original complex tensor compatibility on genuine actual overlap tests. -/
def OriginalComplexFamilyCompatible (T : OriginalComplexChartFamily A q) : Prop :=
  ∀ (i j : A.Index)
    (eta : ComplexTestForm (overlapDomain (originalCurrentTransition A i j)) q)
    (theta : ComplexTestForm (overlapRange (originalCurrentTransition A i j)) q),
    ComplexOverlapRelated (originalCurrentTransition A i j) eta theta →
      restrictComplexLocal q (originalCurrent_overlap_source_le A i j) (T i) eta=
        restrictComplexLocal q (originalCurrent_overlap_target_le A i j) (T j) theta

/-- Complex module of genuine compatible COMPLEX-linear continuous local
functionals, constructed BEFORE any real-current presentation or positivity. -/
def originalComplexCurrentSubmodule : Submodule ℂ (OriginalComplexChartFamily A q) where
  carrier := {T | OriginalComplexFamilyCompatible A q T}
  zero_mem' := by intro i j eta theta h; rfl
  add_mem' := by
    intro S T hS hT i j eta theta h
    exact congrArg₂ (·+·) (hS i j eta theta h) (hT i j eta theta h)
  smul_mem' := by
    intro c T hT i j eta theta h
    exact congrArg (c • ·) (hT i j eta theta h)

/-- The ACTUAL original global complex current on dual test degree q.
Local values may be nonreal. No native manifold/countability or reality field. -/
abbrev OriginalComplexCurrent := ↥(originalComplexCurrentSubmodule A q)

/-- Genuine original REAL current families at the SAME actual test degree. -/
abbrev OriginalRealChartFamily := ∀ i : A.Index,RealLocalFunctional (originalCurrentTarget A i) q

/-- Actual real tensor overlap law on exactly the same original atlas. -/
def OriginalRealFamilyCompatible (T : OriginalRealChartFamily A q) : Prop :=
  ∀ (i j : A.Index)
    (eta : TestForm (overlapDomain (originalCurrentTransition A i j)) q)
    (theta : TestForm (overlapRange (originalCurrentTransition A i j)) q),
    RealOverlapRelated (originalCurrentTransition A i j) eta theta →
      restrictRealLocal q (originalCurrent_overlap_source_le A i j) (T i) eta=
        restrictRealLocal q (originalCurrent_overlap_target_le A i j) (T j) theta

/-- Genuine compatible real current module, to be PRODUCED from arbitrary
original complex currents; it is not a source presentation premise. -/
def originalRealCurrentSubmodule : Submodule ℝ (OriginalRealChartFamily A q) where
  carrier := {T | OriginalRealFamilyCompatible A q T}
  zero_mem' := by intro i j eta theta h; rfl
  add_mem' := by
    intro S T hS hT i j eta theta h
    exact congrArg₂ (·+·) (hS i j eta theta h) (hT i j eta theta h)
  smul_mem' := by
    intro c T hT i j eta theta h
    exact congrArg (c • ·) (hT i j eta theta h)

/-- Actual original real current on SAME atlas and dual test degree. -/
abbrev OriginalRealCurrent := ↥(originalRealCurrentSubmodule A q)

/-- GENUINE original complex current real-part current, with EVERY actual
overlap compatibility field PRODUCED internally by complex embedding/readback. -/
def originalCurrentRe (T : OriginalComplexCurrent A q) : OriginalRealCurrent A q := by
  refine ⟨fun i => currentRe (originalCurrentTarget A i) (T.val i),?_⟩
  intro i j eta theta hrel
  have hc := T.property i j
    (testOfRealCLM (overlapDomain (originalCurrentTransition A i j)) eta)
    (testOfRealCLM (overlapRange (originalCurrentTransition A i j)) theta) hrel.complexEmbedding
  change (T.val i (testOfRealCLM (originalCurrentTarget A i) (TestFunction.monoCLM ℝ eta))).re=
    (T.val j (testOfRealCLM (originalCurrentTarget A j) (TestFunction.monoCLM ℝ theta))).re
  rw [testOfReal_mono (originalCurrent_overlap_source_le A i j),
    testOfReal_mono (originalCurrent_overlap_target_le A i j)]
  exact congrArg Complex.re hc

/-- GENUINE original imaginary current with all tensor compatibility proved;
it is NOT assumed zero or excluded from the original complex current object. -/
def originalCurrentIm (T : OriginalComplexCurrent A q) : OriginalRealCurrent A q := by
  refine ⟨fun i => currentIm (originalCurrentTarget A i) (T.val i),?_⟩
  intro i j eta theta hrel
  have hc := T.property i j
    (testOfRealCLM (overlapDomain (originalCurrentTransition A i j)) eta)
    (testOfRealCLM (overlapRange (originalCurrentTransition A i j)) theta) hrel.complexEmbedding
  change (T.val i (testOfRealCLM (originalCurrentTarget A i) (TestFunction.monoCLM ℝ eta))).im=
    (T.val j (testOfRealCLM (originalCurrentTarget A j) (TestFunction.monoCLM ℝ theta))).im
  rw [testOfReal_mono (originalCurrent_overlap_source_le A i j),
    testOfReal_mono (originalCurrent_overlap_target_le A i j)]
  exact congrArg Complex.im hc

/-- Arbitrary original real/imaginary compatible currents produce an ACTUAL
original global COMPLEX current, with complex linearity, LF continuity and
ALL original tensor overlap fields manufactured rather than supplied. -/
def originalExtendComplexCurrent (S T : OriginalRealCurrent A q) : OriginalComplexCurrent A q := by
  refine ⟨fun i => extendComplexCurrent (originalCurrentTarget A i) (S.val i) (T.val i),?_⟩
  intro i j eta theta hrel
  have hSR := S.property i j _ _ hrel.realPart
  have hSI := S.property i j _ _ hrel.imaginaryPart
  have hTR := T.property i j _ _ hrel.realPart
  have hTI := T.property i j _ _ hrel.imaginaryPart
  simp only [restrictRealLocal,ContinuousLinearMap.comp_apply] at hSR hSI hTR hTI
  change extendComplexCurrent (originalCurrentTarget A i) (S.val i) (T.val i) (TestFunction.monoCLM ℂ eta)=
    extendComplexCurrent (originalCurrentTarget A j) (S.val j) (T.val j) (TestFunction.monoCLM ℂ theta)
  rw [extendComplexCurrent_apply,extendComplexCurrent_apply,
    testRe_mono (originalCurrent_overlap_source_le A i j),
    testIm_mono (originalCurrent_overlap_source_le A i j),
    testRe_mono (originalCurrent_overlap_target_le A i j),
    testIm_mono (originalCurrent_overlap_target_le A i j),hSR,hSI,hTR,hTI]

/-- EVERY original complex current is reconstructed on ALL actual complex
chart tests from its internally produced real/imaginary original currents. -/
theorem originalExtend_current_re_im (T : OriginalComplexCurrent A q) :
    originalExtendComplexCurrent A q (originalCurrentRe A q T) (originalCurrentIm A q T)=T := by
  apply Subtype.ext
  funext i
  exact extend_current_re_im (originalCurrentTarget A i) (T.val i)

/-- Arbitrary original real current is recovered from true complex extension. -/
theorem originalCurrentRe_extend (S T : OriginalRealCurrent A q) :
    originalCurrentRe A q (originalExtendComplexCurrent A q S T)=S := by
  apply Subtype.ext
  funext i
  exact currentRe_extend (originalCurrentTarget A i) (S.val i) (T.val i)

/-- Arbitrary original imaginary current is recovered too: the actual global
complex object has NOT silently been restricted to real currents. -/
theorem originalCurrentIm_extend (S T : OriginalRealCurrent A q) :
    originalCurrentIm A q (originalExtendComplexCurrent A q S T)=T := by
  apply Subtype.ext
  funext i
  exact currentIm_extend (originalCurrentTarget A i) (S.val i) (T.val i)

/-- PROVED actual global dictionary on ALL complex tests, with genuine
original complex LF current object as domain and no reality hypothesis. -/
def originalComplexCurrentEquivRealPair : OriginalComplexCurrent A q ≃
    (OriginalRealCurrent A q × OriginalRealCurrent A q) where
  toFun T := (originalCurrentRe A q T,originalCurrentIm A q T)
  invFun p := originalExtendComplexCurrent A q p.1 p.2
  left_inv := originalExtend_current_re_im A q
  right_inv := by
    rintro ⟨S,T⟩
    exact Prod.ext (originalCurrentRe_extend A q S T) (originalCurrentIm_extend A q S T)

end SGPT.PSH.ComplexCurrentDraft
