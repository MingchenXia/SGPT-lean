import SGPT.PSH.BetaProductNaturality
import SGPT.PSH.SourceGlobalComplexCurrentPositivity

/-! The actual local beta wedge distributions form the SAME genuine global
scalar current, with exact compact overlap and positive measure readbacks. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentDraft
open Set Filter TopologicalSpace MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.LocalCurrents
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.BookCurrent
open scoped Topology Distributions ContDiff

/-- Actual scalar LF inclusion excludes the library zero fallback. -/
theorem scalar_test_inclusion_apply {n : ℕ} {U V : Opens (ComplexModel n)} (hUV : U≤V)
    (phi : 𝓓(U,ℝ)) (z : ComplexModel n) : (TestFunction.monoCLM ℝ phi : 𝓓(V,ℝ)) z=phi z := by
  have h := TestFunction.monoCLM_apply (𝕜 := ℝ) (n₂ := ⊤) (Ω₂ := V) phi
  simpa only [le_refl,hUV,and_self,↓reduceIte] using congrFun h z

/-- Actual tensor beta testing commutes with genuine compact-test inclusion. -/
theorem variableBetaTest_mono {n p : ℕ} {U V : Opens (ComplexModel n)} (hUV : U≤V)
    (beta : Fin p → ComplexModel n → ComplexModel n →L[ℂ] ℂ)
    (hb : ∀ a,ContDiffOn ℝ ∞ (beta a) (V : Set (ComplexModel n))) (phi : 𝓓(U,ℝ)) :
    variableBetaTestCLM V beta hb (TestFunction.monoCLM ℝ phi)=
      (TestFunction.monoCLM ℝ (variableBetaTestCLM U beta (fun a => (hb a).mono hUV) phi) : TestForm V (2*p)) := by
  apply TestFunction.ext
  intro z
  rw [variableBetaTestCLM_apply,scalar_test_inclusion_apply hUV,
    testForm_inclusion_apply hUV,variableBetaTestCLM_apply]

universe u
variable {X : Type u} [TopologicalSpace X] (A : VariableComplexAtlas X) (p : ℕ)

/-- ENTIRE compact overlap law for the ACTUAL global beta wedge distributions.
The source forms' genuine tensor compatibility and original current overlap
law manufacture this identity; no compatible measure/output flag is assumed. -/
theorem originalGlobalBetaWedgeFunctional_overlap
    (T : OriginalComplexCurrent A (2*p)) (beta : Fin p → OriginalGlobalOneZeroForm A)
    (i j : A.Index)
    (phi : 𝓓(overlapDomain (originalCurrentTransition A i j),ℝ))
    (psi : 𝓓(overlapRange (originalCurrentTransition A i j),ℝ))
    (hscalar : ∀ z,z∈(originalCurrentTransition A i j).source →
      phi z=psi (originalCurrentTransition A i j z)) :
    originalGlobalBetaWedgeFunctional A p T beta i (TestFunction.monoCLM ℝ phi)=
      originalGlobalBetaWedgeFunctional A p T beta j (TestFunction.monoCLM ℝ psi) := by
  let U := overlapDomain (originalCurrentTransition A i j)
  let V := overlapRange (originalCurrentTransition A i j)
  let eta := variableBetaTestCLM U (fun a => (beta a).coeff i)
    (fun a => ((beta a).smooth i).mono (originalCurrent_overlap_source_le A i j)) phi
  let theta := variableBetaTestCLM V (fun a => (beta a).coeff j)
    (fun a => ((beta a).smooth j).mono (originalCurrent_overlap_target_le A i j)) psi
  have hrel : RealOverlapRelated (originalCurrentTransition A i j) eta theta := by
    intro z hz v
    change (phi z • betaProduct (fun a => (beta a).coeff i z)) v=
      (psi (originalCurrentTransition A i j z) •
        betaProduct (fun a => (beta a).coeff j (originalCurrentTransition A i j z)))
          (fun a => fderiv ℝ (originalCurrentTransition A i j) z (v a))
    rw [hscalar z hz,original_global_betaProduct_compatible A beta i j hz]
    rfl
  have h := T.property i j (testOfRealCLM U eta) (testOfRealCLM V theta) hrel.complexEmbedding
  change T.val i (testOfRealCLM (originalCurrentTarget A i)
      (variableBetaTestCLM (originalCurrentTarget A i) (fun a => (beta a).coeff i)
        (fun a => (beta a).smooth i) (TestFunction.monoCLM ℝ phi)))=
    T.val j (testOfRealCLM (originalCurrentTarget A j)
      (variableBetaTestCLM (originalCurrentTarget A j) (fun a => (beta a).coeff j)
        (fun a => (beta a).smooth j) (TestFunction.monoCLM ℝ psi)))
  have hi := variableBetaTest_mono (originalCurrent_overlap_source_le A i j)
    (fun a => (beta a).coeff i) (fun a => (beta a).smooth i) phi
  have hj := variableBetaTest_mono (originalCurrent_overlap_target_le A i j)
    (fun a => (beta a).coeff j) (fun a => (beta a).smooth j) psi
  have hie := (congrArg (testOfRealCLM (originalCurrentTarget A i)) hi).trans
    (testOfReal_mono (originalCurrent_overlap_source_le A i j) eta)
  have hje := (congrArg (testOfRealCLM (originalCurrentTarget A j)) hj).trans
    (testOfReal_mono (originalCurrent_overlap_target_le A i j) theta)
  change T.val i (TestFunction.monoCLM ℂ (testOfRealCLM U eta))=
    T.val j (TestFunction.monoCLM ℂ (testOfRealCLM V theta)) at h
  exact (congrArg (T.val i) hie).trans (h.trans (congrArg (T.val j) hje).symm)

/-- Standard actual original complex-valued scalar distributions, together
with their genuine coordinate overlap law on compact scalar tests. -/
structure OriginalGlobalScalarCurrent where
  inChart : ∀ i : A.Index,𝓓(originalCurrentTarget A i,ℝ) →L[ℝ] ℂ
  overlap : ∀ (i j : A.Index)
    (phi : 𝓓(overlapDomain (originalCurrentTransition A i j),ℝ))
    (psi : 𝓓(overlapRange (originalCurrentTransition A i j),ℝ)),
    (∀ z,z∈(originalCurrentTransition A i j).source →
      phi z=psi (originalCurrentTransition A i j z)) →
      inChart i (TestFunction.monoCLM ℝ phi)=inChart j (TestFunction.monoCLM ℝ psi)

/-- The original source T wedge i beta1 wedge bar(beta1) ... is an ACTUAL
global scalar current, with continuous chart functionals and full overlap
compatibility internally produced, before positivity or measure assumptions. -/
def originalGlobalBetaWedgeCurrent (T : OriginalComplexCurrent A (2*p))
    (beta : Fin p → OriginalGlobalOneZeroForm A) : OriginalGlobalScalarCurrent A where
  inChart := originalGlobalBetaWedgeFunctional A p T beta
  overlap := originalGlobalBetaWedgeFunctional_overlap A p T beta

/-- Every chart of the SAME actual global wedge current is a genuine regular
locally finite positive measure, with full signed scalar-test readback. -/
theorem originalGlobalBetaWedgeCurrent_positive_measure
    (T : OriginalComplexCurrent A (2*p)) (hT : OriginalSourceComplexPositive A p T)
    (beta : Fin p → OriginalGlobalOneZeroForm A) (i : A.Index) :
    ∃ nu : Measure (originalCurrentTarget A i),nu.Regular ∧ IsLocallyFiniteMeasure nu ∧
      ∀ phi : 𝓓(originalCurrentTarget A i,ℝ),
        (originalGlobalBetaWedgeCurrent A p T beta).inChart i phi=
          ((∫ x : originalCurrentTarget A i,phi x ∂nu : ℝ) : ℂ) :=
  original_source_positive_actual_wedge_measure A p T hT beta i

end SGPT.PSH.ComplexCurrentDraft
