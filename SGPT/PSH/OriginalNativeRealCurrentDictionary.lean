import SGPT.PSH.OriginalComplexGlobalCurrents
import SGPT.PSH.BookCurrentPositivity

/-! Actual original/native REAL-current dictionary at genuine complementary
degrees. Native hypotheses are ONLY an additional comparison context. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentBridge
open TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.LocalCurrents
open SGPT.Foundations.Analysis.Pending.CanonicalComplementaryCurrentTests
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.ComplexCurrentDraft
open scoped Distributions
universe u

/-- Entire original real LF current degree transport, with no output data. -/
def originalRealCurrentDegreeEquiv {X : Type u} [TopologicalSpace X]
    (A : VariableComplexAtlas X) {q r : ℕ} (h : q=r) :
    OriginalRealCurrent A q ≃ OriginalRealCurrent A r := by
  subst r
  exact Equiv.refl _

/-- Every ACTUAL chart test retains its full degree-transport pairing. -/
theorem originalRealCurrentDegreeEquiv_apply {X : Type u} [TopologicalSpace X]
    (A : VariableComplexAtlas X) {q r : ℕ} (h : q=r) (S : OriginalRealCurrent A q)
    (i : A.Index) (alpha : TestForm (originalCurrentTarget A i) r) :
    (originalRealCurrentDegreeEquiv A h S).val i alpha=
      S.val i (castTestDegree h.symm alpha) := by
  subst r
  rfl

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] (k : CurrentDegree n)

/-- Exact comparison of ACTUAL compatible LF chart currents on the native
manifold's SAME original atlas. Both full overlap fields are proved/read back;
no native current or compatibility output certificate is supplied. -/
def originalNativeRealCurrentExactEquiv :
    OriginalRealCurrent (ofFixedModel n M) (Module.finrank ℝ (ComplexModel n)-k.val) ≃
      GlobalCurrent n M k where
  toFun S := ⟨S.val,S.property⟩
  invFun S := ⟨S.val,S.property⟩
  left_inv S := by apply Subtype.ext; rfl
  right_inv S := by apply Subtype.ext; rfl

/-- Actual original real currents at any equal complementary degree PRODUCE
existing native currents, with full compact LF continuity and tensor overlap. -/
def nativeRealCurrentOfOriginal {q : ℕ}
    (h : q=Module.finrank ℝ (ComplexModel n)-k.val)
    (S : OriginalRealCurrent (ofFixedModel n M) q) : GlobalCurrent n M k :=
  originalNativeRealCurrentExactEquiv k (originalRealCurrentDegreeEquiv (ofFixedModel n M) h S)

/-- EVERY native full test has the literal original current value, including
true degree reindexing. No mere proposition/flag replaces the current object. -/
theorem nativeRealCurrentOfOriginal_inChart {q : ℕ}
    (h : q=Module.finrank ℝ (ComplexModel n)-k.val)
    (S : OriginalRealCurrent (ofFixedModel n M) q) (e : ComplexChart n M)
    (alpha : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel n)-k.val)) :
    (nativeRealCurrentOfOriginal k h S).inChart e alpha=
      S.val e (castTestDegree h.symm alpha) := by
  subst q
  rfl

/-- The genuine current correspondence is bijective on ALL real LF tests. -/
def originalNativeRealCurrentEquiv {q : ℕ}
    (h : q=Module.finrank ℝ (ComplexModel n)-k.val) :
    OriginalRealCurrent (ofFixedModel n M) q ≃ GlobalCurrent n M k :=
  (originalRealCurrentDegreeEquiv (ofFixedModel n M) h).trans (originalNativeRealCurrentExactEquiv k)

end SGPT.PSH.ComplexCurrentBridge
