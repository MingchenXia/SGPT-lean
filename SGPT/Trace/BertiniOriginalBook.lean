import SGPT.Trace.BertiniNativeBookBertini
import SGPT.Trace.BertiniUniversalProjectivePositive
import SGPT.Trace.BertiniZeroDimension

/-! The complete original analytic Bertini theorem, with its raw book weight. -/
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
namespace SGPT.Trace.Bertini
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

/-- Full original `thm:Bert`; the actual projective input produces its own positive bundle. -/
theorem analyticBertini : AnalyticBertiniStatement := by
  intro n N X _ _ _ _ _ hproj hN p hp φ hφ
  cases n with
  | zero => exact coPluripolar_bertiniGoodSet_zero_dim p hp hN φ
  | succ d =>
    cases N with
    | zero => omega
    | succ k =>
      obtain ⟨G, hG, hGpos⟩ :=
        BertiniUniversal.exists_actual_positive_native_bundle_of_book_projective hproj
      let p' : ContMDiffMap 𝓘(ℂ, ComplexModel (d+1)) 𝓘(ℂ, ComplexModel (k+1))
          X (ComplexProjectiveSpace (k+1)) ∞ := ⟨p, hp⟩
      exact coPluripolar_book_bertiniGoodSet_of_raw_positive_native p' G hG hGpos φ hφ

end SGPT.Trace.Bertini
