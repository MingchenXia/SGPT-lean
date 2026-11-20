import SGPT.Projective.NumEqCurves
import SGPT.Toric.NativeChernPullback
import SGPT.Foundations.Analysis.Pending.NefMixedMass

/-! The EXISTING actual degreeAlong is nonnegative for a genuinely native
nef form on ANY actual compact smooth curve map, retaining all components.
Blueprint: native-nef-curve-degree.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses NefMixedMass
open SGPT.Projective.NumEq
open scoped Manifold ContDiff
variable {n : ℕ} {M C : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace C] [ChartedSpace (ComplexModel 1) C]
  [IsComplexManifold 1 C] [CompactSpace C]

/-- Native smooth-epsilon nefness implies nonnegative actual curve degree.
No connectedness, nonempty source, map injectivity or degree comparison. -/
theorem degreeAlong_nonneg_of_nativeNef (omega : KahlerBackground n M)
    (κC : KahlerBackground 1 C) {g : C → M}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel n) ∞ g)
    (θ : ClosedRealOneOneForm n M) (hθ : NefWithRespectTo omega θ) :
    0 ≤ degreeAlong κC hg θ := by
  let : MeasurableSpace C := borel C
  let : BorelSpace C := ⟨rfl⟩
  apply slotIntegral_nonneg_of_nef κC
  intro i
  exact SGPT.Toric.F1IntersectionDraft.nefWithRespectTo_holomorphicPullbackAnyDimension hg omega κC hθ
end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
