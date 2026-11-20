import SGPT.Projective.OriginalPositiveTensorTwist
import SGPT.Projective.OriginalPositiveCurveSection

/-! ANY original line has a literal original positive-twist/power section
nonzero on ALL original components. Blueprint: original-twisted-curve-section.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov
open SGPT.Projective.NumEq.AlgebraicCurveDegree

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f 1 E L)
  (A : OriginalPositiveLine f 1 E)

include a H in
/-- Actual original ordinary twisted-power section; no nonzero or comparison certificate input. -/
theorem exists_originalTwisted_curveSection :
    ∃ M : ℕ, 0 < M ∧ ∃ d : ℕ, 0 < d ∧
      ∃ s : bundlePowerGlobalSections (bundleTensor L (bundleTensorPower A.sheaf M)) d,
        SectionNonzeroOnComponents f E s := by
  obtain ⟨M, hM, hpos⟩ := exists_positive_originalTensorTwist f 1 E a H A
  let Q : OriginalPositiveLine f 1 E :=
    { sheaf := bundleTensor L (bundleTensorPower A.sheaf M)
      atlas := pairwiseTensorAtlas a (A.atlas.tensorPower M)
      metric := H.tensorProduct (A.metric.tensorPower A.atlas M) a (A.atlas.tensorPower M)
      positive := hpos }
  obtain ⟨d, hd, s, hs⟩ := exists_originalPositivePower_curveSection f E Q
  exact ⟨M, hM, d, hd, s, hs⟩

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
