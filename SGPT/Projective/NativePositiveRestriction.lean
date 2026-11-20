import SGPT.Toric.NativeChernPullback
import SGPT.Foundations.Analysis.Pending.SubmanifoldKahlerRestriction

/-! Actual positive native bundle restrictions, preserving original physical
fibers, metrics, and exact own curvature. Geometry only; no cycle certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections
open Set Bundle
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric SGPT.PSH.GlobalL2
open SGPT.Toric.F1IntersectionDraft

/-- Ordinary actual positive native bundle data. Its fields are the original
physical bundle, smooth metric and own closed Chern form, not an embedding
or intersection conclusion. All final producers consume these native objects. -/
structure NativePositiveLine (n : ℕ) (X : Type) [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] where
  bundle : HermitianHolomorphicLineBundle.{0,0} n X
  smooth : IsSourceSmoothHermitianMetric bundle
  curvature : ClosedRealOneOneForm n X
  own : IsOwnFirstChernForm bundle curvature
  positive : curvature.val.IsKahler

namespace NativePositiveLine
variable {n k : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The original positive own Chern form is a genuine original background. -/
def background (L : NativePositiveLine n X) : KahlerBackground n X :=
  ⟨L.curvature, L.positive⟩

/-- Restrict the SAME actual physical native bundle to an actual regular
complex submanifold. The original form pullback is its exact own Chern
curvature; positivity follows from the actual coordinate differential. -/
def restrict (L : NativePositiveLine n X) {W : Set X} (hk : k ≤ n)
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k) :
    let := SubmanifoldChartedSpace.chartedSpace hk hW
    let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW
    NativePositiveLine k W := by
  let := SubmanifoldChartedSpace.chartedSpace hk hW
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW
  let f : ContMDiffMap 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) W X ∞ :=
    ⟨Subtype.val, SubmanifoldChartedSpace.contMDiff_val hk hW⟩
  let P := nativeHolomorphicPullbackBundle L.bundle f
  let hP := nativeHolomorphicPullback_smooth L.bundle f L.smooth
  let theta := ClosedRealOneOneForm.pullback f.contMDiff L.curvature
  have hgeo := nativeHolomorphicPullback_firstChern_geometrically
    L.bundle f L.smooth L.curvature L.own
  refine ⟨P, hP, theta, ?_, SubmanifoldKahlerRestriction.isKahler_pullback hk hW L.curvature L.positive⟩
  intro c e z hz he
  exact (hgeo c hz).symm.trans (sourceNativeFirstChernForm_isOwn P hP c e z hz he)

/-- The manufactured restricted bundle is LITERALLY the actual native
pullback with inherited original physical fiber norms. -/
theorem restrict_bundle (L : NativePositiveLine n X) {W : Set X} (hk : k ≤ n)
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k) :
    let := SubmanifoldChartedSpace.chartedSpace hk hW
    let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW
    (L.restrict hk hW).bundle = nativeHolomorphicPullbackBundle L.bundle
      ⟨Subtype.val, SubmanifoldChartedSpace.contMDiff_val hk hW⟩ := rfl

/-- Its own original curvature is the LITERAL original closed-form pullback. -/
theorem restrict_curvature (L : NativePositiveLine n X) {W : Set X} (hk : k ≤ n)
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k) :
    let := SubmanifoldChartedSpace.chartedSpace hk hW
    let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW
    (L.restrict hk hW).curvature = ClosedRealOneOneForm.pullback
      (SubmanifoldChartedSpace.contMDiff_val hk hW) L.curvature := rfl

end NativePositiveLine
end SGPT.Projective.NumEq.CompleteIntersections
