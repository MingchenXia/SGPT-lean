import SGPT.Projective.SourceHyperplaneChernClass

/-! Genuine actual native bundle-isomorphism and self-pullback Chern CLASS naturality. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.Projective.HyperplaneClassNext

open Set Bundle
open SGPT.Toric.F1IntersectionDraft
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric
open SGPT.PSH.LineBundleMetric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

theorem nativeFiberEquiv_firstChernClass
    (E F : HermitianHolomorphicLineBundle.{0,0} n X)
    (hE : IsSourceSmoothHermitianMetric E) (hF : IsSourceSmoothHermitianMetric F)
    (e : (x : X) → E.Fiber x ≃ₗ[ℂ] F.Fiber x)
    (he : ContMDiff ((𝓘(ℂ, ComplexModel n)).prod (𝓘(ℂ, ℂ)))
      ((𝓘(ℂ, ComplexModel n)).prod (𝓘(ℂ, ℂ))) ∞
      (fun y : TotalSpace ℂ E.Fiber =>
        (⟨y.proj, e y.proj y.snd⟩ : TotalSpace ℂ F.Fiber))) :
    RealBottChern.ofRepresentative (sourceNativeFirstChernForm E hE) =
      RealBottChern.ofRepresentative (sourceNativeFirstChernForm F hF) := by
  let mE := sourceNativeHermitianMetric E hE
  let mF := sourceNativeHermitianMetric F hF
  change RealBottChern.ofRepresentative (firstChernForm mE) =
    RealBottChern.ofRepresentative (firstChernForm mF)
  exact (firstChernClass_eq mE (nativeMetricTransfer e he mF)).trans
    (nativeMetricTransfer_firstChernClass e he mF)

theorem nativeSelfPullback_firstChernClass
    (E : HermitianHolomorphicLineBundle.{0,0} n X)
    (hE : IsSourceSmoothHermitianMetric E)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) X X ∞) :
    RealBottChern.ofRepresentative
      (sourceNativeFirstChernForm (nativeHolomorphicPullbackBundle E f)
        (nativeHolomorphicPullback_smooth E f hE)) =
      SGPT.BDivisor.classPullback f.contMDiff
        (RealBottChern.ofRepresentative (sourceNativeFirstChernForm E hE)) :=
  RealBottChern.ofRepresentative_eq_of_geometricallyEq
    (nativeHolomorphicPullback_firstChern_geometrically E f hE _
      (sourceNativeFirstChernForm_isOwn E hE))

end SGPT.Projective.HyperplaneClassNext
