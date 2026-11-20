import SGPT.Projective.SourceBundleChernNaturality
import SGPT.Projective.SourceLinearCoordinateFamily
import SGPT.Projective.SourceFamilyHolomorphicEquivalence
import SGPT.Projective.SourceHolomorphicSectionPullback

/-! Actual native O1 and physical FS CLASS invariance under every projective linear automorphism. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Projective.HyperplaneClassNext

open Set Bundle
open SGPT.Toric SGPT.Toric.F1IntersectionDraft
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.NativeKodairaPullback SGPT.Bergman.AnalyticSectionProducts
open HermitianHolomorphicLineBundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

theorem sourceProjectiveHyperplaneBundle_class_eq_fs (N : ℕ) :
    RealBottChern.ofRepresentative
      (sourceNativeFirstChernForm (sourceProjectiveHyperplaneBundle N)
        (sourceProjectiveHyperplaneBundle_sourceSmooth N)) =
      RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := N)) :=
  nativeProjectiveHyperplaneOfMetric_class_eq_fs (simplex_edgeSmooth (N := N))
    (sourceSimplexHyperplaneMetric N)

theorem projectiveLinear_nativeHyperplaneClass {N : ℕ}
    (A : (Fin (N + 1) → ℂ) ≃ₗ[ℂ] (Fin (N + 1) → ℂ)) :
    SGPT.BDivisor.classPullback (projectiveLinearSelfMap A).contMDiff
      (RealBottChern.ofRepresentative
        (sourceNativeFirstChernForm (sourceProjectiveHyperplaneBundle N)
          (sourceProjectiveHyperplaneBundle_sourceSmooth N))) =
      RealBottChern.ofRepresentative
        (sourceNativeFirstChernForm (sourceProjectiveHyperplaneBundle N)
          (sourceProjectiveHyperplaneBundle_sourceSmooth N)) := by
  let E := sourceProjectiveHyperplaneBundle N
  let f := projectiveLinearSelfMap A
  let F := nativeHolomorphicPullbackBundle E f
  let hE := sourceProjectiveHyperplaneBundle_sourceSmooth N
  let hF := nativeHolomorphicPullback_smooth E f hE
  let s := projectiveLinearFormFamily A
  let t := fun j => sourceNativeHolomorphicSectionPullback E f
    (sourceProjectiveCoordinateNativeSection N j)
  have hs : ∀ p, ∃ i, s i p ≠ 0 := projectiveLinearFormFamily_generating A
  have ht : ∀ p, ∃ i, t i p ≠ 0 :=
    sourceNativeHolomorphicSectionPullback_generating E f
      (sourceProjectiveCoordinateNativeSection N)
      (sourceProjectiveCoordinateNativeSection_generating N)
  have hSame : ∀ p, sourceNativeFiniteSectionProjectiveMap E s hs p =
      sourceNativeFiniteSectionProjectiveMap F t ht p := by
    intro p
    exact (projectiveLinearFormFamily_projectiveMap A p).trans
      ((sourceNativeFiniteFamily_projectiveMap_pullback E f
        (sourceProjectiveCoordinateNativeSection N)
        (sourceProjectiveCoordinateNativeSection_generating N) p).trans
          (sourceProjectiveCoordinateNativeSection_projectiveMap_identity N (f p))).symm
  have hclass := nativeFiberEquiv_firstChernClass E F hE hF
    (sourceNativeGeneratingFamilies_fiberEquiv E F s t hs ht hSame)
    (sourceNativeGeneratingFamilies_contMDiff_totalMap E F s t hs ht hSame)
  exact (nativeSelfPullback_firstChernClass E hE f).symm.trans hclass.symm

theorem projectiveLinear_fsClass {N : ℕ}
    (A : (Fin (N + 1) → ℂ) ≃ₗ[ℂ] (Fin (N + 1) → ℂ)) :
    SGPT.BDivisor.classPullback (projectiveLinearSelfMap A).contMDiff
      (RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := N))) =
      RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := N)) := by
  rw [← sourceProjectiveHyperplaneBundle_class_eq_fs N]
  exact projectiveLinear_nativeHyperplaneClass A

end SGPT.Projective.HyperplaneClassNext
