import SGPT.Projective.SimplexFubiniStudy
import SGPT.Toric.SameDivisorChernClass
import SGPT.Toric.NativeChernPullback
import SGPT.Toric.MetricFiniteSums

/-! Actual native projective hyperplane Chern CLASS, for every genuine original simplex metric. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.Projective.HyperplaneClassNext

open Set Bundle
open SGPT.Toric SGPT.Toric.F1IntersectionDraft SGPT.Projective.FsNormalizationNext
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.NativeHermitianMetric
open SGPT.PSH.LineBundleMetric HermitianHolomorphicLineBundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

variable {N : ℕ} (hs : latticePolytopeEdgeSmooth (simplexGenerator N))

def simplexHyperplaneFsMetric : BigToricMetric (simplexHyperplaneDivisor hs) :=
  BigToricMetric.castMetric (simplexHyperplaneDivisor_eq_ample hs).symm
    (toricFullLatticeMetric (γ := simplexGenerator N) (hs := hs))

theorem simplexHyperplaneFsMetric_form :
    (simplexHyperplaneFsMetric hs).form =
      ClosedRealOneOneForm.pullback (contMDiff_simplexProjectiveHomeomorph hs)
        (ComplexProjectiveSpace.fsClosedForm (N := N)) := by
  rw [simplexHyperplaneFsMetric, BigToricMetric.castMetric_form]
  exact simplexFullLatticeMetric_form_eq_original_fs_pullback hs

theorem simplexHyperplaneMetric_class_eq_fsPullback
    (h : BigToricMetric (simplexHyperplaneDivisor hs)) :
    RealBottChern.ofRepresentative h.form =
      RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback (contMDiff_simplexProjectiveHomeomorph hs)
          (ComplexProjectiveSpace.fsClosedForm (N := N))) := by
  calc
    _ = RealBottChern.ofRepresentative (simplexHyperplaneFsMetric hs).form :=
      toricSameDivisor_firstChernClass h _
    _ = _ := by rw [simplexHyperplaneFsMetric_form]

theorem simplexHyperplaneNativeChern_class_eq_fsPullback
    (h : BigToricMetric (simplexHyperplaneDivisor hs)) :
    RealBottChern.ofRepresentative
      (sourceNativeFirstChernForm (toricNativeHermitianLineBundle h)
        (isSourceSmoothHermitianMetric_toricNativeHermitianLineBundle h)) =
      RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback (contMDiff_simplexProjectiveHomeomorph hs)
          (ComplexProjectiveSpace.fsClosedForm (N := N))) := by
  calc
    _ = RealBottChern.ofRepresentative h.form :=
      RealBottChern.ofRepresentative_eq_of_geometricallyEq
        (toricNativeFirstChernForm_geometricallyEq h)
    _ = _ := simplexHyperplaneMetric_class_eq_fsPullback hs h

def originalSimplexInverseMap :
    ContMDiffMap 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel N)
      (ComplexProjectiveSpace N) (PolytopeToricVariety (simplexGenerator N) hs) ∞ :=
  ⟨(simplexProjectiveHomeomorph hs).symm, contMDiff_simplexProjectiveHomeomorph_symm hs⟩

def nativeProjectiveHyperplaneOfMetric
    (h : BigToricMetric (simplexHyperplaneDivisor hs)) :
    HermitianHolomorphicLineBundle.{0,0} N (ComplexProjectiveSpace N) :=
  nativeHolomorphicPullbackBundle (toricNativeHermitianLineBundle h) (originalSimplexInverseMap hs)

theorem nativeProjectiveHyperplaneOfMetric_smooth
    (h : BigToricMetric (simplexHyperplaneDivisor hs)) :
    IsSourceSmoothHermitianMetric (nativeProjectiveHyperplaneOfMetric hs h) :=
  nativeHolomorphicPullback_smooth _ _
    (isSourceSmoothHermitianMetric_toricNativeHermitianLineBundle h)

theorem nativeProjectiveHyperplaneOfMetric_class_eq_fs
    (h : BigToricMetric (simplexHyperplaneDivisor hs)) :
    RealBottChern.ofRepresentative
      (sourceNativeFirstChernForm (nativeProjectiveHyperplaneOfMetric hs h)
        (nativeProjectiveHyperplaneOfMetric_smooth hs h)) =
      RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := N)) := by
  let f := originalSimplexInverseMap hs
  have hnative := nativeHolomorphicPullback_firstChern_geometrically
    (toricNativeHermitianLineBundle h) f
    (isSourceSmoothHermitianMetric_toricNativeHermitianLineBundle h) h.form
    (isOwnFirstChernForm_toricNativeHermitianLineBundle h)
  calc
    _ = RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback f.contMDiff h.form) :=
      RealBottChern.ofRepresentative_eq_of_geometricallyEq hnative
    _ = SGPT.BDivisor.classPullback f.contMDiff (RealBottChern.ofRepresentative h.form) := rfl
    _ = SGPT.BDivisor.classPullback f.contMDiff
        (SGPT.BDivisor.classPullback (contMDiff_simplexProjectiveHomeomorph hs)
          (RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := N)))) :=
      congrArg (SGPT.BDivisor.classPullback f.contMDiff)
        (simplexHyperplaneMetric_class_eq_fsPullback hs h)
    _ = SGPT.BDivisor.classPullback
        ((contMDiff_simplexProjectiveHomeomorph hs).comp f.contMDiff)
          (RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := N))) :=
      (SGPT.BDivisor.classPullback_comp _ _ _).symm
    _ = SGPT.BDivisor.classPullback contMDiff_id
        (RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := N))) :=
      SGPT.BDivisor.classPullback_congr (by
        funext x
        exact (simplexProjectiveHomeomorph hs).apply_symm_apply x) _ _ _
    _ = _ := SGPT.BDivisor.classPullback_id _

end SGPT.Projective.HyperplaneClassNext
