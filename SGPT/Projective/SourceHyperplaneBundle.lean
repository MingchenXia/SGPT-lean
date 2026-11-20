import SGPT.Toric.Toric4Projective
import SGPT.Toric.NativePhysicalLineBundle
import SGPT.Toric.NativeChernPullback

/-! Actual native O(1) in every original projective dimension, obtained from
its genuine simplex hyperplane bundle through the actual biholomorphism. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Bergman.NativeKodairaPullback
open Bundle Set
open SGPT.Toric SGPT.Toric.F1IntersectionDraft
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle SGPT.Projective
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

/-- A genuine native source metric on the independently defined simplex
hyperplane Cartier bundle. It has no source-manifold or section-family input. -/
def sourceSimplexHyperplaneMetric (N : ℕ) :
    BigToricMetric (simplexHyperplaneDivisor (simplex_edgeSmooth (N := N))) :=
  Classical.choice (exists_bigToricMetric _)

/-- The actual original inverse simplex/projective biholomorphism. -/
def sourceProjectiveSimplexInverseMap (N : ℕ) :
    ContMDiffMap 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel N)
      (ComplexProjectiveSpace N)
      (PolytopeToricVariety (simplexGenerator N) (simplex_edgeSmooth (N := N))) ∞ :=
  ⟨(simplexProjectiveHomeomorph (simplex_edgeSmooth (N := N))).symm,
    contMDiff_simplexProjectiveHomeomorph_symm (simplex_edgeSmooth (N := N))⟩

/-- The genuine native projective hyperplane bundle O(1). Its fibers and total
space carry Mathlib's actual pullback topology and holomorphic bundle atlas,
independently of every source bundle and of the eventual Kodaira family.
Dimension N=0 is retained without a NeZero or nonempty-source premise. -/
def sourceProjectiveHyperplaneBundle (N : ℕ) :
    HermitianHolomorphicLineBundle.{0,0} N (ComplexProjectiveSpace N) :=
  nativeHolomorphicPullbackBundle
    (toricNativeHermitianLineBundle (sourceSimplexHyperplaneMetric N))
    (sourceProjectiveSimplexInverseMap N)

/-- Actual smoothness of the inherited native hyperplane metric is derived
from the genuine native simplex metric and actual holomorphic pullback. -/
theorem sourceProjectiveHyperplaneBundle_sourceSmooth (N : ℕ) :
    IsSourceSmoothHermitianMetric (sourceProjectiveHyperplaneBundle N) :=
  nativeHolomorphicPullback_smooth
    (toricNativeHermitianLineBundle (sourceSimplexHyperplaneMetric N))
    (sourceProjectiveSimplexInverseMap N)
    (isSourceSmoothHermitianMetric_toricNativeHermitianLineBundle
      (sourceSimplexHyperplaneMetric N))

/-- The physical carrier is the literal independently constructed native
pullback fiber, not a section-space replacement or a prescribed model field. -/
theorem sourceProjectiveHyperplaneBundle_fiber (N : ℕ)
    (p : ComplexProjectiveSpace N) :
    (sourceProjectiveHyperplaneBundle N).Fiber p =
      ((sourceProjectiveSimplexInverseMap N) *ᵖ
        (ToricNativeLineFiber (sourceSimplexHyperplaneMetric N))) p := rfl

end SGPT.Bergman.NativeKodairaPullback
