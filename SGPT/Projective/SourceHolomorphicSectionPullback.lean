import SGPT.Toric.ExceptionalCurve
import SGPT.Toric.NativeChernPullback
import SGPT.Projective.SourceFiniteSectionMap

/-! Actual native section pullback and its literal projective-family functor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Bergman.NativeKodairaPullback
open Bundle Set
open SGPT.Toric.F1IntersectionDraft SGPT.Toric.ExceptionalRestrictionDraft
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.AnalyticSectionProducts
open HermitianHolomorphicLineBundle SGPT.Projective
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff
variable {n m N : ℕ} {X Y : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]

/-- Actual global holomorphic pullback of an original native full section.
The existing genuine total-space pullback criterion proves regularity; the
carrier is literally the original section evaluated at the original map. -/
def sourceNativeHolomorphicSectionPullback
    (E : HermitianHolomorphicLineBundle.{0,0} n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) Y X ∞)
    (t : HolomorphicSections (n := n) E.Fiber) :
    HolomorphicSections (n := m) (nativeHolomorphicPullbackBundle E f).Fiber where
  toFun y := t (f y)
  contMDiff_toFun := contMDiff_nativePullbackMk E f 𝓘(ℂ, ComplexModel m)
    id (fun y => t (f y)) contMDiff_id (t.contMDiff.comp f.contMDiff)

/-- The same actual original physical fiber value, with no carrier transport
or section-space replacement. -/
theorem sourceNativeHolomorphicSectionPullback_apply
    (E : HermitianHolomorphicLineBundle.{0,0} n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) Y X ∞)
    (t : HolomorphicSections (n := n) E.Fiber) (y : Y) :
    sourceNativeHolomorphicSectionPullback E f t y = t (f y) := rfl

/-- True native generation pulls back to generation of the actual pullback
bundle at every original source point, in all dimensions and for empty Y. -/
theorem sourceNativeHolomorphicSectionPullback_generating
    (E : HermitianHolomorphicLineBundle.{0,0} n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) Y X ∞)
    (s : Fin (N+1) → HolomorphicSections (n := n) E.Fiber)
    (hGen : ∀ x : X, ∃ j : Fin (N+1), s j x ≠ 0) :
    ∀ y : Y, ∃ j : Fin (N+1), sourceNativeHolomorphicSectionPullback E f (s j) y ≠ 0 :=
  fun y => hGen (f y)

/-- The ACTUAL finite-native-family projective map commutes with genuine
holomorphic pullback. Both sides read the SAME homogeneous tuple in any
actual original frame and its actual pulled-back frame. -/
theorem sourceNativeFiniteFamily_projectiveMap_pullback
    (E : HermitianHolomorphicLineBundle.{0,0} n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) Y X ∞)
    (s : Fin (N+1) → HolomorphicSections (n := n) E.Fiber)
    (hGen : ∀ x : X, ∃ j : Fin (N+1), s j x ≠ 0) (y : Y) :
    sourceNativeFiniteSectionProjectiveMap (nativeHolomorphicPullbackBundle E f)
      (fun j => sourceNativeHolomorphicSectionPullback E f (s j))
      (sourceNativeHolomorphicSectionPullback_generating E f s hGen) y =
      sourceNativeFiniteSectionProjectiveMap E s hGen (f y) := by
  let e0 := trivializationAt ℂ E.Fiber (f y)
  let e : AtlasFrame E := ⟨e0, inferInstance⟩
  let B := nativeHolomorphicPullbackBundle E f
  let ep : AtlasFrame B := ⟨e0.pullback f, by
    constructor
    exact ⟨e0, inferInstance, rfl⟩⟩
  have hx : f y ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ E.Fiber (f y)
  have hy : y ∈ ep.val.baseSet := hx
  rw [sourceNativeFiniteSectionProjectiveMap_frame B _ _ ep y hy,
    sourceNativeFiniteSectionProjectiveMap_frame E s hGen e (f y) hx]
  apply (ComplexProjectiveSpace.mk_eq_mk_iff _ _).mpr
  refine ⟨1, ?_⟩
  funext j
  simp only [one_smul]
  rfl

end SGPT.Bergman.NativeKodairaPullback
