import SGPT.Projective.SourceHolomorphicSectionPullback
import SGPT.Bergman.SourceTensorDictionary

/-! Genuine restriction with the SAME actual physical tensor fibres. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.NativeTensorRestriction
open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft

variable {n m k : ℕ} {X Y Z : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z] [IsComplexManifold k Z]

def pullbackFrame (E : HermitianHolomorphicLineBundle n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) Y X ∞)
    (e : AtlasFrame E) : AtlasFrame (nativeHolomorphicPullbackBundle E f) :=
  ⟨e.val.pullback f, by constructor; exact ⟨e.val, e.property, rfl⟩⟩

theorem tensorPullbackFrame_coefficient
    (E F : HermitianHolomorphicLineBundle n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) Y X ∞)
    (e : AtlasFrame E) (e' : AtlasFrame F) (y : Y)
    (he : f y ∈ e.val.baseSet) (he' : f y ∈ e'.val.baseSet)
    (T : (tensor E F).Fiber (f y)) :
    ((pullbackFrame (tensor E F) f (tensorAtlasFrame e e')).val ⟨y,T⟩).2 =
      ((tensorAtlasFrame (pullbackFrame E f e) (pullbackFrame F f e')).val ⟨y,T⟩).2 := by
  let ep := pullbackFrame E f e
  let fp := pullbackFrame F f e'
  let := e.property
  let := e'.property
  let := ep.property
  let := fp.property
  change tensorCoordinate E.Fiber F.Fiber e.val e'.val (f y) T =
    tensorCoordinate (nativeHolomorphicPullbackBundle E f).Fiber
      (nativeHolomorphicPullbackBundle F f).Fiber ep.val fp.val y T
  apply DFunLike.congr_fun (f := tensorCoordinate E.Fiber F.Fiber e.val e'.val (f y))
  ext u v
  change tensorCoordinate E.Fiber F.Fiber e.val e'.val (f y) (u ⊗ₜ[ℂ] v) =
    tensorCoordinate (nativeHolomorphicPullbackBundle E f).Fiber
      (nativeHolomorphicPullbackBundle F f).Fiber ep.val fp.val y (u ⊗ₜ[ℂ] v)
  rw [tensorCoordinate_tmul, tensorCoordinate_tmul,
    Trivialization.coe_linearMapAt_of_mem e.val he,
    Trivialization.coe_linearMapAt_of_mem e'.val he',
    Trivialization.coe_linearMapAt_of_mem ep.val he,
    Trivialization.coe_linearMapAt_of_mem fp.val he']
  rfl

def tensorPullbackSectionRestriction
    (E F : HermitianHolomorphicLineBundle n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) Y X ∞)
    (g : ContMDiffMap 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel m) Z Y ∞)
    (S : HolomorphicSections (n := m)
      (tensor (nativeHolomorphicPullbackBundle E f) (nativeHolomorphicPullbackBundle F f)).Fiber) :
    HolomorphicSections (n := k)
      (nativeHolomorphicPullbackBundle (tensor E F) (f.comp g)).Fiber := by
  refine { toFun := fun z => S (g z), contMDiff_toFun := ?_ }
  intro z₀
  let x₀ := f (g z₀)
  let e : AtlasFrame E := ⟨trivializationAt ℂ E.Fiber x₀, inferInstance⟩
  let e' : AtlasFrame F := ⟨trivializationAt ℂ F.Fiber x₀, inferInstance⟩
  let ep := pullbackFrame E f e
  let fp := pullbackFrame F f e'
  let q := tensorAtlasFrame ep fp
  let t := pullbackFrame (tensor E F) (f.comp g) (tensorAtlasFrame e e')
  let := e.property
  let := e'.property
  let := ep.property
  let := fp.property
  let := q.property
  let := t.property
  have he : x₀ ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ _ x₀
  have he' : x₀ ∈ e'.val.baseSet := mem_baseSet_trivializationAt ℂ _ x₀
  have hq : g z₀ ∈ q.val.baseSet := ⟨he,he'⟩
  have ht : z₀ ∈ t.val.baseSet := ⟨he,he'⟩
  have hs := (q.val.contMDiffAt_section_iff hq).mp (S.contMDiff (g z₀))
  apply (t.val.contMDiffAt_section_iff ht).mpr
  apply (hs.comp z₀ g.contMDiff.contMDiffAt).congr_of_eventuallyEq
  have hn := (f.contMDiff.continuous.comp g.contMDiff.continuous).continuousAt.eventually
    ((e.val.open_baseSet.inter e'.val.open_baseSet).mem_nhds ⟨he,he'⟩)
  filter_upwards [hn] with z hz
  exact tensorPullbackFrame_coefficient E F (f.comp g) e e' z hz.1 hz.2 (S (g z))

theorem tensorPullbackSectionRestriction_apply
    (E F : HermitianHolomorphicLineBundle n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) Y X ∞)
    (g : ContMDiffMap 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel m) Z Y ∞)
    (S : HolomorphicSections (n := m)
      (tensor (nativeHolomorphicPullbackBundle E f) (nativeHolomorphicPullbackBundle F f)).Fiber)
    (z : Z) :
    tensorPullbackSectionRestriction E F f g S z = S (g z) := rfl

end SGPT.Trace.NativeTensorRestriction
