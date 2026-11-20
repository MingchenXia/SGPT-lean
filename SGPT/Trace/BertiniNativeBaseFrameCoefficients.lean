import SGPT.Trace.BertiniFamilyBasePhysical

/-! ANY small physical section has genuine holomorphic coefficients in EVERY large frame. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical
open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily
open SGPT.Trace.NativeTensorRestriction

section Generic
variable {n m k : ℕ} {X Y Z : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z] [IsComplexManifold k Z]

private theorem actualTensorCompositeFrameCoefficient
    (E F : HermitianHolomorphicLineBundle.{0,0} n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) Y X ∞)
    (g : ContMDiffMap 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel m) Z Y ∞)
    (e : AtlasFrame E) (h : AtlasFrame F) (z : Z)
    (he : f (g z) ∈ e.val.baseSet) (hh : f (g z) ∈ h.val.baseSet)
    (T : (tensor E F).Fiber (f (g z))) :
    ((pullbackFrame (tensor (nativeHolomorphicPullbackBundle E f) (nativeHolomorphicPullbackBundle F f))
      g (tensorAtlasFrame (pullbackFrame E f e) (pullbackFrame F f h))).val ⟨z,T⟩).2 =
      ((tensorAtlasFrame (pullbackFrame E (f.comp g) e) (pullbackFrame F (f.comp g) h)).val ⟨z,T⟩).2 := by
  let ep := pullbackFrame E f e
  let hp := pullbackFrame F f h
  let eq := pullbackFrame E (f.comp g) e
  let hq := pullbackFrame F (f.comp g) h
  let := ep.property
  let := hp.property
  let := eq.property
  let := hq.property
  change tensorCoordinate (nativeHolomorphicPullbackBundle E f).Fiber
    (nativeHolomorphicPullbackBundle F f).Fiber ep.val hp.val (g z) T =
    tensorCoordinate (nativeHolomorphicPullbackBundle E (f.comp g)).Fiber
      (nativeHolomorphicPullbackBundle F (f.comp g)).Fiber eq.val hq.val z T
  apply DFunLike.congr_fun (f := tensorCoordinate (nativeHolomorphicPullbackBundle E f).Fiber
    (nativeHolomorphicPullbackBundle F f).Fiber ep.val hp.val (g z))
  ext u v
  change tensorCoordinate (nativeHolomorphicPullbackBundle E f).Fiber
    (nativeHolomorphicPullbackBundle F f).Fiber ep.val hp.val (g z) (u ⊗ₜ[ℂ] v) =
    tensorCoordinate (nativeHolomorphicPullbackBundle E (f.comp g)).Fiber
      (nativeHolomorphicPullbackBundle F (f.comp g)).Fiber eq.val hq.val z (u ⊗ₜ[ℂ] v)
  rw [tensorCoordinate_tmul,tensorCoordinate_tmul,
    Trivialization.coe_linearMapAt_of_mem ep.val he,
    Trivialization.coe_linearMapAt_of_mem hp.val hh,
    Trivialization.coe_linearMapAt_of_mem eq.val he,
    Trivialization.coe_linearMapAt_of_mem hq.val hh]
  rfl

def nativeTensorPullbackCompositionSection
    (E F : HermitianHolomorphicLineBundle.{0,0} n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) Y X ∞)
    (g : ContMDiffMap 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel m) Z Y ∞)
    (S : HolomorphicSections (n := k) (tensor
      (nativeHolomorphicPullbackBundle E (f.comp g)) (nativeHolomorphicPullbackBundle F (f.comp g))).Fiber) :
    HolomorphicSections (n := k) (nativeHolomorphicPullbackBundle
      (tensor (nativeHolomorphicPullbackBundle E f) (nativeHolomorphicPullbackBundle F f)) g).Fiber := by
  refine {toFun := fun z => S z,contMDiff_toFun := ?_}
  intro z₀
  let x₀ := f (g z₀)
  let e : AtlasFrame E := ⟨trivializationAt ℂ E.Fiber x₀,inferInstance⟩
  let h : AtlasFrame F := ⟨trivializationAt ℂ F.Fiber x₀,inferInstance⟩
  let q := tensorAtlasFrame (pullbackFrame E (f.comp g) e) (pullbackFrame F (f.comp g) h)
  let t := pullbackFrame (tensor (nativeHolomorphicPullbackBundle E f) (nativeHolomorphicPullbackBundle F f))
    g (tensorAtlasFrame (pullbackFrame E f e) (pullbackFrame F f h))
  let := q.property
  let := t.property
  have he : x₀ ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have hh : x₀ ∈ h.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have hq : z₀ ∈ q.val.baseSet := ⟨he,hh⟩
  have ht : z₀ ∈ t.val.baseSet := ⟨he,hh⟩
  have hs := (q.val.contMDiffAt_section_iff hq).mp (S.contMDiff z₀)
  apply (t.val.contMDiffAt_section_iff ht).mpr
  apply hs.congr_of_eventuallyEq
  have hn := (f.contMDiff.continuous.comp g.contMDiff.continuous).continuousAt.eventually
    ((e.val.open_baseSet.inter h.val.open_baseSet).mem_nhds ⟨he,hh⟩)
  filter_upwards [hn] with z hz
  exact (actualTensorCompositeFrameCoefficient E F f g e h z hz.1 hz.2 (S z)).symm

theorem nativeTensorPullbackCompositionSection_apply
    (E F : HermitianHolomorphicLineBundle.{0,0} n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) Y X ∞)
    (g : ContMDiffMap 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel m) Z Y ∞)
    (S : HolomorphicSections (n := k) (tensor
      (nativeHolomorphicPullbackBundle E (f.comp g)) (nativeHolomorphicPullbackBundle F (f.comp g))).Fiber)
    (z : Z) : nativeTensorPullbackCompositionSection E F f g S z = S z := rfl

theorem contMDiffAt_tensorPullbackComposition_frameCoefficient
    (E F : HermitianHolomorphicLineBundle.{0,0} n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) Y X ∞)
    (g : ContMDiffMap 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel m) Z Y ∞)
    (S : HolomorphicSections (n := k) (tensor
      (nativeHolomorphicPullbackBundle E (f.comp g)) (nativeHolomorphicPullbackBundle F (f.comp g))).Fiber)
    (e : AtlasFrame (tensor (nativeHolomorphicPullbackBundle E f) (nativeHolomorphicPullbackBundle F f)))
    (z : Z) (hz : g z ∈ e.val.baseSet) :
    ContMDiffAt 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ℂ) ∞ (fun z => (e.val ⟨g z,S z⟩).2) z := by
  let T := nativeTensorPullbackCompositionSection E F f g S
  let ep := pullbackFrame (tensor (nativeHolomorphicPullbackBundle E f) (nativeHolomorphicPullbackBundle F f)) g e
  let := ep.property
  have h := (ep.val.contMDiffAt_section_iff hz).mp (T.contMDiff z)
  exact h
end Generic

section Family
variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N)
  (U V : TopologicalSpace.Opens (ComplexModel 1)) (hVU : V ≤ U)
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

theorem contMDiffAt_familySmallSection_largeFrameCoefficient
    (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ (S : HolomorphicSections (n := d + 1)
      (familyNativePhysicalModel p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L).Fiber)
      (e : AtlasFrame (familyNativePhysicalModel p i a v U hsm L))
      (q : familyIncidence p i a v V),
      familyBaseInclusion p i a v U V hVU q ∈ e.val.baseSet →
      ContMDiffAt 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) ∞
        (fun q => (e.val ⟨familyBaseInclusion p i a v U V hVU q,S q⟩).2) q := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  intro S e q hq
  exact contMDiffAt_tensorPullbackComposition_frameCoefficient
    (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L
    (familyNativeXMap p i a v U hsm) (nativeFamilyBaseInclusion p i a v U V hVU hsm) S e q hq
end Family

end SGPT.Trace.BertiniFamilyCanonical
