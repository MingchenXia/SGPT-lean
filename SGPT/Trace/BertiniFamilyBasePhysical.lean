import SGPT.Trace.BertiniFamilyBaseRestriction
import SGPT.Trace.BertiniFamilyMemberRestriction

/-! Actual canonical/physical native model rebasing to the entire smaller
family, literal holomorphic section restriction and SAME member Hodge datum. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical
open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily

section Generic
variable {n m : ℕ} {Y Z : Type}
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z] [IsComplexManifold m Z]

def nativeTensorPullbackDecompose (E F : HermitianHolomorphicLineBundle.{0,0} n Y)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) Z Y ∞)
    (S : HolomorphicSections (n := m) (nativeHolomorphicPullbackBundle (tensor E F) f).Fiber) :
    HolomorphicSections (n := m)
      (tensor (nativeHolomorphicPullbackBundle E f) (nativeHolomorphicPullbackBundle F f)).Fiber := by
  refine {toFun := fun z => S z,contMDiff_toFun := ?_}
  intro z₀
  let x₀ := f z₀
  let e : AtlasFrame E := ⟨trivializationAt ℂ E.Fiber x₀,inferInstance⟩
  let e' : AtlasFrame F := ⟨trivializationAt ℂ F.Fiber x₀,inferInstance⟩
  let ep := NativeTensorRestriction.pullbackFrame E f e
  let fp := NativeTensorRestriction.pullbackFrame F f e'
  let q := tensorAtlasFrame ep fp
  let t := NativeTensorRestriction.pullbackFrame (tensor E F) f (tensorAtlasFrame e e')
  let := e.property
  let := e'.property
  let := q.property
  let := t.property
  have he : x₀ ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have he' : x₀ ∈ e'.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have hq : z₀ ∈ q.val.baseSet := ⟨he,he'⟩
  have ht : z₀ ∈ t.val.baseSet := ⟨he,he'⟩
  have hs := (t.val.contMDiffAt_section_iff ht).mp (S.contMDiff z₀)
  apply (q.val.contMDiffAt_section_iff hq).mpr
  apply hs.congr_of_eventuallyEq
  have hn := f.contMDiff.continuous.continuousAt.eventually
    ((e.val.open_baseSet.inter e'.val.open_baseSet).mem_nhds ⟨he,he'⟩)
  filter_upwards [hn] with z hz
  exact (NativeTensorRestriction.tensorPullbackFrame_coefficient E F f e e' z hz.1 hz.2 (S z)).symm

theorem nativeTensorPullbackDecompose_apply (E F : HermitianHolomorphicLineBundle.{0,0} n Y)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) Z Y ∞)
    (S : HolomorphicSections (n := m) (nativeHolomorphicPullbackBundle (tensor E F) f).Fiber) (z : Z) :
    nativeTensorPullbackDecompose E F f S z = S z := rfl
end Generic

section Family
variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N)
  (U V : TopologicalSpace.Opens (ComplexModel 1)) (hVU : V ≤ U)
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

omit [CompactSpace X] in
theorem familyBaseInclusion_XMap :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    (familyNativeXMap p i a v U hsm).comp (nativeFamilyBaseInclusion p i a v U V hVU hsm) =
      familyNativeXMap p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  rfl

omit [CompactSpace X] [IsComplexManifold (d + 1) X] in
theorem familyBaseInclusion_scalarParameter :
    SGPT.Trace.BertiniPencilNormal.scalarParameter p i a v U ∘ familyBaseInclusion p i a v U V hVU =
      SGPT.Trace.BertiniPencilNormal.scalarParameter p i a v V := rfl

def familyCanonicalBaseFiberEquiv :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ q : familyIncidence p i a v V,
      (familyNativeCanonicalModel p i a v U hsm).Fiber (familyBaseInclusion p i a v U V hVU q) ≃ₗᵢ[ℂ]
      (familyNativeCanonicalModel p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm)).Fiber q := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  intro q
  exact LinearIsometryEquiv.refl ℂ _

def familyPhysicalBaseFiberEquiv (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ q : familyIncidence p i a v V,
      (familyNativePhysicalModel p i a v U hsm L).Fiber (familyBaseInclusion p i a v U V hVU q) ≃ₗᵢ[ℂ]
      (familyNativePhysicalModel p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L).Fiber q := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  intro q
  exact LinearIsometryEquiv.refl ℂ _

def familyPhysicalBaseRestriction (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber →
      HolomorphicSections (n := d + 1)
        (familyNativePhysicalModel p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L).Fiber := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  intro S
  let E := tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)
  let f := familyNativeXMap p i a v U hsm
  let g := nativeFamilyBaseInclusion p i a v U V hVU hsm
  exact nativeTensorPullbackDecompose E L (f.comp g)
    (NativeTensorRestriction.tensorPullbackSectionRestriction E L f g S)

theorem familyPhysicalBaseRestriction_apply (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ (S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber)
      (q : familyIncidence p i a v V),
      familyPhysicalBaseRestriction p i a v U V hVU hsm L S q = S (familyBaseInclusion p i a v U V hVU q) := by
  intros
  rfl

theorem familyPhysicalBaseRestriction_norm (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ (S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber)
      (q : familyIncidence p i a v V),
      ‖familyPhysicalBaseRestriction p i a v U V hVU hsm L S q‖ = ‖S (familyBaseInclusion p i a v U V hVU q)‖ := by
  intros
  rfl

theorem familyPhysicalBaseRestriction_member (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X) (t : V) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v)
      (familyBaseRestrictedSmoothness p i a v U V hVU hsm t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v)
      (familyBaseRestrictedSmoothness p i a v U V hVU hsm t)
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
    ∀ S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber,
      familyNativeMemberAdjunctionSection p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L t
        (familyPhysicalBaseRestriction p i a v U V hVU hsm L S) =
      familyNativeMemberAdjunctionSection p i a v U hsm L ⟨t.val,hVU t.property⟩ S := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsV t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsV t)
  let := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  intro S
  ext y
  rw [familyNativeMemberAdjunctionSection_apply,familyNativeMemberAdjunctionSection_apply,
    familyPhysicalBaseRestriction_apply]
  rfl

theorem familyPhysicalBaseRestriction_memberHodgeEnergy
    (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X) (φ : X → EReal) (t : V) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber,
      familyNativeMemberHodgeEnergy p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L φ t
        (familyPhysicalBaseRestriction p i a v U V hVU hsm L S) =
      familyNativeMemberHodgeEnergy p i a v U hsm L φ ⟨t.val,hVU t.property⟩ S := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  intro S
  unfold familyNativeMemberHodgeEnergy
  rw [familyPhysicalBaseRestriction_member p i a v U V hVU hsm L t S]
end Family
end SGPT.Trace.BertiniFamilyCanonical
