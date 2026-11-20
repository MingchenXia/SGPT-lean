import SGPT.Trace.BertiniFamilyMemberRestriction

/-! Genuine ambient whole sections give actual family physical sections,
with SAME compact-X values/norms and exact original moving-member readback. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical
open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily

section Generic
variable {n m : ℕ} {X Y : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]

def nativeTensorSectionPullback (E F : HermitianHolomorphicLineBundle n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) Y X ∞)
    (S : HolomorphicSections (n := n) (tensor E F).Fiber) :
    HolomorphicSections (n := m)
      (tensor (nativeHolomorphicPullbackBundle E f) (nativeHolomorphicPullbackBundle F f)).Fiber := by
  refine { toFun := fun y => S (f y), contMDiff_toFun := ?_ }
  intro y₀
  let x₀ := f y₀
  let e : AtlasFrame E := ⟨trivializationAt ℂ E.Fiber x₀,inferInstance⟩
  let e' : AtlasFrame F := ⟨trivializationAt ℂ F.Fiber x₀,inferInstance⟩
  let q := tensorAtlasFrame e e'
  let ep := NativeTensorRestriction.pullbackFrame E f e
  let fp := NativeTensorRestriction.pullbackFrame F f e'
  let t := tensorAtlasFrame ep fp
  let := e.property
  let := e'.property
  let := q.property
  let := ep.property
  let := fp.property
  let := t.property
  have he : x₀ ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have he' : x₀ ∈ e'.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have hq : x₀ ∈ q.val.baseSet := ⟨he,he'⟩
  have ht : y₀ ∈ t.val.baseSet := ⟨he,he'⟩
  have hs := (q.val.contMDiffAt_section_iff hq).mp (S.contMDiff x₀)
  apply (t.val.contMDiffAt_section_iff ht).mpr
  apply (hs.comp y₀ f.contMDiff.contMDiffAt).congr_of_eventuallyEq
  have hn := f.contMDiff.continuous.continuousAt.eventually
    ((e.val.open_baseSet.inter e'.val.open_baseSet).mem_nhds ⟨he,he'⟩)
  filter_upwards [hn] with y hy
  exact (NativeTensorRestriction.tensorPullbackFrame_coefficient E F f e e' y hy.1 hy.2 (S (f y))).symm

theorem nativeTensorSectionPullback_apply (E F : HermitianHolomorphicLineBundle n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) Y X ∞)
    (S : HolomorphicSections (n := n) (tensor E F).Fiber) (y : Y) :
    nativeTensorSectionPullback E F f S y = S (f y) := rfl

def nativeTensorSectionPullbackLinearMap (E F : HermitianHolomorphicLineBundle n X)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) Y X ∞) :
    HolomorphicSections (n := n) (tensor E F).Fiber →ₗ[ℂ]
      HolomorphicSections (n := m)
        (tensor (nativeHolomorphicPullbackBundle E f) (nativeHolomorphicPullbackBundle F f)).Fiber where
  toFun := nativeTensorSectionPullback E F f
  map_add' S T := by ext y; rfl
  map_smul' c S := by ext y; rfl
end Generic

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

def familyAmbientPhysicalSection
    (L : HermitianHolomorphicLineBundle (d + 1) X) (T : HolomorphicSections (n := d + 1)
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
        (nativeBertiniHyperplaneBundle p)) L).Fiber) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  exact nativeTensorSectionPullback
    (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p))
    L (familyNativeXMap p i a v U hsm) T

theorem familyAmbientPhysicalSection_apply
    (L : HermitianHolomorphicLineBundle (d + 1) X) (T : HolomorphicSections (n := d + 1)
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
        (nativeBertiniHyperplaneBundle p)) L).Fiber) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ q : familyIncidence p i a v U,
      familyAmbientPhysicalSection p i a v U hsm L T q = T q.val.2 := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro q
  rfl

theorem familyAmbientPhysicalSection_norm
    (L : HermitianHolomorphicLineBundle (d + 1) X) (T : HolomorphicSections (n := d + 1)
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
        (nativeBertiniHyperplaneBundle p)) L).Fiber) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ q : familyIncidence p i a v U,
      ‖familyAmbientPhysicalSection p i a v U hsm L T q‖ = ‖T q.val.2‖ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro q
  rfl

theorem familyAmbientPhysicalSection_norm_le
    (L : HermitianHolomorphicLineBundle (d + 1) X) (T : HolomorphicSections (n := d + 1)
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
        (nativeBertiniHyperplaneBundle p)) L).Fiber) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ q : familyIncidence p i a v U,
      ‖familyAmbientPhysicalSection p i a v U hsm L T q‖ ≤ ‖T‖ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro q
  exact norm_apply_le_sectionSize _ T q.val.2

theorem familyAmbientPhysicalSection_member
    (L : HermitianHolomorphicLineBundle (d + 1) X) (T : HolomorphicSections (n := d + 1)
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
        (nativeBertiniHyperplaneBundle p)) L).Fiber) (t : U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
    familyNativeMemberAdjunctionSection p i a v U hsm L t
      (familyAmbientPhysicalSection p i a v U hsm L T) =
      nativeBertiniPhysicalAdjunctionSection p i (a - t.val 0 • v) (hsm t) L T := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  ext y
  rfl

theorem familyAmbientPhysicalSection_memberHodgeEnergy
    (L : HermitianHolomorphicLineBundle (d + 1) X) (φ : X → EReal) (T : HolomorphicSections (n := d + 1)
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
        (nativeBertiniHyperplaneBundle p)) L).Fiber) (t : U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    familyNativeMemberHodgeEnergy p i a v U hsm L φ t
      (familyAmbientPhysicalSection p i a v U hsm L T) =
      nativeBertiniAdjunctionHodgeEnergy p i (a - t.val 0 • v) (hsm t) L φ T := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  exact congrArg (nativeBertiniMemberHodgeEnergy p i (a - t.val 0 • v) (hsm t) L φ)
    (familyAmbientPhysicalSection_member p i a v U hsm L T t)

end SGPT.Trace.BertiniFamilyCanonical
