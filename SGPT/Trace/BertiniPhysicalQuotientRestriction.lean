import SGPT.Trace.NativeTensorSwapLast
import SGPT.Trace.BertiniGlobalPhysicalAdjunction

/-! Genuine physical canonical restriction of the literal original
multiplier quotient. No Nadel or restriction isomorphism is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft

section Generic
variable {n : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

def nativeMultiplierSwapLastSectionMap (E F G : HermitianHolomorphicLineBundle n Y)
    {φ : Y → EReal} (hφ : IsGlobalQuasiPshPotential (n := n) φ) :
    nativeMultiplierSections (tensor (tensor E F) G) φ →ₗ[ℂ]
      nativeMultiplierSections (tensor (tensor E G) F) φ where
  toFun S := ⟨NativeTensorSwap.swapLastSection E F G S.val,
    NativeTensorSwap.swapLastSection_mem_multiplier E F G hφ S⟩
  map_add' S T := by
    apply Subtype.ext
    ext y
    exact map_add (NativeTensorSwap.swapLastFiber E F G y) (S.val y) (T.val y)
  map_smul' c S := by
    apply Subtype.ext
    ext y
    exact map_smul (NativeTensorSwap.swapLastFiber E F G y) c (S.val y)
end Generic

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (ζ : ComplexModel N)
  (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
  (L : HermitianHolomorphicLineBundle (d + 1) X)
  {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ)

def nativeBertiniPhysicalQuotientRestriction :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    ((nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ) ⧸
      (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
        (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i ζ)).range) →ₗ[ℂ]
    HolomorphicSections (n := d) (tensor (nativeCanonicalBundle (n := d)
      (X := member p (affinePoint i ζ)))
      (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  let E := tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L
  let P := nativeBertiniHyperplaneBundle p
  let M := nativeMultiplierSectionMap E P hφ (nativeBertiniAffineSection p i ζ)
  let R : nativeMultiplierSections (tensor E P) φ →ₗ[ℂ]
      HolomorphicSections (n := d) (tensor (nativeCanonicalBundle (n := d)
        (X := member p (affinePoint i ζ)))
        (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber := {
    toFun S := nativeBertiniPhysicalAdjunctionSection p i ζ hsm L
      (nativeMultiplierSwapLastSectionMap _ L P hφ S).val
    map_add' S T := by
      ext y
      change nativeBertiniPhysicalAdjunctionFiberEquiv p i ζ hsm L y
          (NativeTensorSwap.swapLastFiber _ L P y.val (S.val y.val + T.val y.val)) = _
      rw [map_add,map_add]
      rfl
    map_smul' c S := by
      ext y
      change nativeBertiniPhysicalAdjunctionFiberEquiv p i ζ hsm L y
          (NativeTensorSwap.swapLastFiber _ L P y.val (c • S.val y.val)) = _
      rw [map_smul,map_smul]
      rfl }
  apply M.range.liftQ R
  rintro S ⟨u,rfl⟩
  ext y
  change nativeBertiniPhysicalAdjunctionFiberEquiv p i ζ hsm L y
    (NativeTensorSwap.swapLastFiber _ L P y.val
      (u.val y.val ⊗ₜ[ℂ] nativeBertiniAffineSection p i ζ y.val)) = 0
  rw [(nativeBertiniAffineSection_zero_iff p i ζ y.val).mpr y.property,
    TensorProduct.tmul_zero,map_zero,map_zero]

theorem nativeBertiniPhysicalQuotientRestriction_mk
    (S : nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    nativeBertiniPhysicalQuotientRestriction p i ζ hsm L hφ
      ((nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
        (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i ζ)).range.mkQ S) =
      nativeBertiniPhysicalAdjunctionSection p i ζ hsm L
        (NativeTensorSwap.swapLastSection (nativeCanonicalBundle (n := d + 1) (X := X)) L
          (nativeBertiniHyperplaneBundle p) S.val) := rfl

theorem nativeBertiniPhysicalQuotientRestriction_mk_apply
    (S : nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ)
    (y : member p (affinePoint i ζ)) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    nativeBertiniPhysicalQuotientRestriction p i ζ hsm L hφ
      ((nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
        (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i ζ)).range.mkQ S) y =
      nativeBertiniPhysicalAdjunctionFiberEquiv p i ζ hsm L y
        (NativeTensorSwap.swapLastFiber (nativeCanonicalBundle (n := d + 1) (X := X)) L
          (nativeBertiniHyperplaneBundle p) y.val (S.val y.val)) := rfl

end SGPT.Trace.Bertini
