import SGPT.Trace.BertiniGlobalPhysicalAdjunction
import SGPT.Trace.NativeCanonicalPhysicalDensity
import SGPT.Trace.BertiniOriginalMetricResidueDensity
import SGPT.Trace.BertiniOriginalNativeParametrization

/-! Exact actual global physical adjunction image residue density. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini.SliceChart

open Bundle Set Filter TensorProduct Metric
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  {p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞}
  {φ : X → EReal} (c : SliceChart (d + 1) (p : X → ComplexProjectiveSpace N) φ)

def originalGlobalPhysicalResidueValue
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint c.i q.1.val))
    (L : HermitianHolomorphicLineBundle (d + 1) X) :
    let hdim : IsSmoothMemberOfDim p p.contMDiff (affinePoint c.i q.1.val) d :=
      by simpa using isSmoothMemberOfDim_of_isSmoothHypersurfaceMember p p.contMDiff hsm
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hdim.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hdim.1
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint c.i q.1.val)).isCompact
    (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
      (nativeBertiniHyperplaneBundle p)) L).Fiber (c.tangentPoint q) →ₗ[ℂ] L.Fiber (c.tangentPoint q) := by
  let hdim : IsSmoothMemberOfDim p p.contMDiff (affinePoint c.i q.1.val) d :=
    by simpa using isSmoothMemberOfDim_of_isSmoothHypersurfaceMember p p.contMDiff hsm
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hdim.1
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hdim.1
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint c.i q.1.val)).isCompact
  exact (nativeCanonicalPhysicalValue
    (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p c.i q.1.val hsm))
    (c.originalSliceMemberPoint q)
    (fun k => mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d)
      (c.originalMemberParameter q) q.2.val (EuclideanSpace.single k 1))).comp
    (nativeBertiniPhysicalAdjunctionFiberEquiv p c.i q.1.val hsm L
      (c.originalSliceMemberPoint q)).toLinearMap

private theorem originalGlobalPhysicalResidueValue_eq_local
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint c.i q.1.val))
    (L : HermitianHolomorphicLineBundle (d + 1) X) :
    let hdim : IsSmoothMemberOfDim p p.contMDiff (affinePoint c.i q.1.val) d :=
      by simpa using isSmoothMemberOfDim_of_isSmoothHypersurfaceMember p p.contMDiff hsm
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hdim.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hdim.1
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint c.i q.1.val)).isCompact
    ∀ T, c.originalGlobalPhysicalResidueValue q hsm L T =
      c.originalResidueLValue p.contMDiff q hdim L T := by
  dsimp only
  let hdim : IsSmoothMemberOfDim p p.contMDiff (affinePoint c.i q.1.val) d :=
    by simpa using isSmoothMemberOfDim_of_isSmoothHypersurfaceMember p p.contMDiff hsm
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hdim.1
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hdim.1
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint c.i q.1.val)).isCompact
  intro T
  let F := c.originalGlobalPhysicalResidueValue q hsm L
  let G := c.originalResidueLValue p.contMDiff q hdim L
  have hFG : F = G := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro A
    apply LinearMap.ext
    intro l
    change nativeCanonicalFiberEquiv (n := d) (c.originalSliceMemberPoint q)
        (nativeBertiniAdjunctionFiberEquiv p c.i q.1.val hsm (c.originalSliceMemberPoint q) A)
        (fun k => mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d)
          (c.originalMemberParameter q) q.2.val (EuclideanSpace.single k 1)) • l =
      nativeCanonicalFiberEquiv (n := d) (c.originalSliceMemberPoint q)
        (c.originalSliceAdjunctionFiberEquiv p.contMDiff q hdim A)
        (fun k => c.originalSliceParameterTangentEquiv p.contMDiff q hdim
          (EuclideanSpace.single k 1)) • l
    simp_rw [c.mfderiv_originalMemberParameter p.contMDiff q hdim]
    rw [c.originalAdjunctionFiberEquiv_eq_global q hsm A]
  exact LinearMap.congr_fun hFG T

theorem originalGlobalPhysicalResidueValue_eq_normalDivision
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint c.i q.1.val))
    (L : HermitianHolomorphicLineBundle (d + 1) X) :
    let hdim : IsSmoothMemberOfDim p p.contMDiff (affinePoint c.i q.1.val) d :=
      by simpa using isSmoothMemberOfDim_of_isSmoothHypersurfaceMember p p.contMDiff hsm
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hdim.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hdim.1
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint c.i q.1.val)).isCompact
    ∀ T, c.originalGlobalPhysicalResidueValue q hsm L T =
      (c.tangentNormalDenominator q)⁻¹ • c.originalAmbientLValue p.contMDiff q L T := by
  dsimp only
  let hdim : IsSmoothMemberOfDim p p.contMDiff (affinePoint c.i q.1.val) d :=
    by simpa using isSmoothMemberOfDim_of_isSmoothHypersurfaceMember p p.contMDiff hsm
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hdim.1
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hdim.1
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint c.i q.1.val)).isCompact
  intro T
  rw [c.originalGlobalPhysicalResidueValue_eq_local q hsm L T,
    c.originalResidueLValue_eq_normalDivision p.contMDiff q hdim L T]

def originalGlobalWeightedResidueDensity
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint c.i q.1.val))
    (L : HermitianHolomorphicLineBundle (d + 1) X) (T : (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
      (nativeBertiniHyperplaneBundle p)) L).Fiber (c.tangentPoint q)) : ℝ≥0∞ :=
  ENNReal.ofReal (‖c.originalGlobalPhysicalResidueValue q hsm L T‖ ^ 2) *
    multiplierWeight 1 (φ (c.tangentPoint q))

theorem originalGlobalWeightedResidueDensity_eq_normalDivision
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint c.i q.1.val))
    (L : HermitianHolomorphicLineBundle (d + 1) X) (T : (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
      (nativeBertiniHyperplaneBundle p)) L).Fiber (c.tangentPoint q)) :
    c.originalGlobalWeightedResidueDensity q hsm L T =
      ENNReal.ofReal (‖(c.tangentNormalDenominator q)⁻¹ • c.originalAmbientLValue p.contMDiff q L T‖ ^ 2) *
        multiplierWeight 1 (φ (c.tangentPoint q)) := by
  rw [originalGlobalWeightedResidueDensity, c.originalGlobalPhysicalResidueValue_eq_normalDivision q hsm L T]

theorem originalGlobalPhysicalAdjunctionSection_density
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint c.i q.1.val))
    (L : HermitianHolomorphicLineBundle (d + 1) X)
    (S : HolomorphicSections (n := d + 1)
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L).Fiber) :
    let hdim : IsSmoothMemberOfDim p p.contMDiff (affinePoint c.i q.1.val) d :=
      by simpa using isSmoothMemberOfDim_of_isSmoothHypersurfaceMember p p.contMDiff hsm
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hdim.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hdim.1
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint c.i q.1.val)).isCompact
    ENNReal.ofReal (‖nativeCanonicalPhysicalValue
      (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p c.i q.1.val hsm))
      (c.originalSliceMemberPoint q)
      (fun k => mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d)
        (c.originalMemberParameter q) q.2.val (EuclideanSpace.single k 1))
      (nativeBertiniPhysicalAdjunctionSection p c.i q.1.val hsm L S
        (c.originalSliceMemberPoint q))‖ ^ 2) * multiplierWeight 1 (φ (c.tangentPoint q)) =
      ENNReal.ofReal (‖(c.tangentNormalDenominator q)⁻¹ • c.originalAmbientLValue p.contMDiff q L
        (S (c.tangentPoint q))‖ ^ 2) * multiplierWeight 1 (φ (c.tangentPoint q)) := by
  let hdim : IsSmoothMemberOfDim p p.contMDiff (affinePoint c.i q.1.val) d :=
    by simpa using isSmoothMemberOfDim_of_isSmoothHypersurfaceMember p p.contMDiff hsm
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hdim.1
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hdim.1
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint c.i q.1.val)).isCompact
  change c.originalGlobalWeightedResidueDensity q hsm L (S (c.tangentPoint q)) = _
  exact c.originalGlobalWeightedResidueDensity_eq_normalDivision q hsm L (S (c.tangentPoint q))

end SGPT.Trace.Bertini.SliceChart
