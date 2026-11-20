import SGPT.Trace.BertiniIntrinsicNormalLift
import SGPT.Trace.BertiniNativeAdjunctionFibers

/-! Actual intrinsic value of the ORIGINAL native canonical adjunction fibre map.

This fixes the actual original defining section (one affine dual-parameter
lift). Changing that lift requires the base O_Lambda(1) in relative adjunction.
Global holomorphic gluing and the intrinsic global Hodge density remain separate.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini.SliceChart

open Bundle Set Filter Metric TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

variable {d N : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (d + 1)) Y] [IsComplexManifold (d + 1) Y]
  [CompactSpace Y]
  {p : Y → ComplexProjectiveSpace N} {φ : Y → EReal}
  (c : SliceChart (d + 1) p φ)

theorem originalCanonicalResidue_intrinsic
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothMemberOfDim p hp (affinePoint c.i q.1.val) d) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    letI := isCompact_iff_compactSpace.mp (isClosed_member p hp.continuous (affinePoint c.i q.1.val)).isCompact
    ∀ (α : (nativeCanonicalBundle (n := d + 1) (X := Y)).Fiber (c.tangentPoint q))
      (v : Fin d → TangentSpace 𝓘(ℂ, ComplexModel d) (c.originalSliceMemberPoint q)),
      nativeCanonicalFiberEquiv (n := d) (c.originalSliceMemberPoint q)
        (c.originalSliceCanonicalFiberResidueEquiv hp q hsm α) v =
      nativeCanonicalFiberEquiv (n := d + 1) (c.tangentPoint q) α
        (Matrix.vecCons (c.originalIntrinsicNormal q)
          (fun i => c.originalNativeInclusionDifferential hp q hsm (v i))) := by
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
  let := isCompact_iff_compactSpace.mp (isClosed_member p hp.continuous (affinePoint c.i q.1.val)).isCompact
  intro α v
  rw [c.originalSliceCanonicalFiberResidueEquiv_apply hp q hsm α v]
  let A := nativeOriginalChartTangentEquiv c.e (c.tangentPoint q) (c.tangentPoint_chart_coordinates q).1
  change nativeCanonicalFiberEquiv (n := d + 1) (c.tangentPoint q) α
    (fun i => A.symm (Matrix.vecCons (c.originalNormalizedNormal q)
      (fun j => (c.originalSliceNativeTangentEquiv hp q hsm (v j)).val) i)) = _
  apply congrArg (nativeCanonicalFiberEquiv (n := d + 1) (c.tangentPoint q) α)
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    change A.symm ((c.originalSliceNativeTangentEquiv hp q hsm (v i)).val) =
      c.originalNativeInclusionDifferential hp q hsm (v i)
    exact c.originalIntrinsicTangentEquiv_apply hp q hsm (v i)

theorem originalAdjunctionFiber_intrinsic
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothMemberOfDim p hp (affinePoint c.i q.1.val) d) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    letI := isCompact_iff_compactSpace.mp (isClosed_member p hp.continuous (affinePoint c.i q.1.val)).isCompact
    ∀ (α : (nativeCanonicalBundle (n := d + 1) (X := Y)).Fiber (c.tangentPoint q))
      (w : (nativeBertiniHyperplaneBundle ⟨p, hp⟩).Fiber (c.tangentPoint q))
      (v : Fin d → TangentSpace 𝓘(ℂ, ComplexModel d) (c.originalSliceMemberPoint q)),
      nativeCanonicalFiberEquiv (n := d) (c.originalSliceMemberPoint q)
        (c.originalSliceAdjunctionFiberEquiv hp q hsm (α ⊗ₜ[ℂ] w)) v =
      nativeCanonicalFiberEquiv (n := d + 1) (c.tangentPoint q) α
        (Matrix.vecCons (c.originalIntrinsicNormalLift hp q w)
          (fun i => c.originalNativeInclusionDifferential hp q hsm (v i))) := by
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
  let := isCompact_iff_compactSpace.mp (isClosed_member p hp.continuous (affinePoint c.i q.1.val)).isCompact
  intro α w v
  rw [c.originalSliceAdjunctionFiberEquiv_tmul hp q hsm, map_smul, AlternatingMap.smul_apply,
    c.originalCanonicalResidue_intrinsic hp q hsm α v]
  have hpoint := c.tangentPoint_chart_coordinates q
  let A := nativeBertiniCoordinateFiberEquiv ⟨p, hp⟩ c.j (c.tangentPoint q)
    ((mem_chartLiftDomain_iff p hpoint.1).mp hpoint.2.2)
  change A w * nativeCanonicalFiberEquiv (n := d + 1) (c.tangentPoint q) α
    (Matrix.vecCons (c.originalIntrinsicNormal q)
      (fun i => c.originalNativeInclusionDifferential hp q hsm (v i))) =
    nativeCanonicalFiberEquiv (n := d + 1) (c.tangentPoint q) α
      (Matrix.vecCons (A w • c.originalIntrinsicNormal q)
        (fun i => c.originalNativeInclusionDifferential hp q hsm (v i)))
  rw [AlternatingMap.map_vecCons_smul]
  rfl

theorem originalAdjunctionFiber_any_normal
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothMemberOfDim p hp (affinePoint c.i q.1.val) d) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    letI := isCompact_iff_compactSpace.mp (isClosed_member p hp.continuous (affinePoint c.i q.1.val)).isCompact
    ∀ (α : (nativeCanonicalBundle (n := d + 1) (X := Y)).Fiber (c.tangentPoint q))
      (w : (nativeBertiniHyperplaneBundle ⟨p, hp⟩).Fiber (c.tangentPoint q))
      (ν : TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) (c.tangentPoint q))
      (_hν : c.originalIntrinsicConormal hp q ν = w)
      (v : Fin d → TangentSpace 𝓘(ℂ, ComplexModel d) (c.originalSliceMemberPoint q)),
      nativeCanonicalFiberEquiv (n := d) (c.originalSliceMemberPoint q)
        (c.originalSliceAdjunctionFiberEquiv hp q hsm (α ⊗ₜ[ℂ] w)) v =
      nativeCanonicalFiberEquiv (n := d + 1) (c.tangentPoint q) α
        (Matrix.vecCons ν (fun i => c.originalNativeInclusionDifferential hp q hsm (v i))) := by
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
  let := isCompact_iff_compactSpace.mp (isClosed_member p hp.continuous (affinePoint c.i q.1.val)).isCompact
  intro α w ν hν v
  rw [c.originalAdjunctionFiber_intrinsic hp q hsm α w v]
  exact c.originalNativeContraction_independent hp q hsm
    (nativeCanonicalFiberEquiv (n := d + 1) (c.tangentPoint q) α)
    (c.originalIntrinsicNormalLift hp q w) ν ((c.originalIntrinsicNormalLift_spec hp q w).trans hν.symm) v

end SGPT.Trace.Bertini.SliceChart
