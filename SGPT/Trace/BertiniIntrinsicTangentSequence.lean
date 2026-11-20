import SGPT.Trace.BertiniIntrinsicConormalCoordinates
import SGPT.Trace.BertiniNativeChartDerivativeReadback

/-! Actual intrinsic tangent-normal exactness for the ORIGINAL native member.

The produced tangent/kernel isomorphism retains the literal native mfderiv
of the original subtype inclusion, not a chosen abstract tangent map.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini.SliceChart

open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps

variable {d N : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (d + 1)) Y] [IsComplexManifold (d + 1) Y]
  {p : Y → ComplexProjectiveSpace N} {φ : Y → EReal}
  (c : SliceChart (d + 1) p φ)

/-- Actual inverse native ambient chart transports the actual original
coordinate conormal kernel onto the actual intrinsic normal-line kernel. -/
def originalIntrinsicKernelEquiv
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch) :
    LinearMap.ker (c.originalMemberConormal q).toLinearMap ≃ₗ[ℂ]
      LinearMap.ker (c.originalIntrinsicConormal hp q) := by
  let A := nativeOriginalChartTangentEquiv c.e (c.tangentPoint q) (c.tangentPoint_chart_coordinates q).1
  have hpoint := c.tangentPoint_chart_coordinates q
  have hs := nativeBertiniCoordinateSection_ne_zero ⟨p, hp⟩ c.j (c.tangentPoint q)
    ((mem_chartLiftDomain_iff p hpoint.1).mp hpoint.2.2)
  exact {
    toFun := fun w => ⟨A.symm w.val, by
      change c.originalIntrinsicConormal hp q (A.symm w.val) = 0
      rw [c.originalIntrinsicConormal_coordinates hp q, LinearEquiv.apply_symm_apply]
      rw [show c.originalMemberConormal q w.val = 0 from w.property, zero_smul]⟩
    invFun := fun v => ⟨A v.val, by
      have h : c.originalIntrinsicConormal hp q v.val = 0 := v.property
      rw [c.originalIntrinsicConormal_coordinates hp q] at h
      exact (smul_eq_zero.mp h).resolve_right hs⟩
    left_inv := by
      intro w
      apply Subtype.ext
      exact A.apply_symm_apply w.val
    right_inv := by
      intro v
      apply Subtype.ext
      exact A.symm_apply_apply v.val
    map_add' := by
      intro u v
      apply Subtype.ext
      exact map_add A.symm u.val v.val
    map_smul' := by
      intro a v
      apply Subtype.ext
      exact map_smul A.symm a v.val }

section Member

variable (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
  (q : (ball c.ζ₀ c.r) × c.tangentPatch)
  (hsm : IsSmoothMemberOfDim p hp (affinePoint c.i q.1.val) d)

/-- Literal actual native manifold derivative of the ORIGINAL native member
subtype inclusion at the ORIGINAL actual slice point. -/
def originalNativeInclusionDifferential :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    TangentSpace 𝓘(ℂ, ComplexModel d) (c.originalSliceMemberPoint q) →L[ℂ]
      TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) (c.tangentPoint q) := by
  letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
  letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
  exact mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1))
    (Subtype.val : member p (affinePoint c.i q.1.val) → Y) (c.originalSliceMemberPoint q)

/-- The native tangent of the ORIGINAL member is the kernel of the ACTUAL
intrinsic original physical-normal-line conormal, produced from original geometry. -/
def originalIntrinsicTangentEquiv :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    TangentSpace 𝓘(ℂ, ComplexModel d) (c.originalSliceMemberPoint q) ≃ₗ[ℂ]
      LinearMap.ker (c.originalIntrinsicConormal hp q) := by
  letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
  letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
  exact (c.originalSliceNativeTangentEquiv hp q hsm).trans (c.originalIntrinsicKernelEquiv hp q)

theorem originalIntrinsicTangentEquiv_apply :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    ∀ v, (c.originalIntrinsicTangentEquiv hp q hsm v).val =
      c.originalNativeInclusionDifferential hp q hsm v := by
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
  intro v
  let A := nativeOriginalChartTangentEquiv c.e (c.tangentPoint q) (c.tangentPoint_chart_coordinates q).1
  change A.symm ((c.originalSliceNativeTangentEquiv hp q hsm v).val) = _
  rw [c.originalSliceNativeTangentEquiv_apply hp q hsm v]
  let f : ContMDiffMap 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1))
      (member p (affinePoint c.i q.1.val)) Y ∞ :=
    ⟨Subtype.val, SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ d) hsm.1⟩
  have hread := coordinateMap_fderiv_preferred_source_apply f (c.originalSliceMemberPoint q) c.e
    (c.tangentPoint_chart_coordinates q).1 v
  change fderiv ℂ (coordinateMap (Subtype.val : member p (affinePoint c.i q.1.val) → Y)
    (complexChartAt (n := d) (c.originalSliceMemberPoint q)) c.e)
    ((complexChartAt (n := d) (c.originalSliceMemberPoint q)).val (c.originalSliceMemberPoint q)) v =
      A (c.originalNativeInclusionDifferential hp q hsm v) at hread
  rw [hread]
  exact A.symm_apply_apply _

theorem originalNativeInclusionDifferential_injective :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    Function.Injective (c.originalNativeInclusionDifferential hp q hsm) := by
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
  intro u v huv
  apply (c.originalIntrinsicTangentEquiv hp q hsm).injective
  apply Subtype.ext
  simpa only [c.originalIntrinsicTangentEquiv_apply hp q hsm] using huv

theorem originalNativeInclusionDifferential_range :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    (c.originalNativeInclusionDifferential hp q hsm).toLinearMap.range =
      LinearMap.ker (c.originalIntrinsicConormal hp q) := by
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
  apply le_antisymm
  · rintro w ⟨v, rfl⟩
    change c.originalNativeInclusionDifferential hp q hsm v ∈ _
    rw [← c.originalIntrinsicTangentEquiv_apply hp q hsm v]
    exact (c.originalIntrinsicTangentEquiv hp q hsm v).property
  · intro w hw
    obtain ⟨v, hv⟩ := (c.originalIntrinsicTangentEquiv hp q hsm).surjective ⟨w, hw⟩
    refine ⟨v, ?_⟩
    change c.originalNativeInclusionDifferential hp q hsm v = w
    rw [← c.originalIntrinsicTangentEquiv_apply hp q hsm v]
    exact congrArg Subtype.val hv

end Member

end SGPT.Trace.Bertini.SliceChart
