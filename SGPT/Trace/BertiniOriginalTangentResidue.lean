import SGPT.Trace.BertiniNativeTangentKernel

/-! The original fixed-member equation and actual native tangent/kernel map.

Every equation, normal and local zero identity in the final construction is
produced from the original SliceChart and original smooth-member data.
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
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open scoped ProductComplexManifold
open ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

variable {d N : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (d + 1)) Y] [IsComplexManifold (d + 1) Y]
  {p : Y → ComplexProjectiveSpace N} {φ : Y → EReal}
  (c : SliceChart (d + 1) p φ)

/-- The exact original fixed-parameter member equation in the original
ambient chart and original projective target chart. -/
def originalFixedMemberEquation (q : (ball c.ζ₀ c.r) × c.tangentPatch) :
    ComplexModel (d + 1) → ℂ :=
  fun z => pairing (affineLift c.i q.1.val) (chartLift p c.e c.j z)

/-- The actual original slice point has the actual original ambient
coordinates and lies in the actual original conormal chart domain. -/
theorem tangentPoint_chart_coordinates (q : (ball c.ζ₀ c.r) × c.tangentPatch) :
    c.tangentPoint q ∈ c.e.val.source ∧
      c.e.val (c.tangentPoint q) = c.slice q.1.val (c.tangentLift q.2.val) ∧
      c.e.val (c.tangentPoint q) ∈ chartLiftDomain p c.e c.j := by
  have hs := c.source_subset (c.Φ.mapsTo_invFun
    (c.mapsTo_target q.1.val q.1.property (c.tangentLift q.2.val) q.2.property))
  have hsl : c.slice q.1.val (c.tangentLift q.2.val) ∈ chartLiftDomain p c.e c.j := hs.2
  have hpnt : c.tangentPoint q = c.e.val.symm (c.slice q.1.val (c.tangentLift q.2.val)) := rfl
  rw [hpnt]
  refine ⟨c.e.val.map_target hsl.1, c.e.val.right_inv hsl.1, ?_⟩
  rwa [c.e.val.right_inv hsl.1]

/-- The actual derivative of the exact original fixed-member equation is
the previously produced actual conormal, with no equation/derivative certificate. -/
theorem originalFixedMemberEquation_fderiv
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch) :
    fderiv ℂ (c.originalFixedMemberEquation q) (c.e.val (c.tangentPoint q)) =
      c.originalMemberConormal q := by
  let w := c.Φ.invFun (flatProj c.m
    (prodModelEquiv N (d + 1) (q.1.val, c.tangentLift q.2.val)))
  have ht := c.mapsTo_target q.1.val q.1.property (c.tangentLift q.2.val) q.2.property
  have hs : w ∈ conormalDomain p c.e c.j := c.source_subset (c.Φ.mapsTo_invFun ht)
  have hfst : ((prodModelEquiv N (d + 1)).symm w).1 = q.1.val := by
    rw [c.fst_invFun ht, fst_symm_flatProj, ContinuousLinearEquiv.symm_apply_apply]
  have hw : prodModelEquiv N (d + 1)
      (q.1.val, c.slice q.1.val (c.tangentLift q.2.val)) = w := by
    apply (prodModelEquiv N (d + 1)).symm.injective
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact Prod.ext hfst.symm rfl
  have hG := (differentiableOn_conormalGenerator p hp c.i c.e c.j 0 w hs).differentiableAt
    ((isOpen_conormalDomain p hp c.e c.j).mem_nhds hs)
  let L := prodModelEquiv N (d + 1)
  have hI : HasFDerivAt (fun z : ComplexModel (d + 1) => prodModelEquiv N (d + 1) (q.1.val, z))
      ((L : ComplexModel N × ComplexModel (d + 1) →L[ℂ] ComplexModel (N + (d + 1))).comp
        ((0 : ComplexModel (d + 1) →L[ℂ] ComplexModel N).prod
          (ContinuousLinearMap.id ℂ (ComplexModel (d + 1)))))
      (c.slice q.1.val (c.tangentLift q.2.val)) :=
    (L : ComplexModel N × ComplexModel (d + 1) →L[ℂ] ComplexModel (N + (d + 1))).hasFDerivAt.comp
      (c.slice q.1.val (c.tangentLift q.2.val))
      ((hasFDerivAt_const q.1.val (c.slice q.1.val (c.tangentLift q.2.val))).prodMk
        (hasFDerivAt_id (c.slice q.1.val (c.tangentLift q.2.val))))
  have hG' : HasFDerivAt (conormalGenerator p c.i c.e c.j 0)
      (fderiv ℂ (conormalGenerator p c.i c.e c.j 0) w)
      (prodModelEquiv N (d + 1) (q.1.val, c.slice q.1.val (c.tangentLift q.2.val))) := by
    rw [hw]
    exact hG.hasFDerivAt
  have hc := hG'.comp (c.slice q.1.val (c.tangentLift q.2.val)) hI
  have heq : (conormalGenerator p c.i c.e c.j 0 ∘
      (fun z : ComplexModel (d + 1) => prodModelEquiv N (d + 1) (q.1.val, z))) =
      c.originalFixedMemberEquation q := by
    funext z
    simp only [Function.comp_apply, conormalGenerator, Fin.cons_zero,
      ContinuousLinearEquiv.symm_apply_apply, originalFixedMemberEquation]
  rw [heq] at hc
  rw [(c.tangentPoint_chart_coordinates q).2.1]
  apply hc.fderiv.trans
  apply ContinuousLinearMap.ext
  intro v
  rfl

/-- Exact original member membership supplies actual vanishing of the
actual original fixed-member equation in its genuine chart domain. -/
theorem originalFixedMemberEquation_zero (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    {x : Y} (hx : x ∈ c.e.val.source) (hpx : p x ∈ (affineChart c.j).source)
    (hm : x ∈ member p (affinePoint c.i q.1.val)) :
    c.originalFixedMemberEquation q (c.e.val x) = 0 := by
  change pairing (affineLift c.i q.1.val) (chartLift p c.e c.j (c.e.val x)) = 0
  rw [chartLift_chart p hx]
  apply (isIncident_mk_mk_iff (affineLift_ne_zero c.i q.1.val)
    (affineLift_ne_zero c.j (affineChart c.j (p x)))).mp
  change IsIncident (affinePoint c.i q.1.val)
    (ComplexProjectiveSpace.mk (affineLift c.j (affineChart c.j (p x))) (affineLift_ne_zero _ _))
  rw [← eq_mk_affineLift_affineChart c.j hpx]
  exact hm

/-- The original slice point as an actual point of the literal original member. -/
def originalSliceMemberPoint (q : (ball c.ζ₀ c.r) × c.tangentPatch) :
    member p (affinePoint c.i q.1.val) :=
  ⟨c.tangentPoint q, c.tangentPoint_mem_member q⟩

/-- Native tangent of the ORIGINAL smooth member is the actual original
conormal kernel. Original zero equation and normal are produced internally. -/
def originalSliceNativeTangentEquiv
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothMemberOfDim p hp (affinePoint c.i q.1.val) d) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    TangentSpace 𝓘(ℂ, ComplexModel d) (c.originalSliceMemberPoint q) ≃ₗ[ℂ]
      LinearMap.ker (c.originalMemberConormal q).toLinearMap := by
  letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
  letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
  let y := c.originalSliceMemberPoint q
  let e := complexChartAt (n := d) y
  let z := e.val y
  have hey : y ∈ e.val.source := mem_complexChartAt_source y
  have hpoint := c.tangentPoint_chart_coordinates q
  have hz : z ∈ coordinateDomain (Subtype.val : member p (affinePoint c.i q.1.val) → Y) e c.e :=
    mem_coordinateDomain hey hpoint.1
  have hFz : coordinateMap (Subtype.val : member p (affinePoint c.i q.1.val) → Y) e c.e z =
      c.e.val (c.tangentPoint q) := coordinateMap_at hey
  have hg : DifferentiableAt ℂ (c.originalFixedMemberEquation q)
      (coordinateMap (Subtype.val : member p (affinePoint c.i q.1.val) → Y) e c.e z) := by
    rw [hFz]
    exact (hasFDerivAt_pairing_chartLift p hp hpoint.2.2 (affineLift c.i q.1.val)).differentiableAt
  have hdf : fderiv ℂ (c.originalFixedMemberEquation q)
      (coordinateMap (Subtype.val : member p (affinePoint c.i q.1.val) → Y) e c.e z) =
      c.originalMemberConormal q := by
    rw [hFz, c.originalFixedMemberEquation_fderiv hp q]
  have hν : fderiv ℂ (c.originalFixedMemberEquation q)
      (coordinateMap (Subtype.val : member p (affinePoint c.i q.1.val) → Y) e c.e z)
      (c.originalNormalizedNormal q) = 1 := by
    rw [hdf]
    exact c.originalNormalizedNormal_spec hp q
  have hinc := SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ d) hsm.1
  have hD := coordinateDomain_isOpen hinc e c.e
  have hpy : p (c.tangentPoint q) ∈ (affineChart c.j).source :=
    (mem_chartLiftDomain_iff p hpoint.1).mp hpoint.2.2
  have hF : ContinuousAt
      (fun t : ComplexModel d => p ((e.val.symm t : member p (affinePoint c.i q.1.val)) : Y)) z :=
    hp.continuous.continuousAt.comp ((continuous_subtype_val.continuousAt).comp
      (e.val.continuousAt_symm hz.1))
  have hzero : (c.originalFixedMemberEquation q ∘
      coordinateMap (Subtype.val : member p (affinePoint c.i q.1.val) → Y) e c.e) =ᶠ[𝓝 z]
      fun _ => 0 := by
    have hpy' : p ((e.val.symm z : member p (affinePoint c.i q.1.val)) : Y) ∈
        (affineChart c.j).source := by
      change p ((e.val.symm (e.val y) : member p (affinePoint c.i q.1.val)) : Y) ∈ _
      rw [e.val.left_inv hey]
      exact hpy
    filter_upwards [hD.mem_nhds hz, hF.eventually ((affineChart c.j).open_source.mem_nhds hpy')]
      with t ht hpt
    exact c.originalFixedMemberEquation_zero q ht.2 hpt (e.val.symm t).property
  let E := nativeSubmanifoldCoordinateConormalEquiv hsm.1 e c.e z hz
    (c.originalFixedMemberEquation q) hg (c.originalNormalizedNormal q) hν hzero
  exact E.trans (LinearEquiv.ofEq _ _ (congrArg
    (fun L : ComplexModel (d + 1) →L[ℂ] ℂ => LinearMap.ker L.toLinearMap) hdf))

/-- Exact literal original inclusion derivative retained by the produced
native original tangent/kernel equivalence. -/
theorem originalSliceNativeTangentEquiv_apply
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothMemberOfDim p hp (affinePoint c.i q.1.val) d) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    ∀ v : TangentSpace 𝓘(ℂ, ComplexModel d) (c.originalSliceMemberPoint q),
      (c.originalSliceNativeTangentEquiv hp q hsm v).val =
        fderiv ℂ (coordinateMap (Subtype.val : member p (affinePoint c.i q.1.val) → Y)
          (complexChartAt (n := d) (c.originalSliceMemberPoint q)) c.e)
          ((complexChartAt (n := d) (c.originalSliceMemberPoint q)).val
            (c.originalSliceMemberPoint q)) v := by
  intros
  rfl

/-- Actual original ambient top forms become actual original native member
top covectors through the produced original conormal and inclusion derivative. -/
def originalSliceTopFormResidueEquiv
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothMemberOfDim p hp (affinePoint c.i q.1.val) d) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    ((ComplexModel (d + 1)) [⋀^Fin (d + 1)]→ₗ[ℂ] ℂ) ≃ₗ[ℂ]
      ((TangentSpace 𝓘(ℂ, ComplexModel d) (c.originalSliceMemberPoint q)) [⋀^Fin d]→ₗ[ℂ] ℂ) := by
  letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
  letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
  exact (c.originalConormalResidueEquiv hp q).trans
    (AlternatingMap.domLCongr ℂ ℂ (Fin d) ℂ (c.originalSliceNativeTangentEquiv hp q hsm).symm)

theorem originalSliceTopFormResidueEquiv_apply
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothMemberOfDim p hp (affinePoint c.i q.1.val) d) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    ∀ (α : (ComplexModel (d + 1)) [⋀^Fin (d + 1)]→ₗ[ℂ] ℂ)
      (v : Fin d → TangentSpace 𝓘(ℂ, ComplexModel d) (c.originalSliceMemberPoint q)),
      c.originalSliceTopFormResidueEquiv hp q hsm α v =
        α (Matrix.vecCons (c.originalNormalizedNormal q)
          (fun i => (c.originalSliceNativeTangentEquiv hp q hsm (v i)).val)) := by
  intros
  rfl

end SGPT.Trace.Bertini.SliceChart
