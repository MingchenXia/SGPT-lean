import SGPT.Trace.BertiniOriginalMetricResidueDensity

/-! The actual original member-valued slice map is native holomorphic and
its LITERAL native Mathlib mfderiv is the produced parameter tangent map.
Global holomorphic adjunction/coordinate density/Hodge gluing stay separate. -/

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

variable {d N : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (d + 1)) Y] [IsComplexManifold (d + 1) Y]
  {p : Y → ComplexProjectiveSpace N} {φ : Y → EReal}
  (c : SliceChart (d + 1) p φ)

/-- The actual original member-valued inverse-flattening parametrization
on its actual open patch, extended by the original point elsewhere. -/
def originalMemberParameter (q : (ball c.ζ₀ c.r) × c.tangentPatch) :
    ComplexModel d → member p (affinePoint c.i q.1.val) := by
  classical
  exact fun b => if hb : b ∈ c.tangentPatch then c.originalSliceMemberPoint (q.1, ⟨b, hb⟩)
    else c.originalSliceMemberPoint q

theorem originalMemberParameter_apply
    (q : (ball c.ζ₀ c.r) × c.tangentPatch) {b : ComplexModel d} (hb : b ∈ c.tangentPatch) :
    c.originalMemberParameter q b = c.originalSliceMemberPoint (q.1, ⟨b, hb⟩) := by
  classical
  exact dif_pos hb

theorem originalMemberParameter_at (q : (ball c.ζ₀ c.r) × c.tangentPatch) :
    c.originalMemberParameter q q.2.val = c.originalSliceMemberPoint q := by
  rw [c.originalMemberParameter_apply q q.2.property]

theorem contMDiffAt_originalMemberParameter
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothMemberOfDim p hp (affinePoint c.i q.1.val) d) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    ContMDiffAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞ (c.originalMemberParameter q) q.2.val := by
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
  let g := c.originalMemberParameter q
  have hH : ContDiffAt ℂ ∞ (c.originalTangentCoordinateMap q.1.val) q.2.val :=
    contDiffAt_of_differentiableOn_complex
      (fun b hb => (c.differentiableAt_originalTangentCoordinateMap (q.1, ⟨b, hb⟩)).differentiableWithinAt)
      c.isOpen_tangentPatch q.2.property
  have ht := c.V_subset (c.mapsTo_V q.1.val q.1.property (c.tangentLift q.2.val) q.2.property)
  have ha := (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas c.e.property) ht).comp
    q.2.val hH.contMDiffAt
  have heq : (fun b => (g b).val) =ᶠ[𝓝 q.2.val]
      (fun b => c.e.val.symm (c.originalTangentCoordinateMap q.1.val b)) := by
    filter_upwards [c.isOpen_tangentPatch.mem_nhds q.2.property] with b hb
    rw [show g b = c.originalSliceMemberPoint (q.1, ⟨b, hb⟩) from c.originalMemberParameter_apply q hb]
    rfl
  have hg : ContMDiffAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1)) ∞
      (fun b => (g b).val) q.2.val := ha.congr_of_eventuallyEq heq
  let F := SubmanifoldChartedSpace.FlatData.ofRegularAtDim (hsm.1 (g q.2.val).val (g q.2.val).property)
  have hgy : (g q.2.val).val ∈ F.ambSource :=
    SubmanifoldChartedSpace.FlatData.mem_ambSource_ofRegularAtDim _
  have hchart : g q.2.val ∈ (chartAt (ComplexModel d) (g q.2.val)).source := mem_chart_source _ _
  rw [contMDiffAt_iff_target_of_mem_source hchart]
  refine ⟨tendsto_subtype_rng.mpr hg.continuousAt, ?_⟩
  change ContMDiffAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞
    (fun b => FirstPass.RegularLocusDense.coordinateProjection (d + 1) d
      (F.flat (F.amb.val (g b).val))) q.2.val
  have hfa := (contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas F.amb.property) hgy.1).comp
    q.2.val hg
  have hfb := (contDiffAt_of_differentiableOn_complex F.differentiableOn_flat
    F.flat.open_source hgy.2).contMDiffAt
  exact (FirstPass.RegularLocusDense.coordinateProjection (d + 1) d).contDiff.contMDiff.contMDiffAt.comp
    q.2.val (hfb.comp q.2.val hfa)

theorem mfderiv_originalMemberParameter
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothMemberOfDim p hp (affinePoint c.i q.1.val) d) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    ∀ v : ComplexModel d,
      mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) (c.originalMemberParameter q) q.2.val v =
        c.originalSliceParameterTangentEquiv hp q hsm v := by
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
  let g := c.originalMemberParameter q
  let inc := (Subtype.val : member p (affinePoint c.i q.1.val) → Y)
  let D : ComplexModel d →L[ℂ] TangentSpace 𝓘(ℂ, ComplexModel d) (c.originalSliceMemberPoint q) :=
    mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) g q.2.val
  let A := nativeOriginalChartTangentEquiv c.e (c.tangentPoint q) (c.tangentPoint_chart_coordinates q).1
  have hg := (c.contMDiffAt_originalMemberParameter hp q hsm).mdifferentiableAt (by simp)
  have hi := (SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ d) hsm.1).mdifferentiable (by simp) (g q.2.val)
  have hpoint := c.tangentPoint_chart_coordinates q
  have hgp : inc (g q.2.val) = c.tangentPoint q := by
    change (c.originalMemberParameter q q.2.val).val = c.tangentPoint q
    rw [c.originalMemberParameter_at q]
    rfl
  have hc : MDifferentiableAt 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1)) c.e.val
      (inc (g q.2.val)) := by
    rw [hgp]
    exact mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel (d + 1))) c.e.property hpoint.1
  have hinc := mfderiv_comp q.2.val hi hg
  have hchart := mfderiv_comp q.2.val hc (hi.comp q.2.val hg)
  have heq : (c.e.val ∘ (inc ∘ g)) =ᶠ[𝓝 q.2.val] c.originalTangentCoordinateMap q.1.val := by
    filter_upwards [c.isOpen_tangentPatch.mem_nhds q.2.property] with b hb
    rw [Function.comp_apply, Function.comp_apply,
      show g b = c.originalSliceMemberPoint (q.1, ⟨b, hb⟩) from c.originalMemberParameter_apply q hb]
    exact (c.tangentPoint_chart_coordinates (q.1, ⟨b, hb⟩)).2.1
  rw [hinc] at hchart
  intro v
  have hv := DFunLike.congr_fun hchart v
  rw [heq.mfderiv_eq, mfderiv_eq_fderiv] at hv
  change fderiv ℂ (c.originalTangentCoordinateMap q.1.val) q.2.val v =
    mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1)) c.e.val (inc (g q.2.val))
      (mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1)) inc (g q.2.val) (D v)) at hv
  have hgval : g q.2.val = c.originalSliceMemberPoint q := c.originalMemberParameter_at q
  rw [hgval] at hv
  apply (c.originalSliceNativeTangentEquiv hp q hsm).injective
  apply Subtype.ext
  rw [c.originalSliceParameterTangentEquiv_coordinates hp q hsm]
  change (c.originalSliceNativeTangentEquiv hp q hsm (D v)).val =
    fderiv ℂ (c.originalTangentCoordinateMap q.1.val) q.2.val v
  have hE := c.originalIntrinsicTangentEquiv_apply hp q hsm (D v)
  have hEA : (c.originalSliceNativeTangentEquiv hp q hsm (D v)).val =
      A (c.originalNativeInclusionDifferential hp q hsm (D v)) := by
    change A.symm ((c.originalSliceNativeTangentEquiv hp q hsm (D v)).val) =
      c.originalNativeInclusionDifferential hp q hsm (D v) at hE
    have h := congrArg A hE
    rw [LinearEquiv.apply_symm_apply] at h
    exact h
  rw [hEA]
  change fderiv ℂ (c.originalTangentCoordinateMap q.1.val) q.2.val v =
    mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1)) c.e.val (c.tangentPoint q)
      (c.originalNativeInclusionDifferential hp q hsm (D v)) at hv
  rw [nativeOriginalChartTangentEquiv_apply]
  exact hv.symm

variable [CompactSpace Y]

theorem originalCanonicalResidue_native_parameter_coefficient
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothMemberOfDim p hp (affinePoint c.i q.1.val) d) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    letI := isCompact_iff_compactSpace.mp (isClosed_member p hp.continuous (affinePoint c.i q.1.val)).isCompact
    ∀ α : (nativeCanonicalBundle (n := d + 1) (X := Y)).Fiber (c.tangentPoint q),
      nativeCanonicalFiberEquiv (n := d) (c.originalSliceMemberPoint q)
        (c.originalSliceCanonicalFiberResidueEquiv hp q hsm α)
        (fun j => mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d)
          (c.originalMemberParameter q) q.2.val (EuclideanSpace.single j 1)) =
      (c.tangentNormalDenominator q)⁻¹ *
        nativeCanonicalFiberInChart c.e (c.tangentPoint q) (c.tangentPoint_chart_coordinates q).1 α
          (Matrix.vecCons (EuclideanSpace.single c.m 1)
            (fun j => EuclideanSpace.single (c.m.succAbove j) 1)) := by
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
  let := isCompact_iff_compactSpace.mp (isClosed_member p hp.continuous (affinePoint c.i q.1.val)).isCompact
  intro α
  simp_rw [c.mfderiv_originalMemberParameter hp q hsm]
  exact c.originalCanonicalResidue_parameter_coefficient hp q hsm α

end SGPT.Trace.Bertini.SliceChart
