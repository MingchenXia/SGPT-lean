import SGPT.Foundations.Analysis.Pending.CompactAffineCurveCharts
import Mathlib.Topology.Separation.Regular

set_option autoImplicit false

/-!
# Actual nested affine curve regions

Internally produce the actual compact inverse-chart image of a complex test
set and three open collars whose closures stay in the true chart and prescribed
open time domain. No chart-fit or collar certificate is assumed.
-/

open Set Filter Topology
open scoped Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.CompactAffineCurveRegions

open FirstPass CompactAffineCurveCharts

noncomputable section

/-- The model affine time is the true inverse of the contracted embedding. -/
theorem model_affine_left_inverse (z0 : ComplexModel 1) {δ : ℝ} (hδ : δ ≠ 0) (τ : ℂ) :
    curveModelEquiv (δ⁻¹ • (z0 + δ • curveModelEquiv.symm τ - z0)) = τ := by
  simp only [add_sub_cancel_left, inv_smul_smul₀ hδ,
    ContinuousLinearEquiv.apply_symm_apply]

/-- The contracted model embedding is the true inverse of affine time. -/
theorem model_affine_right_inverse (z0 z : ComplexModel 1) {δ : ℝ} (hδ : δ ≠ 0) :
    z0 + δ • curveModelEquiv.symm (curveModelEquiv (δ⁻¹ • (z - z0))) = z := by
  simp only [ContinuousLinearEquiv.symm_apply_apply, smul_inv_smul₀ hδ]
  abel

variable {T : Type*} [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T]
  [IsComplexManifold 1 T] [CompactSpace T]

/-- Actual compact time tests have three internally produced genuine curve collars. -/
theorem exists_compact_affine_curve_regions (p : T) {K S : Set ℂ}
    (hK : IsCompact K) (hS : IsOpen S) (hKS : K ⊆ S) :
    ∃ (e : ComplexChart 1 T) (z0 : ComplexModel 1) (δ : ℝ) (V1 V2 V3 : Set T),
      z0 ∈ e.val.target ∧ 0 < δ ∧
      (∀ τ ∈ K, z0 + δ • curveModelEquiv.symm τ ∈ e.val.target) ∧
      IsCompact ((fun τ => e.val.symm (z0 + δ • curveModelEquiv.symm τ)) '' K) ∧
      IsOpen V1 ∧ IsOpen V2 ∧ IsOpen V3 ∧
      (fun τ => e.val.symm (z0 + δ • curveModelEquiv.symm τ)) '' K ⊆ V1 ∧
      closure V1 ⊆ V2 ∧ closure V2 ⊆ V3 ∧ closure V3 ⊆ e.val.source ∧
      ∀ y ∈ closure V3, curveModelEquiv (δ⁻¹ • (e.val y - z0)) ∈ S := by
  obtain ⟨e, z0, δ, hz0, hδ, hfit⟩ := exists_compact_affine_curve_chart p hK
  let F : ℂ → ComplexModel 1 := fun τ => z0 + δ • curveModelEquiv.symm τ
  let G : T → ℂ := fun y => curveModelEquiv (δ⁻¹ • (e.val y - z0))
  let KT : Set T := (fun τ => e.val.symm (F τ)) '' K
  have hF : Continuous F := by fun_prop
  have hKT : IsCompact KT := by
    apply hK.image_of_continuousOn
    simpa only [Function.comp_def] using
      e.val.symm.continuousOn.comp hF.continuousOn hfit
  have hG : ContinuousOn G e.val.source := by
    exact curveModelEquiv.continuous.comp_continuousOn
      ((e.val.continuousOn.sub continuousOn_const).const_smul δ⁻¹)
  let O : Set T := e.val.source ∩ G ⁻¹' S
  have hO : IsOpen O := hG.isOpen_inter_preimage e.val.open_source hS
  have hKTO : KT ⊆ O := by
    rintro _ ⟨τ, hτ, rfl⟩
    refine ⟨e.val.map_target (hfit τ hτ), ?_⟩
    change curveModelEquiv (δ⁻¹ • (e.val (e.val.symm (F τ)) - z0)) ∈ S
    rw [e.val.right_inv (hfit τ hτ)]
    simpa only [F, model_affine_left_inverse z0 (ne_of_gt hδ)] using hKS hτ
  obtain ⟨V3, hV3, hKTV3, hcl3⟩ :=
    hKT.exists_isOpen_closure_subset (hO.mem_nhdsSet.mpr hKTO)
  obtain ⟨V2, hV2, hKTV2, hcl2⟩ :=
    hKT.exists_isOpen_closure_subset (hV3.mem_nhdsSet.mpr hKTV3)
  obtain ⟨V1, hV1, hKTV1, hcl1⟩ :=
    hKT.exists_isOpen_closure_subset (hV2.mem_nhdsSet.mpr hKTV2)
  refine ⟨e, z0, δ, V1, V2, V3, hz0, hδ, hfit, hKT,
    hV1, hV2, hV3, hKTV1, hcl1, hcl2, ?_, ?_⟩
  · exact fun y hy => (hcl3 hy).1
  · exact fun y hy => (hcl3 hy).2

end

end SGPT.Foundations.Analysis.Pending.CompactAffineCurveRegions
