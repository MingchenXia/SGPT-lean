import SGPT.Trace.BertiniOriginalOpenMemberParameter

/-! Actual original multi-parameter member image is an internally produced open set. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini.SliceChart

open Bundle Set Filter Metric TensorProduct
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open ProductComplexManifold
open scoped ProductComplexManifold

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  {p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞}
  {φ : X → EReal} (c : SliceChart (d + 1) (p : X → ComplexProjectiveSpace N) φ)

theorem flatProj_tangentLift_coordinateDelete (ζ : ComplexModel N) (z : ComplexModel (d + 1)) :
    flatProj c.m (prodModelEquiv N (d + 1) (ζ,c.tangentLift (originalMemberCoordinateDelete c.m z))) =
      flatProj c.m (prodModelEquiv N (d + 1) (ζ,z)) := by
  apply (prodModelEquiv N (d + 1)).symm.injective
  apply Prod.ext
  · simp only [fst_symm_flatProj,ContinuousLinearEquiv.symm_apply_apply]
  · rw [snd_symm_flatProj,snd_symm_flatProj]
    simp only [slCoord_apply,ContinuousLinearEquiv.symm_apply_apply]
    ext k
    rcases Fin.eq_self_or_eq_succAbove c.m k with rfl | ⟨j,rfl⟩ <;>
      simp [tangentLift,tangentCoordinateInsert,originalMemberCoordinateDelete,Fin.succAbove_ne]

def originalSliceAmbientSource (ζ : ComplexModel N) : TopologicalSpace.Opens X := by
  let R : Set (ComplexModel (d + 1)) :=
    (fun z => prodModelEquiv N (d + 1) (ζ,z)) ⁻¹' c.Φ.source ∩
      (originalMemberCoordinateDelete c.m) ⁻¹' c.tangentPatch
  have hR : IsOpen R :=
    (c.Φ.isOpen_source.preimage ((prodModelEquiv N (d + 1)).continuous.comp
      (continuous_const.prodMk continuous_id))).inter
      (c.isOpen_tangentPatch.preimage (originalMemberCoordinateDelete c.m).continuous)
  exact ⟨c.e.val.source ∩ c.e.val ⁻¹' R,c.e.val.isOpen_inter_preimage hR⟩

def originalSliceMemberSource (ζ : ComplexModel N) :
    TopologicalSpace.Opens (member p (affinePoint c.i ζ)) :=
  ⟨(Subtype.val : member p (affinePoint c.i ζ) → X) ⁻¹' c.originalSliceAmbientSource ζ,
    (c.originalSliceAmbientSource ζ).isOpen.preimage continuous_subtype_val⟩

theorem originalOpenMemberParameter_mem_source (ζ : ball c.ζ₀ c.r)
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint c.i ζ.val)) :
    letI := nativeBertiniMemberChartedSpace p c.i ζ.val hsm
    letI := nativeBertiniMemberComplex p c.i ζ.val hsm
    ∀ u : c.originalTangentPatchOpen,
      c.originalOpenMemberParameter ζ hsm u ∈ c.originalSliceMemberSource ζ.val := by
  let := nativeBertiniMemberChartedSpace p c.i ζ.val hsm
  let := nativeBertiniMemberComplex p c.i ζ.val hsm
  intro u
  let t := flatProj c.m (prodModelEquiv N (d + 1) (ζ.val,c.tangentLift u.val))
  have ht : t ∈ c.Φ.target := c.mapsTo_target ζ.val ζ.property (c.tangentLift u.val) u.property
  have hp := c.tangentPoint_chart_coordinates (ζ,u)
  have hw : prodModelEquiv N (d + 1) (ζ.val,c.e.val (c.tangentPoint (ζ,u))) = c.Φ.invFun t := by
    apply (prodModelEquiv N (d + 1)).symm.injective
    rw [ContinuousLinearEquiv.symm_apply_apply]
    apply Prod.ext
    · simpa only [t,fst_symm_flatProj,ContinuousLinearEquiv.symm_apply_apply] using (c.fst_invFun ht).symm
    · exact hp.2.1
  change (c.originalOpenMemberParameter ζ hsm u).val ∈ c.originalSliceAmbientSource ζ.val
  rw [c.originalOpenMemberParameter_apply ζ hsm u]
  refine ⟨hp.1,?_,?_⟩
  · change prodModelEquiv N (d + 1) (ζ.val,c.e.val (c.tangentPoint (ζ,u))) ∈ c.Φ.source
    exact hw.symm ▸ c.Φ.mapsTo_invFun ht
  · have hd := c.originalOpenMemberParameter_coordinateDelete ζ hsm u
    change originalMemberCoordinateDelete c.m (c.e.val (c.tangentPoint (ζ,u))) = u.val at hd
    change originalMemberCoordinateDelete c.m (c.e.val (c.tangentPoint (ζ,u))) ∈ c.tangentPatch
    exact hd.symm ▸ u.property

theorem originalOpenMemberParameter_reconstruct (ζ : ball c.ζ₀ c.r)
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint c.i ζ.val)) :
    letI := nativeBertiniMemberChartedSpace p c.i ζ.val hsm
    letI := nativeBertiniMemberComplex p c.i ζ.val hsm
    ∀ (y : member p (affinePoint c.i ζ.val)) (hy : y ∈ c.originalSliceMemberSource ζ.val),
      c.originalOpenMemberParameter ζ hsm ⟨originalMemberCoordinateDelete c.m (c.e.val y.val),hy.2.2⟩ = y := by
  let := nativeBertiniMemberChartedSpace p c.i ζ.val hsm
  let := nativeBertiniMemberComplex p c.i ζ.val hsm
  intro y hy
  let z := c.e.val y.val
  let w := prodModelEquiv N (d + 1) (ζ.val,z)
  let u : c.originalTangentPatchOpen := ⟨originalMemberCoordinateDelete c.m z,hy.2.2⟩
  have hdom : c.e.val y.val ∈ chartLiftDomain p c.e c.j := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using (c.source_subset hy.2.1).2
  have hpx : p y.val ∈ (affineChart c.j).source := (mem_chartLiftDomain_iff p hy.1).mp hdom
  have hg := c.originalFixedMemberEquation_zero (ζ,u) hy.1 hpx y.property
  unfold originalFixedMemberEquation at hg
  have hg0 : conormalGenerator p c.i c.e c.j 0 w = 0 := by
    simpa only [w,z,conormalGenerator,Fin.cons_zero,ContinuousLinearEquiv.symm_apply_apply] using hg
  have hflat : c.Φ.toFun w = flatProj c.m w := by
    rw [c.toFun_eq]
    exact flatMap_eq_flatProj p hg0
  have ht : flatProj c.m (prodModelEquiv N (d + 1) (ζ.val,c.tangentLift u.val)) = c.Φ.toFun w :=
    (c.flatProj_tangentLift_coordinateDelete ζ.val z).trans hflat.symm
  have hi : c.Φ.invFun (flatProj c.m (prodModelEquiv N (d + 1) (ζ.val,c.tangentLift u.val))) = w := by
    rw [ht]
    exact c.Φ.left_inv w hy.2.1
  have hz : c.originalTangentCoordinateMap ζ.val u.val = z := by
    change ((prodModelEquiv N (d + 1)).symm (c.Φ.invFun
      (flatProj c.m (prodModelEquiv N (d + 1) (ζ.val,c.tangentLift u.val))))).2 = z
    rw [hi,ContinuousLinearEquiv.symm_apply_apply]
  apply Subtype.ext
  change c.e.val.symm (c.originalTangentCoordinateMap ζ.val u.val) = y.val
  rw [hz]
  exact c.e.val.left_inv hy.1

theorem originalOpenMemberParameter_range (ζ : ball c.ζ₀ c.r)
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint c.i ζ.val)) :
    letI := nativeBertiniMemberChartedSpace p c.i ζ.val hsm
    letI := nativeBertiniMemberComplex p c.i ζ.val hsm
    Set.range (c.originalOpenMemberParameter ζ hsm) = c.originalSliceMemberSource ζ.val := by
  let := nativeBertiniMemberChartedSpace p c.i ζ.val hsm
  let := nativeBertiniMemberComplex p c.i ζ.val hsm
  ext y
  constructor
  · rintro ⟨u,rfl⟩
    exact c.originalOpenMemberParameter_mem_source ζ hsm u
  · intro hy
    exact ⟨⟨originalMemberCoordinateDelete c.m (c.e.val y.val),hy.2.2⟩,
      c.originalOpenMemberParameter_reconstruct ζ hsm y hy⟩

end SGPT.Trace.Bertini.SliceChart
