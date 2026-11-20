import SGPT.PSH.AtlasOpenRestriction
import SGPT.PSH.AtlasAnalyticModificationPullback

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

universe u
variable {X : Type u} [TopologicalSpace X]

/-- ORIGINAL A,U and an actual point internally give the SAME actual open
inclusion inverse, genuinely holomorphic ON U in EVERY original chart pair. -/
theorem openRestriction_inverse_isHolomorphicOn (A : VariableComplexAtlas X)
    (U : Opens X) (p : U) :
    A.IsHolomorphicOn (A.openRestriction U)
      (U.openPartialHomeomorphSubtypeCoe ⟨p⟩).symm (U : Set X) := by
  classical
  have hU : Nonempty U := ⟨p⟩
  let e := U.openPartialHomeomorphSubtypeCoe hU
  have ht : e.target = (U : Set X) := U.openPartialHomeomorphSubtypeCoe_target hU
  have hval (y : X) (hy : y ∈ (U : Set X)) : (e.symm y).val = y := by
    change e (e.symm y) = y
    exact e.right_inv (by rw [ht]; exact hy)
  unfold openRestriction
  rw [dif_pos hU]
  refine ⟨?_, ?_⟩
  · exact e.continuousOn_symm.mono (by
      intro y hy
      rw [ht]
      exact hy)
  · intro i j
    change DifferentiableOn ℂ ((A.chart j) ∘ Subtype.val ∘ e.symm ∘ (A.chart i).symm)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹'
        ((U : Set X) ∩ e.symm ⁻¹' ((A.chart j).subtypeRestr hU).source))
    have hsub : (A.chart i).target ∩ (A.chart i).symm ⁻¹'
        ((U : Set X) ∩ e.symm ⁻¹' ((A.chart j).subtypeRestr hU).source) ⊆
        (A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.chart j).source := by
      intro z hz
      refine ⟨hz.1, ?_⟩
      have hj := hz.2.2
      simp only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] at hj
      rw [hval _ hz.2.1] at hj
      exact hj
    have h := A.holomorphic i j
    change DifferentiableOn ℂ ((A.chart j) ∘ (A.chart i).symm)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.chart j).source) at h
    apply h.congr_mono ?_ hsub
    intro z hz
    change (A.chart j) (e.symm ((A.chart i).symm z)).val = (A.chart j) ((A.chart i).symm z)
    rw [hval _ hz.2.1]

/-- The EXISTING actual inclusion component map is genuinely an OPEN
embedding; both component qualifications and openness are manufactured. -/
theorem openRestriction_componentMap_isOpenEmbedding (A : VariableComplexAtlas X)
    (U : Opens X) (p : U) :
    Topology.IsOpenEmbedding ((A.openRestriction_inclusion_isHolomorphic U).componentMap p) := by
  let F := (A.openRestriction_inclusion_isHolomorphic U).componentMap p
  apply Topology.IsOpenEmbedding.of_comp F
    (A.componentOpen p.val).isOpen.isOpenEmbedding_subtypeVal
  exact U.isOpen.isOpenEmbedding_subtypeVal.comp
    (((A.openRestriction U).componentOpen p).isOpen.isOpenEmbedding_subtypeVal)

end SGPT.PSH.VariableComplexAtlas
