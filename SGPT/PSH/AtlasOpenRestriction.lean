import SGPT.PSH.AtlasNativeComponentInclusion

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

universe u
variable {X : Type u} [TopologicalSpace X]

private def nonemptyOpenRestriction (A : VariableComplexAtlas X) (U : Opens X)
    (hU : Nonempty U) : VariableComplexAtlas U where
  Index := A.Index
  dimension := A.dimension
  chart := fun i => (A.chart i).subtypeRestr hU
  cover := by
    intro p
    obtain ⟨i, hi⟩ := A.cover p.val
    exact ⟨i, by simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hi⟩
  holomorphic := by
    intro i j
    have hcoord : ContDiffOn ℂ ∞ (A.chart j ∘ id ∘ (A.chart i).symm)
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (id ⁻¹' (A.chart j).source)) := by
      simpa only [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source, Function.comp_id, Function.id_comp, preimage_id] using
        contDiffOn_of_differentiableOn_complex (A.holomorphic i j)
          ((A.chart i).symm.trans (A.chart j)).open_source
    have h := nativeOpenSubtypeCoordinate_contDiffOn (A.chart i) (A.chart j)
      rfl rfl U U hU hU id id (fun _ => rfl) hcoord
    simpa only [nativeCoordinateDimensionTransport, Function.comp_id, Function.id_comp,
      OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, preimage_id] using h.differentiableOn (by simp)

/-- ORIGINAL A and ANY actual original open give its genuine inherited
varying atlas. The empty branch has a truly empty chart index, never a model cert. -/
def openRestriction (A : VariableComplexAtlas X) (U : Opens X) : VariableComplexAtlas U := by
  classical
  by_cases hU : Nonempty U
  · exact nonemptyOpenRestriction A U hU
  · exact {
      Index := ULift.{u} (Fin 0)
      dimension := fun i => Fin.elim0 i.down
      chart := fun i => Fin.elim0 i.down
      cover := fun p => (hU ⟨p⟩).elim
      holomorphic := fun i => Fin.elim0 i.down }

/-- EVERY actual original point retains exactly its original local dimension;
its own membership internally rules out the genuinely empty branch. -/
theorem openRestriction_pointDimension (A : VariableComplexAtlas X) (U : Opens X) (p : U) :
    (A.openRestriction U).pointDimension p = A.pointDimension p.val := by
  classical
  have hU : Nonempty U := ⟨p⟩
  unfold openRestriction
  rw [dif_pos hU]
  obtain ⟨i, hi⟩ := A.cover p.val
  have hp : p ∈ ((nonemptyOpenRestriction A U hU).chart i).source := by
    simpa only [nonemptyOpenRestriction, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hi
  exact ((nonemptyOpenRestriction A U hU).pointDimension_eq_chart p i hp).trans
    (A.pointDimension_eq_chart p.val i hi).symm

/-- ANY actual original open has the SAME literal holomorphic inclusion,
with every original chart pair and no fixed native model/certificate. -/
theorem openRestriction_inclusion_isHolomorphic (A : VariableComplexAtlas X) (U : Opens X) :
    (A.openRestriction U).IsHolomorphic A (Subtype.val : U → X) := by
  classical
  by_cases hU : Nonempty U
  · unfold openRestriction
    rw [dif_pos hU]
    refine ⟨continuous_subtype_val, ?_⟩
    intro i j
    change DifferentiableOn ℂ (A.chart j ∘ Subtype.val ∘ ((A.chart i).subtypeRestr hU).symm)
      (((A.chart i).subtypeRestr hU).target ∩ ((A.chart i).subtypeRestr hU).symm ⁻¹'
        ((Subtype.val : U → X) ⁻¹' (A.chart j).source))
    let V : Opens X := ⊤
    let F : U → V := fun p => ⟨p.val, mem_univ _⟩
    have hV : Nonempty V := ⟨⟨(Classical.choice hU).val, mem_univ _⟩⟩
    have hcoord : ContDiffOn ℂ ∞ (A.chart j ∘ id ∘ (A.chart i).symm)
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (id ⁻¹' (A.chart j).source)) := by
      simpa only [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source, Function.comp_id, Function.id_comp, preimage_id] using
        contDiffOn_of_differentiableOn_complex (A.holomorphic i j)
          ((A.chart i).symm.trans (A.chart j)).open_source
    have h := nativeOpenSubtypeCoordinate_contDiffOn (A.chart i) (A.chart j)
      rfl rfl U V hU hV id F (fun _ => rfl) hcoord
    simp only [OpenPartialHomeomorph.subtypeRestr_source] at h
    change ContDiffOn ℂ ∞ (A.chart j ∘ Subtype.val ∘ ((A.chart i).subtypeRestr hU).symm)
      (((A.chart i).subtypeRestr hU).target ∩ ((A.chart i).subtypeRestr hU).symm ⁻¹'
        ((Subtype.val : U → X) ⁻¹' (A.chart j).source)) at h
    exact h.differentiableOn (by simp)
  · unfold openRestriction
    rw [dif_neg hU]
    refine ⟨continuous_subtype_val, ?_⟩
    intro i
    exact Fin.elim0 i.down

end SGPT.PSH.VariableComplexAtlas
