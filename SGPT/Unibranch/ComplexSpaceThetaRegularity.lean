import SGPT.Unibranch.ComplexSpaceThetaPSH
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialIndependence

/-! Actual regularity of original theta-PSH on arbitrary singular spaces.
Blueprint: complex-space-theta-regularity.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology ContDiff
open SGPT.Foundations.Analysis.FirstPass
namespace SGPT.Unibranch.SourceReducedComplexSpace

private theorem finite_corrected_cancel (a : EReal) (r : ℝ) :
    ((r : EReal)+a)+((-r : ℝ) : EReal) = a :=
  (congrArg (fun b : EReal => b+((-r : ℝ) : EReal)) (add_comm (r : EReal) a)).trans (by
    simpa only [zero_sub,EReal.coe_zero,add_zero] using corrected_add_sub a r 0)

/-- Original theta-PSH never takes top values on the original singular space. -/
theorem IsThetaPSH.ne_top {X : SourceReducedComplexSpace} {θ : SpaceForm X 2}
    {φ : X.obj.left → EReal} (hφ : X.IsThetaPSH θ φ) (x : X.obj.left) : φ x ≠ ⊤ := by
  obtain ⟨e,⟨c,rfl⟩,-,g,-,-,hpsh⟩ := hφ x
  intro htop
  have h := hpsh.ne_top c
  simp [htop,EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)] at h

/-- Upper semicontinuity is derived from the actual corrected original
PSH model and finite smooth-gauge cancellation in the SAME original topology. -/
theorem IsThetaPSH.upperSemicontinuous {X : SourceReducedComplexSpace} {θ : SpaceForm X 2}
    {φ : X.obj.left → EReal} (hφ : X.IsThetaPSH θ φ) : UpperSemicontinuous φ := by
  intro x
  obtain ⟨e,⟨c,rfl⟩,-,g,hg,-,hpsh⟩ := hφ x
  have hcoords : Continuous (fun b : e.carrier => b.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hgC : Continuous (fun b : e.carrier => g b.val.val) :=
    hg.continuousOn.comp_continuous hcoords (fun b => b.val.property)
  have hminus : Continuous (fun b : e.carrier => ((-g b.val.val : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp hgC.neg
  have hu : UpperSemicontinuousAt (fun b : e.carrier =>
      (g b.val.val : EReal)+φ (e.toPoint b)) c := hpsh.upperSemicontinuous c
  have hm : UpperSemicontinuousAt (fun b : e.carrier => ((-g b.val.val : ℝ) : EReal)) c :=
    hminus.continuousAt.upperSemicontinuousAt
  have hsum := UpperSemicontinuousAt.add' hu hm
    (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _)))
  have heq : (fun b : e.carrier =>
      ((g b.val.val : EReal)+φ (e.toPoint b))+((-g b.val.val : ℝ) : EReal)) =
      (fun b : e.carrier => φ (e.toPoint b)) := by
    funext b
    exact finite_corrected_cancel _ _
  rw [heq] at hsum
  intro a ha
  rw [← e.isOpenEmbedding_toPoint.map_nhds_eq c]
  exact eventually_map.mpr (hsum a ha)

end SGPT.Unibranch.SourceReducedComplexSpace
