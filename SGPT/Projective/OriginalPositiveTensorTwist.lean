import SGPT.Projective.OriginalPositiveLineRestriction
import SGPT.IGood.DXMainTensorMetric

/-! An ACTUAL original positive physical tensor twist of ANY original
line, with true original Chern form. Blueprint: original-positive-tensor-twist.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
  (E : ClosedProjectiveEmbedding f) {L : X.Modules} (a : LineBundleAtlas L)
  (H : SchemeLineBundleMetric f n E L) (A : OriginalPositiveLine f n E)

local instance twistTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance twistCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance twistManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

omit [IsSeparated f] [QuasiCompact f] in
/-- Actual original tensor metric and atlas on L tensor A^M retain their literal fixed Chern sum. -/
theorem originalTensorTwist_curvature (M : ℕ) :
    (((H.tensorProduct (A.metric.tensorPower A.atlas M) a (A.atlas.tensorPower M)).curvature
      (pairwiseTensorAtlas a (A.atlas.tensorPower M))).val).GeometricallyEq
        (H.curvature a + (M : ℝ) • A.curvature).val := by
  let := E.isSeparated
  let := E.quasiCompact
  have hT := H.curvature_tensorProduct (A.metric.tensorPower A.atlas M) a
    (A.atlas.tensorPower M) (pairwiseTensorAtlas a (A.atlas.tensorPower M))
  have hP := A.metric.curvature_tensorPower A.atlas M
  intro c z hz
  exact (hT c hz).trans (congrArg (fun η => (H.curvature a).val.coeff c z + η) (hP c hz))

/-- ANY actual original physical line inherits an actual positive original tensor twist. -/
theorem exists_positive_originalTensorTwist :
    ∃ M : ℕ, 0 < M ∧
      (((H.tensorProduct (A.metric.tensorPower A.atlas M) a (A.atlas.tensorPower M)).curvature
        (pairwiseTensorAtlas a (A.atlas.tensorPower M))).val).IsKahler := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let κ : KahlerBackground n (SchemeComplexPoint f) := ⟨A.curvature, A.positive⟩
  obtain ⟨C, hC, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul κ (H.curvature a)
  obtain ⟨M, hM⟩ := exists_nat_gt C
  have hM0 : 0 < M := by exact_mod_cast hC.trans hM
  have hη : (H.curvature a + (M : ℝ) • A.curvature).val.IsKahler := by
    refine ⟨fun c z hz => ⟨(H.curvature a + (M : ℝ) • A.curvature).property.2 c z hz,
      fun v hv => ?_⟩, (H.curvature a + (M : ℝ) • A.curvature).property.1⟩
    have h1 := hsemi c z hz v
    have h2 : 0 < A.curvature.val.coeff c z ![v, Complex.I • v] := (A.positive.1 c z hz).2 v hv
    simp only [κ, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h1 ⊢
    nlinarith [mul_pos (sub_pos.mpr hM) h2]
  exact ⟨M, hM0, (originalTensorTwist_curvature f n E a H A M).isKahler_iff.mpr hη⟩

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
