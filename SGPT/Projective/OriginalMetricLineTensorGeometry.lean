import SGPT.Projective.OriginalPositiveTensorTwist
import SGPT.Foundations.Schemes.TensorSectionZeroIdeals
import SGPT.NAPotential.FSPosKahler
import SGPT.Foundations.Analysis.Pending.ExceptionalMetricProof

/-! Only actual original sheaf/atlas/physical-metric data and their genuine
literal tensor/power curvatures and positive twists.
Blueprint: original-metric-line-tensor-geometry.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
local instance metricLineTensorTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance metricLineTensorCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance metricLineTensorManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- Ordinary original data only, with no positivity, curve, number, class,
period or comparison field. -/
structure OriginalMetricLine where
  sheaf : X.Modules
  atlas : LineBundleAtlas sheaf
  metric : SchemeLineBundleMetric f n E sheaf

namespace OriginalMetricLine
variable {f n E}

def toIntrinsic (A : OriginalMetricLine f n E) : IntrinsicLineBundle X := ⟨A.sheaf,A.atlas⟩
def curvature (A : OriginalMetricLine f n E) :
    letI := E.isSeparated;letI := E.quasiCompact;ClosedRealOneOneForm n (SchemeComplexPoint f) :=
  A.metric.curvature A.atlas

def tensor (A B : OriginalMetricLine f n E) : OriginalMetricLine f n E where
  sheaf := bundleTensor A.sheaf B.sheaf
  atlas := A.atlas.tensor B.atlas
  metric := A.metric.tensorProduct B.metric A.atlas B.atlas

def power (A : OriginalMetricLine f n E) (r : ℕ) : OriginalMetricLine f n E where
  sheaf := bundleTensorPower A.sheaf r
  atlas := A.atlas.tensorPower r
  metric := A.metric.tensorPower A.atlas r

/-- Actual tensor physical Chern coefficients, for the SAME original tensor atlas. -/
theorem tensor_curvature (A B : OriginalMetricLine f n E) :
    letI := E.isSeparated
    letI := E.quasiCompact
    (A.tensor B).curvature.val.GeometricallyEq (A.curvature+B.curvature).val :=
  A.metric.curvature_tensorProduct B.metric A.atlas B.atlas (A.atlas.tensor B.atlas)

/-- Actual original power physical Chern coefficients, including power zero. -/
theorem power_curvature (A : OriginalMetricLine f n E) (r : ℕ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    (A.power r).curvature.val.GeometricallyEq ((r:ℝ) • A.curvature).val :=
  A.metric.curvature_tensorPower A.atlas r

def Positive (A : OriginalMetricLine f n E) : Prop :=
  letI := E.isSeparated;letI := E.quasiCompact;A.curvature.val.IsKahler

/-- Every actual original metric line admits a genuine positive tensor twist
by a genuinely positive actual original metric line; no Chern/period premise. -/
theorem exists_positive_tensor_twist (A : OriginalMetricLine f n E) :
    ∃ B : OriginalMetricLine f n E, B.Positive ∧ (A.tensor B).Positive := by
  let := E.isSeparated
  let := E.quasiCompact
  let P : OriginalPositiveLine f n E := {
    sheaf := SGPT.NAPotential.FSPos.hyperplaneBundle E
    atlas := SGPT.NAPotential.FSPos.hyperplaneAtlas E
    metric := SGPT.NAPotential.FSPos.fubiniStudyMetric f E n
    positive := SGPT.NAPotential.FSPos.fubiniStudy_isKahler f E n }
  obtain ⟨r,hr,hpos⟩ := exists_positive_originalTensorTwist f n E A.atlas A.metric P
  let R : OriginalMetricLine f n E := ⟨P.sheaf,P.atlas,P.metric⟩
  let B := R.power r
  refine ⟨B,?_,?_⟩
  · have hgeo := R.power_curvature r
    have hrR : (0:ℝ)<r := by exact_mod_cast hr
    have hR : R.curvature.val.IsKahler := P.positive
    have hscale : ((r:ℝ) • R.curvature).val.IsKahler :=
      ExceptionalMetricProof.isKahler_of_isStrictlyPositive fun e z hz v hv => by
        have h := (hR.1 e z hz).2 v hv
        simp only [ClosedRealOneOneForm.coeff_smul,ContinuousAlternatingMap.smul_apply,smul_eq_mul]
        exact mul_pos hrR h
    exact hgeo.isKahler_iff.mpr hscale
  · let HT := A.metric.tensorProduct (P.metric.tensorPower P.atlas r) A.atlas (P.atlas.tensorPower r)
    have hgeo := HT.curvature_atlas_geometricallyEq
      (A.atlas.tensor (P.atlas.tensorPower r)) (pairwiseTensorAtlas A.atlas (P.atlas.tensorPower r))
    exact hgeo.isKahler_iff.mpr hpos
end OriginalMetricLine
end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
