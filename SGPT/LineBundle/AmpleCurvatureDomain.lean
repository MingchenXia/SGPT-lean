import SGPT.LineBundle.AmplePositiveMetric
import SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy

/-! Actual original ampleness supplies both positive-class hypotheses for DH. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.LineBundle.AmpleChern
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) (E : ClosedProjectiveEmbedding f)
  [SmoothOfRelativeDimension n f]

local instance : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- The SAME original ample line and arbitrary metric produce actual Kähler and big class data. -/
theorem originalAmple_curvature_domain {L : X.Modules}
    (P : AmplePolarization f L) (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L) :
    letI := E.isSeparated
    letI := E.quasiCompact
    (∃ ω : ClosedRealOneOneForm n (SchemeComplexPoint f), ω.val.IsKahler ∧
      RealBottChern.ofRepresentative ω = RealBottChern.ofRepresentative (H.curvature a)) ∧
    IsBigClass (RealBottChern.ofRepresentative (H.curvature a)) := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨K, hK⟩ := exists_positive_metric_of_amplePolarization f n E P a
  have hc : RealBottChern.ofRepresentative (K.curvature a) =
      RealBottChern.ofRepresentative (H.curvature a) := K.chernClass_independent H a a
  refine ⟨⟨K.curvature a, hK, hc⟩, ?_⟩
  rw [← hc]
  exact PluripolarCapacityDichotomy.isBigClass_kahler ⟨K.curvature a, hK⟩

end SGPT.LineBundle.AmpleChern
