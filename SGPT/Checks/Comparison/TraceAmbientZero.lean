import SGPT.Checks.Comparison.TraceNativeTrivialFS
import SGPT.NAPotential.TraceResNATrace

/-! Original trace compatibility in ambient dimension zero, for EVERY curve.
Blueprint: `trace-gf-actual-hull.tex`. No rational GF or prime certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SGPT.NAPotential.TraceComparison

open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Envelope
open SGPT.NAPotential.Berkovich SGPT.NAPotential.NATrace SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SourceTraceRepresentativeDefinition
open scoped Topology Manifold ContDiff ENNReal

/-- Every ACTUAL original NA curve in ambient dimension zero has
well-defined ACTUAL trace along EVERY nonempty actual target. -/
theorem traceWellDefined_of_ambient_dim_zero
    {M V : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel 0) M]
    [IsComplexManifold 0 M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
    [Nonempty V] {θ : AtlasClosedRealOneOneForm (ofFixedModel 0 M)}
    (Γ : SourceNAPotential θ) (ι : V → M) : TraceWellDefined ι Γ := by
  intro κ
  exact ⟨(Γ.component κ).val.max, fun s hs =>
    ⟨hs,sourceGenericLelongNumber_zero_dimension rfl ι _⟩⟩

/-- The ACTUAL original trace cutoff is the ACTUAL ambient maximum,
internally, in dimension zero and for EVERY actual original curve. -/
theorem traceCutoff_eq_max_of_ambient_dim_zero
    {M V : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel 0) M]
    [IsComplexManifold 0 M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
    [Nonempty V] {θ : AtlasClosedRealOneOneForm (ofFixedModel 0 M)}
    (Γ : SourceNAPotential θ) (ι : V → M) (κ : SourceKahlerForm 0 M) :
    traceCutoff ι Γ κ = (Γ.component κ).val.max := by
  refine le_antisymm (traceCutoff_le_max (traceWellDefined_of_ambient_dim_zero Γ ι) κ) ?_
  apply le_of_forall_lt_imp_le_of_dense
  intro s hs
  exact le_csSup (traceCutoff_set_bddAbove ι Γ κ)
    ⟨hs,sourceGenericLelongNumber_zero_dimension rfl ι _⟩

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 0 f]
  (EX : ClosedProjectiveEmbedding f) [IsProper f]
local instance traceAmbientZeroTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance traceAmbientZeroCharts : ChartedSpace (ComplexModel 0) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f 0
local instance traceAmbientZeroManifold : IsComplexManifold 0 (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f 0
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]

/-- The BOOK'S ambient-dimension-zero trace/analytification identity at
EVERY actual ambient point, for EVERY actual original NA curve. -/
theorem naPotentialAnAt_eq_traceMax_of_ambient_dim_zero
    {k : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
    [IsComplexManifold k V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
    (hk : k ≤ 0) (omegaX : KahlerBackground 0 (SchemeComplexPoint f))
    (omegaV : KahlerBackground k V) {ι : V → SchemeComplexPoint f}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel 0) ∞ ι)
    (hvol : SGPT.Trace.RIsoB.PullbackKahlerVolumePos hι)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel 0 (SchemeComplexPoint f))}
    (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ι Γ)
    (κX : SourceKahlerForm 0 (SchemeComplexPoint f)) (κV : SourceKahlerForm k V)
    (v : BerkovichPoint f) :
    naPotentialAnAt 0 EX Γ κX v =
      ((((TraceRes.naTraceRes hk omegaX omegaV hι hvol Γ hwd).component κV).val.max : ℝ) : EReal) := by
  rw [NANS.naPotentialAnAt_eq_of_dim_zero, TraceRes.naTraceRes_max hk omegaX omegaV hι hvol Γ hwd κV κX,
    traceCutoff_eq_max_of_ambient_dim_zero]

end SGPT.NAPotential.TraceComparison
