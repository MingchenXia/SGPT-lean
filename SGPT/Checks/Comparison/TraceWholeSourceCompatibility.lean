import SGPT.Checks.Comparison.TraceWholeSourceDefinition
import SGPT.Checks.Comparison.TraceResolutionFamilyCompatibility

/-! Original ambient analytification equals the divisorial reader of the
ACTUAL entire resolution-independent trace FAMILY. Exact source convention,
all positive real weights/trivial point/dimension zero. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison
open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Envelope
open SGPT.NAPotential.Berkovich SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver
open SGPT.Trace.Trace2Resolution
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open FixedGermNormalOrder DemaillyApproximantDivisorialLelong NATrace NativeImage
open scoped Topology Manifold ContDiff ENNReal

variable {X : Scheme.{0}} {L : X.Modules} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsIntegral X] [IsProjective f]
  (EX : ClosedProjectiveEmbedding f)
local instance wholeSourceCompatibilityProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance wholeSourceCompatibilityTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance wholeSourceCompatibilityCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance wholeSourceCompatibilityManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]

/-- WHOLE original thm:comp_traceop under the exact printed resolution
convention. The ACTUAL entire unique general-Kahler trace family has
original source formulas AND faithful actual same-common-model category
coherence, and its reader equals original ambient An on EVERY R/index.
No approximation, common-model or divisor-dictionary premise. Trivial
valuations and source/target dimensions zero are retained. -/
theorem source_comp_traceop
    (Y : ClosedIrreducibleAnalyticSubvariety n (SchemeComplexPoint f))
    (omegaX : KahlerBackground n (SchemeComplexPoint f))
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) {d : ℕ} (hd : 0 < d)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((d : ℝ)⁻¹) • H.curvature a).val)
    (Γ : SourceNAPotential θ) (hwd : carrierTraceWellDefined Y Γ)
    (κX : SourceKahlerForm n (SchemeComplexPoint f)) :
    IsOriginalResolutionTraceFamily Y Γ (resolutionTraceFamily Y omegaX Γ hwd) ∧
    ∀ (R : ResolutionTarget Y) (κR : SourceKahlerForm Y.dim R.V),
    nativeDivisorialRestriction f n EX Y.dim_le omegaX R.kahler R.contMDiff
      (SGPT.Trace.RIsoB.pullbackKahlerVolumePos R) a H hd hθ Γ
      (carrierTraceWellDefined_on Y Γ hwd R) κX κR =
        nativeDivisorialFunction (resolutionTraceFamily Y omegaX Γ hwd R) κR := by
  refine ⟨source_naTrace_family Y omegaX Γ hwd,?_⟩
  intro R κR
  exact resolutionTraceFamily_ambient_compatibility f n EX Y R omegaX a H hd hθ Γ hwd κX κR

end SGPT.NAPotential.TraceComparison
