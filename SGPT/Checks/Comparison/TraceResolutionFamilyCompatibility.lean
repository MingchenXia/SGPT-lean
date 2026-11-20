import SGPT.Checks.Comparison.TraceGeneralResolutionFamily
import SGPT.Checks.Comparison.TraceNAResolutionCompatibility

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
local instance familyCompatibilityProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance familyCompatibilityTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance familyCompatibilityCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance familyCompatibilityManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]

/-- Original thm:comp_traceop read in the PRINTED resolution convention:
EVERY value of the actual unique trace family has the SAME ambient
restriction function on actual native divisorial/trivial classes.
The entire family is constructed independently under general Kahler
hypotheses; the rational primitive Chern scope is used only for ambient An. -/
theorem resolutionTraceFamily_ambient_compatibility
    (Y : ClosedIrreducibleAnalyticSubvariety n (SchemeComplexPoint f)) (R : ResolutionTarget Y)
    (omegaX : KahlerBackground n (SchemeComplexPoint f))
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) {d : ℕ} (hd : 0 < d)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((d : ℝ)⁻¹) • H.curvature a).val)
    (Γ : SourceNAPotential θ) (hwd : carrierTraceWellDefined Y Γ)
    (κX : SourceKahlerForm n (SchemeComplexPoint f)) (κR : SourceKahlerForm Y.dim R.V) :
    nativeDivisorialRestriction f n EX Y.dim_le omegaX R.kahler R.contMDiff
      (SGPT.Trace.RIsoB.pullbackKahlerVolumePos R) a H hd hθ Γ
      (carrierTraceWellDefined_on Y Γ hwd R) κX κR =
        nativeDivisorialFunction (resolutionTraceFamily Y omegaX Γ hwd R) κR :=
  nativeDivisorialRestriction_eq_trace f n EX Y.dim_le omegaX R.kahler R.contMDiff
    (SGPT.Trace.RIsoB.pullbackKahlerVolumePos R) a H hd hθ Γ
    (carrierTraceWellDefined_on Y Γ hwd R) κX κR

/-- The actual target AND target index in the final family comparison
are also internally constructed; the original carrier-wise condition,
original Gamma and primitive ambient Chern data are the source inputs. -/
theorem resolutionTraceFamily_chosen_ambient_compatibility
    (Y : ClosedIrreducibleAnalyticSubvariety n (SchemeComplexPoint f))
    (omegaX : KahlerBackground n (SchemeComplexPoint f))
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) {d : ℕ} (hd : 0 < d)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((d : ℝ)⁻¹) • H.curvature a).val)
    (Γ : SourceNAPotential θ) (hwd : carrierTraceWellDefined Y Γ)
    (κX : SourceKahlerForm n (SchemeComplexPoint f)) :
    let R := resolutionTraceTarget Y omegaX
    let κR := sourceKahlerFormOfBackground R.kahler
    nativeDivisorialRestriction f n EX Y.dim_le omegaX R.kahler R.contMDiff
      (SGPT.Trace.RIsoB.pullbackKahlerVolumePos R) a H hd hθ Γ
      (carrierTraceWellDefined_on Y Γ hwd R) κX κR =
        nativeDivisorialFunction (resolutionTraceFamily Y omegaX Γ hwd R) κR :=
  resolutionTraceFamily_ambient_compatibility f n EX Y (resolutionTraceTarget Y omegaX)
    omegaX a H hd hθ Γ hwd κX (sourceKahlerFormOfBackground (resolutionTraceTarget Y omegaX).kahler)

end SGPT.NAPotential.TraceComparison
