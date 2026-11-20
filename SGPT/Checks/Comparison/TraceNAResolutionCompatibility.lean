import SGPT.Checks.Comparison.TraceNACanonicalRestriction

/-! Actual ORIGINAL irreducible Y / native ResolutionTarget comparison.
The original carrier-wise hwd is retained; actual volume positivity and
dimension inequality are produced internally from the SAME resolution.
Blueprint: trace-na-final-native.tex. No target algebraization.
-/
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
local instance resolutionCompatibilityProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance resolutionCompatibilityTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance resolutionCompatibilityCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance resolutionCompatibilityManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]

/-- The BOOK'S literal carrier-wise well-defined trace condition,
independent of every native resolution choice. -/
def sourceTraceWellDefinedOn
    (Y : ClosedIrreducibleAnalyticSubvariety n (SchemeComplexPoint f))
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (Γ : SourceNAPotential θ) : Prop :=
  ∀ κ : SourceKahlerForm n (SchemeComplexPoint f), ∃ s₀ : ℝ, ∀ s < s₀,
    ∃ h : s < (Γ.component κ).val.max,
      (ofFixedModel n (SchemeComplexPoint f)).sourceGenericLelong
        ((Γ.component κ).val.potential ⟨s,h⟩) Y.carrier = 0

/-- The actual original resolving target is constructed from the
accepted original theorem; no Hironaka development is performed here. -/
def sourceResolutionTarget
    (Y : ClosedIrreducibleAnalyticSubvariety n (SchemeComplexPoint f))
    (omegaX : KahlerBackground n (SchemeComplexPoint f)) : ResolutionTarget Y :=
  Classical.choice (SGPT.Trace.Trace2Resolution.exists_resolutionTarget omegaX Y)

omit [IsIntegral X] in
/-- Exact carrier-wise condition gives actual trace along EVERY SAME
actual native resolution, internally. -/
theorem sourceTraceWellDefinedOn_resolution_iff
    (Y : ClosedIrreducibleAnalyticSubvariety n (SchemeComplexPoint f)) (R : ResolutionTarget Y)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (Γ : SourceNAPotential θ) :
    TraceWellDefined R.ι Γ ↔ sourceTraceWellDefinedOn f n Y Γ :=
  TraceRes.traceWellDefined_resolution_iff R Γ

/-- Actual FUNCTION equality on the original native divisor quotient of
EVERY actual resolution of the original irreducible analytic Y.
No hvol/hk/target-field/reader certificate is supplied. -/
theorem naTraceResolution_divisorial_compatibility
    (Y : ClosedIrreducibleAnalyticSubvariety n (SchemeComplexPoint f)) (R : ResolutionTarget Y)
    (omegaX : KahlerBackground n (SchemeComplexPoint f))
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) {d : ℕ} (hd : 0 < d)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((d : ℝ)⁻¹) • H.curvature a).val)
    (Γ : SourceNAPotential θ) (hwd : sourceTraceWellDefinedOn f n Y Γ)
    (κX : SourceKahlerForm n (SchemeComplexPoint f)) (κR : SourceKahlerForm Y.dim R.V) :
    let hwR := (sourceTraceWellDefinedOn_resolution_iff f n Y R Γ).mpr hwd
    nativeDivisorialRestriction f n EX Y.dim_le omegaX R.kahler R.contMDiff
      (SGPT.Trace.RIsoB.pullbackKahlerVolumePos R) a H hd hθ Γ hwR κX κR =
        nativeDivisorialFunction (TraceRes.naTraceResolution R omegaX Γ hwR) κR := by
  dsimp only
  exact nativeDivisorialRestriction_eq_trace f n EX Y.dim_le omegaX R.kahler R.contMDiff
    (SGPT.Trace.RIsoB.pullbackKahlerVolumePos R) a H hd hθ Γ
    ((sourceTraceWellDefinedOn_resolution_iff f n Y R Γ).mpr hwd) κX κR

/-- The resolving target and target Kähler index are ALSO produced
internally. Original Y, original Gamma, original book hwd and original
primitive Chern normalization are the entire source input. -/
theorem naTraceOnSubvariety_divisorial_compatibility
    (Y : ClosedIrreducibleAnalyticSubvariety n (SchemeComplexPoint f))
    (omegaX : KahlerBackground n (SchemeComplexPoint f))
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) {d : ℕ} (hd : 0 < d)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((d : ℝ)⁻¹) • H.curvature a).val)
    (Γ : SourceNAPotential θ) (hwd : sourceTraceWellDefinedOn f n Y Γ)
    (κX : SourceKahlerForm n (SchemeComplexPoint f)) :
    let R := sourceResolutionTarget f n Y omegaX
    let hwR := (sourceTraceWellDefinedOn_resolution_iff f n Y R Γ).mpr hwd
    let κR := sourceKahlerFormOfBackground R.kahler
    nativeDivisorialRestriction f n EX Y.dim_le omegaX R.kahler R.contMDiff
      (SGPT.Trace.RIsoB.pullbackKahlerVolumePos R) a H hd hθ Γ hwR κX κR =
        nativeDivisorialFunction (TraceRes.naTraceResolution R omegaX Γ hwR) κR :=
  naTraceResolution_divisorial_compatibility f n EX Y (sourceResolutionTarget f n Y omegaX)
    omegaX a H hd hθ Γ hwd κX (sourceKahlerFormOfBackground (sourceResolutionTarget f n Y omegaX).kahler)

end SGPT.NAPotential.TraceComparison
