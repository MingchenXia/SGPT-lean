import SGPT.Checks.Comparison.TraceGFSequenceProducer
import SGPT.Checks.Comparison.ThinApprox.SourceApproximationAgreement
import SGPT.Checks.Comparison.TraceGFSequenceTrivialLimit

/-! The GIVEN GENERAL original NA curve, via the actual original BJ approximation.
Blueprint: `trace-na-general-family.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison

open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Envelope
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.PiecewiseLinearData
open SGPT.NAPotential.BJ.GfIm SGPT.NAPotential.BJ.GfIm.RationalHull
open SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open FixedGermNormalOrder DemaillyApproximantDivisorialLelong NativeImage NATrace
open scoped Topology Manifold ContDiff ENNReal

variable {X : Scheme.{0}} {L : X.Modules} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsIntegral X] [IsProjective f]
  (EX : ClosedProjectiveEmbedding f)
local instance traceGeneralTrivialProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance traceGeneralTrivialTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance traceGeneralTrivialCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance traceGeneralTrivialManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]

/-- The GIVEN GENERAL original curve at the actual native trivial image
has its actual unchanged trace maximum. Includes every target dimension
and ambient dimension zero; every actual GF/cutoff limit is internal. -/
theorem naPotentialAnAt_nativeTrivial_eq_traceMax
    {k : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
    [IsComplexManifold k V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
    (hk : k ≤ n) (omegaX : KahlerBackground n (SchemeComplexPoint f))
    (omegaV : KahlerBackground k V) {ι : V → SchemeComplexPoint f}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hvol : SGPT.Trace.RIsoB.PullbackKahlerVolumePos hι)
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) {d : ℕ} (hd : 0 < d)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((d : ℝ)⁻¹) • H.curvature a).val)
    (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ι Γ)
    (κX : SourceKahlerForm n (SchemeComplexPoint f)) (κV : SourceKahlerForm k V) (z : V) :
    naPotentialAnAt n EX Γ κX (NativeTrivial.point f n ι hι z) =
      ((((TraceRes.naTraceRes hk omegaX omegaV hι hvol Γ hwd).component κV).val.max : ℝ) : EReal) := by
  cases n with
  | zero =>
    exact naPotentialAnAt_eq_traceMax_of_ambient_dim_zero f EX hk omegaX omegaV hι hvol Γ hwd κX κV
      (NativeTrivial.point f 0 ι hι z)
  | succ r =>
    obtain ⟨S⟩ := exists_nativeGFSequence f r EX
      (SGPT.NAPotential.ThinApprox.BJ.SourceApproximationAgreement.original_approximation.{0} f)
      a H hd hθ Γ κX
    exact S.nativeTrivial_eq a H hd hθ hk omegaX omegaV hι hvol hwd κV z

end SGPT.NAPotential.TraceComparison
