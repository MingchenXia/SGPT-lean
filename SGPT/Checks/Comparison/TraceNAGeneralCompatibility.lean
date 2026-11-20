import SGPT.Checks.Comparison.TraceGFSequenceProducer
import SGPT.Checks.Comparison.ThinApprox.SourceApproximationAgreement
import SGPT.Checks.Comparison.TraceGFSequenceNativeLimit

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
local instance traceGeneralCompatibilityProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance traceGeneralCompatibilityTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance traceGeneralCompatibilityCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance traceGeneralCompatibilityManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]

/-- The GIVEN GENERAL original curve, with the actual original BJ
approximation theorem PROVED internally in its exact original predicate. The
original curve's psh analytification, actual ample/Kahler perturbation,
all GF lifts/common transitions/infimum/trace limits are produced inside.
No family, image/value, order/bound or normalization certificate is input. -/
theorem naTraceRes_nativeDivisorial_eq
    {m : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel (m+1)) V]
    [IsComplexManifold (m+1) V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
    (hk : m+1 ≤ n) (omegaX : KahlerBackground n (SchemeComplexPoint f))
    (omegaV : KahlerBackground (m+1) V) {ι : V → SchemeComplexPoint f}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel (m+1)) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hvol : SGPT.Trace.RIsoB.PullbackKahlerVolumePos hι)
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) {d : ℕ} (hd : 0 < d)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((d : ℝ)⁻¹) • H.curvature a).val)
    (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ι Γ)
    (κX : SourceKahlerForm n (SchemeComplexPoint f)) (κV : SourceKahlerForm (m+1) V)
    (p : PrimePresentation (m+1) V) {z : p.model} (hz : z ∈ p.divisor)
    (Φ : DivisorFlattening (m := m) p.divisor z) (c : ℝ) (hc : 0 < c) :
    BJPrep.naDivisorialTransform (TraceRes.naTraceRes hk omegaX omegaV hι hvol Γ hwd) κV p c =
      naPotentialAnAt n EX Γ κX
        (nativeImagePoint f n (ι ∘ p.projection) (hι.comp p.modification.1) z Φ c hc) := by
  cases n with
  | zero => omega
  | succ r =>
    obtain ⟨S⟩ := exists_nativeGFSequence f r EX
      (SGPT.NAPotential.ThinApprox.BJ.SourceApproximationAgreement.original_approximation.{0} f)
      a H hd hθ Γ κX
    exact S.nativeDivisorial_eq a H hd hθ hk omegaX omegaV hι hvol hwd κV p hz Φ c hc

end SGPT.NAPotential.TraceComparison
