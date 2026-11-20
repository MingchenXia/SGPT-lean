import SGPT.Checks.Comparison.TraceAmbientZero
import SGPT.Checks.Comparison.TraceGFRealizedCompatibility
import SGPT.Checks.Comparison.TraceGFRealizedTrivialCompatibility
import SGPT.NAPotential.TowerAlgReflect
import SGPT.Checks.Comparison.GFRationalHullImage

/-! The GIVEN original NA curve with ORIGINAL rational GF analytification.
Blueprint: `trace-gf-actual-hull.tex`. -/
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
local instance traceGivenGFProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance traceGivenGFTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance traceGivenGFCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance traceGivenGFManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]

/-- **The ORIGINAL rational GF case for the GIVEN original NA curve.**
The same primitive line bundle, metric, positive rational denominator and
Chern equality produce the actual original hull internally; actual full
analytification injectivity identifies the GIVEN curve with that hull.
No hull, section-family, trace/reader or image-value certificate is an input. -/
theorem naTraceRes_nativeDivisorial_eq_of_isRationalGF
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
    (hGF : IsRationalGF f ((d : ℚ)⁻¹ • rationalPicardClass a) (naPotentialAnAt n EX Γ κX))
    (p : PrimePresentation (m+1) V) {z : p.model} (hz : z ∈ p.divisor)
    (Φ : DivisorFlattening (m := m) p.divisor z) (c : ℝ) (hc : 0 < c) :
    BJPrep.naDivisorialTransform (TraceRes.naTraceRes hk omegaX omegaV hι hvol Γ hwd) κV p c =
      naPotentialAnAt n EX Γ κX
        (nativeImagePoint f n (ι ∘ p.projection) (hι.comp p.modification.1) z Φ c hc) := by
  cases n with
  | zero => omega
  | succ r =>
    obtain ⟨D,hD,hAn⟩ := exists_originalHull_naPotentialAnAt_eq_of_isRationalGF
      f (r+1) EX a H hd hθ hGF
    have hΓ : hullNAPotential D = Γ :=
      (TowerAlg.naPotentialAnAt_injective (E := EX) κX) (hAn κX)
    have hwD : TraceWellDefined ι (hullNAPotential D) := hΓ.symm ▸ hwd
    simpa only [hΓ] using realizedHull_naTraceRes_nativeDivisorial_eq f (r+1) EX
      hk omegaX omegaV hι hvol a H hd D hD hwD κX κV p hz Φ c hc

/-- The SAME GIVEN original rational-GF NA curve at the actual native
trivial image equals its ACTUAL unchanged trace maximum, including BOTH original
ambient and native target dimension zero. -/
theorem naPotentialAnAt_nativeTrivial_eq_traceMax_of_isRationalGF
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
    (κX : SourceKahlerForm n (SchemeComplexPoint f)) (κV : SourceKahlerForm k V)
    (hGF : IsRationalGF f ((d : ℚ)⁻¹ • rationalPicardClass a) (naPotentialAnAt n EX Γ κX))
    (z : V) :
    naPotentialAnAt n EX Γ κX (NativeTrivial.point f n ι hι z) =
      ((((TraceRes.naTraceRes hk omegaX omegaV hι hvol Γ hwd).component κV).val.max : ℝ) : EReal) := by
  cases n with
  | zero =>
    exact naPotentialAnAt_eq_traceMax_of_ambient_dim_zero f EX hk omegaX omegaV hι hvol Γ hwd κX κV
      (NativeTrivial.point f 0 ι hι z)
  | succ r =>
    obtain ⟨D,hD,hAn⟩ := exists_originalHull_naPotentialAnAt_eq_of_isRationalGF
      f (r+1) EX a H hd hθ hGF
    have hΓ : hullNAPotential D = Γ :=
      (TowerAlg.naPotentialAnAt_injective (E := EX) κX) (hAn κX)
    have hwD : TraceWellDefined ι (hullNAPotential D) := hΓ.symm ▸ hwd
    simpa only [hΓ] using realizedHull_trivialPoint_eq_traceMax f (r+1) EX
      hk omegaX omegaV hι hvol a H hd D hD hwD κX κV z

end SGPT.NAPotential.TraceComparison
