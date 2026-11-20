import SGPT.Checks.Comparison.TraceGFRealizedCutoff
import SGPT.Checks.Comparison.TraceNativeLegendreRational
import SGPT.Checks.Comparison.TraceNARationalCompatibility

/-! ORIGINAL rational hull and ACTUAL native NA trace Legendre compatibility.
Blueprint: `trace-gf-actual-hull.tex`. No native target algebraization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison

open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Envelope
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.PiecewiseLinearData
open SGPT.NAPotential.BJ.GfIm SGPT.NAPotential.BJ.GfIm.RationalHull
open SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision
open SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision.WholeHull
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open FixedGermNormalOrder DemaillyApproximantDivisorialLelong NativeImage NATrace
open scoped Topology Manifold ContDiff ENNReal

variable {X : Scheme.{0}} {L : X.Modules} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsIntegral X] [IsProjective f]
  (EX : ClosedProjectiveEmbedding f)
local instance traceGFRealizedCompatProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance traceGFRealizedCompatTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance traceGFRealizedCompatCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance traceGFRealizedCompatManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {m : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel (m+1)) V]
  [IsComplexManifold (m+1) V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- The EXISTING original NA trace of the SAME original rational hull has
its unchanged native divisorial transform equal to the ambient hull's actual
analytification at the SAME produced native image point. All cutoffs, zero
families and both rational/real cofinalities are internal. -/
theorem realizedHull_naTraceRes_nativeDivisorial_eq
    (hk : m+1 ≤ n) (omegaX : KahlerBackground n (SchemeComplexPoint f))
    (omegaV : KahlerBackground (m+1) V) {ι : V → SchemeComplexPoint f}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel (m+1)) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hvol : SGPT.Trace.RIsoB.PullbackKahlerVolumePos hι)
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) {d : ℕ} (hd : 0 < d)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (D : PiecewiseLinearData θ) {φ : BerkovichPoint f → EReal}
    (hD : OriginalHullRealization f n EX a H d D φ)
    (hwd : TraceWellDefined ι (hullNAPotential D))
    (κX : SourceKahlerForm n (SchemeComplexPoint f)) (κV : SourceKahlerForm (m+1) V)
    (p : PrimePresentation (m+1) V) {z : p.model} (hz : z ∈ p.divisor)
    (Φ : DivisorFlattening (m := m) p.divisor z) (c : ℝ) (hc : 0 < c) :
    BJPrep.naDivisorialTransform
      (TraceRes.naTraceRes hk omegaX omegaV hι hvol (hullNAPotential D) hwd) κV p c =
      naPotentialAnAt n EX (hullNAPotential D) κX
        (nativeImagePoint f n (ι ∘ p.projection) (hι.comp p.modification.1) z Φ c hc) := by
  let Δ := TraceRes.naTraceRes hk omegaX omegaV hι hvol (hullNAPotential D) hwd
  let T := (Δ.component κV).val.max
  have hT : T = traceCutoff ι (hullNAPotential D) κX :=
    TraceRes.naTraceRes_max hk omegaX omegaV hι hvol (hullNAPotential D) hwd κV κX
  have hTS : T ≤ D.τ 0 := hT ▸ traceCutoff_le_max hwd κX
  let F : ℝ → EReal := fun s => potentialAn n EX
    (uscRegularization (D.pointwiseUpperConcaveEnvelope s))
      (nativeImagePoint f n (ι ∘ p.projection) (hι.comp p.modification.1) z Φ c hc)
  have hpsh (s : ℝ) (hs : s ≤ D.τ 0) : IsThetaPshPotential (atlasClosedFormToNative θ).val
      (uscRegularization (D.pointwiseUpperConcaveEnvelope s)) := by
    rw [uscRegularization_pointwiseUpperConcaveEnvelope_eq_simplexValue]
    exact (isThetaPSH_iff_nativeThetaPotential θ _).mp (isThetaPSH_simplexValue D s hs)
  have hanti : ∀ {s t : ℝ}, s ≤ t → t < D.τ 0 → F t ≤ F s := by
    intro s r hsr hr
    apply BerkovichPoint.potentialAn_mono_of_multiplierIdealAlgebraic n EX
      (SGPT.GAGA.H0S.multiplierIdealAlgebraic f EX n) (hpsh r hr.le) (hpsh s (hsr.trans hr.le))
    intro x
    simp only [uscRegularization_pointwiseUpperConcaveEnvelope_eq_simplexValue]
    exact simplexValue_antitone D x hsr
  have hbot : ∀ q : ℚ, T < (q : ℝ) → (q : ℝ) < D.τ 0 → F q = ⊥ := by
    intro q hqT hq
    exact realizedHull_nativeImagePoint_eq_bot_above_traceCutoff f n EX hι
      a H hd D hD κX q hq (hT ▸ hqT) p Φ c hc
  change BJPrep.naDivisorialTransform Δ κV p c = _
  rw [naDivisorialTransform_eq_rational_parameterSup Δ κV p c hc.le,
    hull_naPotentialAnAt_eq_rational_originalHullSup]
  change (⨆ q : ℚ, ⨆ (hq : (q : ℝ) < T),
    -((c : EReal) * ((presentationReader ((Δ.component κV).val.potential ⟨q, hq⟩) p : ℝ≥0∞) : EReal)) +
      ((q : ℝ) : EReal)) =
    ⨆ q : ℚ, ⨆ (_ : (q : ℝ) < D.τ 0), F q + ((q : ℝ) : EReal)
  rw [rational_parameterSup_eq_below_of_bot_above F (D.τ 0) T hTS hanti hbot]
  refine iSup_congr fun q => iSup_congr fun hq => ?_
  exact congrArg (fun a : EReal => a + ((q : ℝ) : EReal))
    (realizedHull_naTraceRes_slice_nativeImagePoint_eq f n EX hk omegaX omegaV hι hvol
      a H hd D hD hwd κV q hq p hz Φ c hc)

end SGPT.NAPotential.TraceComparison
