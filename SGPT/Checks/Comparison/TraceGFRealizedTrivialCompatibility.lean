import SGPT.Checks.Comparison.TraceGFRealizedTrivialSlices
import SGPT.Checks.Comparison.TraceNARationalCompatibility

/-! SAME original rational slices at the ACTUAL native trivial image.
Blueprint: `trace-gf-actual-hull.tex`. All native target dimensions. -/
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
open FixedGermNormalOrder DemaillyApproximantDivisorialLelong NativeTrivial NATrace
open scoped Topology Manifold ContDiff ENNReal

variable {X : Scheme.{0}} {L : X.Modules} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsIntegral X] [IsProjective f]
  (EX : ClosedProjectiveEmbedding f)
local instance traceGFRealizedTrivialCompatProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance traceGFRealizedTrivialCompatTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance traceGFRealizedTrivialCompatCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance traceGFRealizedTrivialCompatManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {k : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- The ORIGINAL rational hull at its ACTUAL native trivial image has
value the ACTUAL maximum of its unchanged NA trace, in EVERY native target
dimension, including zero. All literal restrictions and cutoffs are internal. -/
theorem realizedHull_trivialPoint_eq_traceMax
    (hk : k ≤ n) (omegaX : KahlerBackground n (SchemeComplexPoint f))
    (omegaV : KahlerBackground k V) {ι : V → SchemeComplexPoint f}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hvol : SGPT.Trace.RIsoB.PullbackKahlerVolumePos hι)
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) {d : ℕ} (hd : 0 < d)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (D : PiecewiseLinearData θ) {φ : BerkovichPoint f → EReal}
    (hD : OriginalHullRealization f n EX a H d D φ)
    (hwd : TraceWellDefined ι (hullNAPotential D))
    (κX : SourceKahlerForm n (SchemeComplexPoint f)) (κV : SourceKahlerForm k V) (z : V) :
    naPotentialAnAt n EX (hullNAPotential D) κX (point f n ι hι z) =
      ((((TraceRes.naTraceRes hk omegaX omegaV hι hvol
        (hullNAPotential D) hwd).component κV).val.max : ℝ) : EReal) := by
  let Δ := TraceRes.naTraceRes hk omegaX omegaV hι hvol (hullNAPotential D) hwd
  let T := (Δ.component κV).val.max
  have hT : T = traceCutoff ι (hullNAPotential D) κX :=
    TraceRes.naTraceRes_max hk omegaX omegaV hι hvol (hullNAPotential D) hwd κV κX
  have hTS : T ≤ D.τ 0 := hT ▸ traceCutoff_le_max hwd κX
  let F : ℝ → EReal := fun s => potentialAn n EX
    (uscRegularization (D.pointwiseUpperConcaveEnvelope s)) (point f n ι hι z)
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
    exact realizedHull_trivialPoint_slice_eq_bot_above_traceCutoff f n EX hι
      a H hd D hD κX q hq (hT ▸ hqT) z
  have hzero (q : ℚ) (hq : (q : ℝ) < T) : F q = 0 :=
    realizedHull_trivialPoint_slice_eq_zero_of_lt_traceCutoff f n EX hk omegaX omegaV hι
      a H hd D hD hwd κX q (hT ▸ hq) z
  rw [hull_naPotentialAnAt_eq_rational_originalHullSup]
  change (⨆ q : ℚ, ⨆ (_ : (q : ℝ) < D.τ 0), F q + ((q : ℝ) : EReal)) = (T : EReal)
  rw [rational_parameterSup_eq_below_of_bot_above F (D.τ 0) T hTS hanti hbot]
  have hrewrite : (⨆ q : ℚ, ⨆ (hq : (q : ℝ) < T), F q + ((q : ℝ) : EReal)) =
      ⨆ q : ℚ, ⨆ (_ : (q : ℝ) < T), ((q : ℝ) : EReal) := by
    refine iSup_congr fun q => iSup_congr fun hq => ?_
    rw [hzero q hq, zero_add]
  rw [hrewrite]
  apply le_antisymm
  · exact iSup_le fun q => iSup_le fun hq => EReal.coe_le_coe_iff.mpr hq.le
  · simpa only [zero_add] using add_real_le_rational_iSup (0 : EReal) T

end SGPT.NAPotential.TraceComparison
