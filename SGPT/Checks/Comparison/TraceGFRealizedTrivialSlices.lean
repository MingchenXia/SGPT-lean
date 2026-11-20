import SGPT.Checks.Comparison.TraceGFRealizedSlices

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
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open FixedGermNormalOrder DemaillyApproximantDivisorialLelong NativeTrivial NATrace
open scoped Topology Manifold ContDiff ENNReal

variable {X : Scheme.{0}} {L : X.Modules} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsIntegral X] [IsProjective f]
  (EX : ClosedProjectiveEmbedding f)
local instance traceGFRealizedTrivialProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance traceGFRealizedTrivialTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance traceGFRealizedTrivialCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance traceGFRealizedTrivialManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {k : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- Below its ACTUAL trace cutoff, the SAME ACTUALLY manufactured GF
hull slice has value zero at the SAME actual native trivial image. -/
theorem realizedHull_trivialPoint_slice_eq_zero_of_lt_traceCutoff
    (hk : k ≤ n) (omegaX : KahlerBackground n (SchemeComplexPoint f))
    (omegaV : KahlerBackground k V) {ι : V → SchemeComplexPoint f}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) {d : ℕ} (hd : 0 < d)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (D : PiecewiseLinearData θ) {φ : BerkovichPoint f → EReal}
    (hD : OriginalHullRealization f n EX a H d D φ)
    (hwd : TraceWellDefined ι (hullNAPotential D))
    (κX : SourceKahlerForm n (SchemeComplexPoint f)) (q : ℚ)
    (hq : (q : ℝ) < traceCutoff ι (hullNAPotential D) κX) (z : V) :
    potentialAn n EX (uscRegularization (D.pointwiseUpperConcaveEnvelope (q : ℝ)))
      (NativeTrivial.point f n ι hι z) = 0 := by
  have htrace := sliceTraceable_of_lt_traceCutoff hwd κX hq
  have htype := realizedHull_hasManifoldAnalyticSingularityType f n EX a H hd D hD q htrace.1.le
  have htrace' : SliceTraceable ι (hullNAPotential D) (sourceKahlerFormOfBackground omegaX) q :=
    sliceTraceable_index ι (hullNAPotential D) htrace
  have hne := originalHull_restriction_nontrivial_of_traceable hk omegaX omegaV hι D q htrace' htype
  obtain ⟨N,K,hK,F,hF,heq⟩ := exists_realizedHull_physicalSlice f n EX a H hd D hD q htrace.1.le
  rw [heq] at hne ⊢
  simpa only [sectionsMaxLog, RationalHull.finiteMaximum] using
    NativeTrivial.potentialAn_sectionMaximum_trivialPoint_eq_zero f n EX a H N K hK F.sections hF ι hι
      (by simpa only [sectionsMaxLog, RationalHull.finiteMaximum] using hne) z

omit [MeasurableSpace V] [BorelSpace V] [CompactSpace V] in
/-- Above its ACTUAL trace cutoff, the SAME ACTUALLY manufactured GF
hull slice is minus infinity at the SAME actual native trivial image. -/
theorem realizedHull_trivialPoint_slice_eq_bot_above_traceCutoff
    {ι : V → SchemeComplexPoint f}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) {d : ℕ} (hd : 0 < d)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (D : PiecewiseLinearData θ) {φ : BerkovichPoint f → EReal}
    (hD : OriginalHullRealization f n EX a H d D φ)
    (κX : SourceKahlerForm n (SchemeComplexPoint f)) (q : ℚ) (hq : (q : ℝ) < D.τ 0)
    (hcut : traceCutoff ι (hullNAPotential D) κX < (q : ℝ)) (z : V) :
    potentialAn n EX (uscRegularization (D.pointwiseUpperConcaveEnvelope (q : ℝ)))
      (NativeTrivial.point f n ι hι z) = ⊥ := by
  have hbot := originalHull_restriction_eq_bot_of_traceCutoff_lt D κX q hq hcut
  obtain ⟨N,K,hK,F,hF,heq⟩ := exists_realizedHull_physicalSlice f n EX a H hd D hD q hq.le
  rw [heq] at hbot ⊢
  simpa only [sectionsMaxLog, RationalHull.finiteMaximum] using
    NativeTrivial.potentialAn_sectionMaximum_trivialPoint_eq_bot f n EX a H N K hK F.sections hF ι hι
      (by simpa only [sectionsMaxLog, RationalHull.finiteMaximum] using hbot) z

end SGPT.NAPotential.TraceComparison
