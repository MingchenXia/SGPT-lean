import SGPT.Checks.Comparison.TraceGFRealizedSlices
import SGPT.Checks.Comparison.TraceNativeAnalyticZero

/-! ACTUAL above-cutoff vanishing at the SAME native prime image point.
Blueprint: `trace-gf-actual-hull.tex`. -/
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
open FixedGermNormalOrder DemaillyApproximantDivisorialLelong NativeImage NATrace
open scoped Topology Manifold ContDiff ENNReal

variable {X : Scheme.{0}} {L : X.Modules} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsIntegral X] [IsProjective f]
  (EX : ClosedProjectiveEmbedding f)
local instance traceGFRealizedCutoffProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance traceGFRealizedCutoffTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance traceGFRealizedCutoffCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance traceGFRealizedCutoffManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {m : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel (m+1)) V]
  [IsComplexManifold (m+1) V] [ConnectedSpace V]

/-- Above its ACTUAL original trace cutoff, the ACTUALLY manufactured GF
hull has value minus infinity at the SAME actual native prime image. -/
theorem realizedHull_nativeImagePoint_eq_bot_above_traceCutoff
    {ι : V → SchemeComplexPoint f}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel (m+1)) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) {d : ℕ} (hd : 0 < d)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (D : PiecewiseLinearData θ) {φ : BerkovichPoint f → EReal}
    (hD : OriginalHullRealization f n EX a H d D φ)
    (κX : SourceKahlerForm n (SchemeComplexPoint f)) (q : ℚ) (hq : (q : ℝ) < D.τ 0)
    (hcut : traceCutoff ι (hullNAPotential D) κX < (q : ℝ))
    (p : PrimePresentation (m+1) V) {z : p.model} (Φ : DivisorFlattening (m := m) p.divisor z)
    (c : ℝ) (hc : 0 < c) :
    potentialAn n EX (uscRegularization (D.pointwiseUpperConcaveEnvelope (q : ℝ)))
      (nativeImagePoint f n (ι ∘ p.projection) (hι.comp p.modification.1) z Φ c hc) = ⊥ := by
  have hbot := originalHull_restriction_eq_bot_of_traceCutoff_lt D κX q hq hcut
  obtain ⟨N,K,hK,F,hF,heq⟩ := exists_realizedHull_physicalSlice f n EX a H hd D hD q hq.le
  rw [heq] at hbot ⊢
  have htype := normalized_sectionMaximum_nativeRestriction_has_global_actual_ideal_type
    f n EX a H N K hK F.sections (ι ∘ p.projection) (hι.comp p.modification.1)
  have horder := originalNormalOrder_eq_top_of_globalAnalyticType_eq_bot htype
    (fun w => by simpa only [sectionsMaxLog, RationalHull.finiteMaximum, Finset.sup'_apply, Function.comp_apply] using hbot (p.projection w)) Φ
  have hvalue := potentialAn_sectionMaximum_nativeImagePoint_eq f n EX a H N K hK F.sections hF
    (ι ∘ p.projection) (hι.comp p.modification.1) z Φ c hc
  rw [horder] at hvalue
  have hfinite : (K : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top K
  have hpos : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  simpa only [sectionsMaxLog, RationalHull.finiteMaximum, ENat.toENNReal_top,
    ENNReal.mul_top hpos, ENNReal.top_div_of_ne_top hfinite, EReal.coe_ennreal_top, EReal.neg_top] using hvalue

end SGPT.NAPotential.TraceComparison
