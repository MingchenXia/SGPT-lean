import SGPT.Checks.Comparison.TraceNativePrimeFSReader
import SGPT.Checks.Comparison.TraceNativeTrivialFS
import SGPT.Checks.Comparison.TraceNAHullCutoff
import SGPT.Checks.Comparison.GFRationalHullCurve

/-! The ACTUAL original rational GF realization supplies SAME physical slices.
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
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open FixedGermNormalOrder DemaillyApproximantDivisorialLelong NativeImage NATrace
open scoped Topology Manifold ContDiff ENNReal

variable {X : Scheme.{0}} {L : X.Modules} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsIntegral X] [IsProjective f]
  (EX : ClosedProjectiveEmbedding f)
local instance traceGFRealizedProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance traceGFRealizedTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance traceGFRealizedCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance traceGFRealizedManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]

omit [IsIntegral X] [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)] in
/-- The actual original GF realization supplies the SAME physical slice,
actual nonzero section family and positive normalization at every rational cut. -/
theorem exists_realizedHull_physicalSlice
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) {d : ℕ} (hd : 0 < d)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (D : PiecewiseLinearData θ) {φ : BerkovichPoint f → EReal}
    (hD : OriginalHullRealization f n EX a H d D φ) (q : ℚ) (hq : (q : ℝ) ≤ D.τ 0) :
    ∃ N K : ℕ, 0 < K ∧ ∃ F : ActualSectionFamily L N, (∀ j, F.sections j ≠ 0) ∧
      uscRegularization (D.pointwiseUpperConcaveEnvelope (q : ℝ)) =
        fun x => (((K : ℝ)⁻¹ : ℝ) : EReal) *
          finiteMaximum (fun j => H.sectionLogNormSq a N (F.sections j)) x := by
  obtain ⟨N,hN,hfamilies⟩ := hD.2.2.1
  obtain ⟨Q,hQ,F,hF,heq⟩ := hfamilies q hq
  exact ⟨N*Q,d*N*Q,Nat.mul_pos (Nat.mul_pos hd hN) hQ,F,hF,heq⟩

omit [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)] in
/-- The actual original GF physical slice has genuine analytic
singularities; every generator/type witness is manufactured internally. -/
theorem realizedHull_hasManifoldAnalyticSingularityType
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) {d : ℕ} (hd : 0 < d)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (D : PiecewiseLinearData θ) {φ : BerkovichPoint f → EReal}
    (hD : OriginalHullRealization f n EX a H d D φ) (q : ℚ) (hq : (q : ℝ) ≤ D.τ 0) :
    HasManifoldAnalyticSingularityType (n := n)
      (uscRegularization (D.pointwiseUpperConcaveEnvelope (q : ℝ))) := by
  obtain ⟨N,K,hK,F,_hF,heq⟩ := exists_realizedHull_physicalSlice f n EX a H hd D hD q hq
  rw [heq]
  simpa only [sectionsMaxLog, RationalHull.finiteMaximum] using
    normalized_sectionMaximum_hasManifoldAnalyticSingularityType f n EX H a N K hK F.sections

variable {m : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel (m+1)) V]
  [IsComplexManifold (m+1) V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- The ACTUALLY manufactured original GF hull has the SAME original
native trace slice value at its ACTUAL ambient image point. -/
theorem realizedHull_naTraceRes_slice_nativeImagePoint_eq
    (hk : m+1 ≤ n) (omegaX : KahlerBackground n (SchemeComplexPoint f))
    (omegaV : KahlerBackground (m+1) V) {ι : V → SchemeComplexPoint f}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel (m+1)) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hvol : SGPT.Trace.RIsoB.PullbackKahlerVolumePos hι)
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) {d : ℕ} (hd : 0 < d)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (D : PiecewiseLinearData θ) {φ : BerkovichPoint f → EReal}
    (hD : OriginalHullRealization f n EX a H d D φ) (hwd : TraceWellDefined ι (hullNAPotential D))
    (κV : SourceKahlerForm (m+1) V) (q : ℚ)
    (hq : (q : ℝ) < ((TraceRes.naTraceRes hk omegaX omegaV hι hvol
      (hullNAPotential D) hwd).component κV).val.max)
    (p : PrimePresentation (m+1) V) {z : p.model} (hz : z ∈ p.divisor)
    (Φ : DivisorFlattening (m := m) p.divisor z) (c : ℝ) (hc : 0 < c) :
    -((c : EReal) * ((presentationReader
      (((TraceRes.naTraceRes hk omegaX omegaV hι hvol
        (hullNAPotential D) hwd).component κV).val.potential ⟨q,hq⟩) p : ℝ≥0∞) : EReal)) =
      potentialAn n EX (uscRegularization (D.pointwiseUpperConcaveEnvelope (q : ℝ)))
        (nativeImagePoint f n (ι ∘ p.projection) (hι.comp p.modification.1) z Φ c hc) := by
  have htrace := sliceTraceable_of_lt_traceCutoff hwd (sourceKahlerFormOfBackground omegaX) hq
  have htype := realizedHull_hasManifoldAnalyticSingularityType f n EX a H hd D hD q htrace.1.le
  have hI := originalHull_naTraceRes_slice_iEquivalent_restriction hk omegaX omegaV hι hvol D hwd κV q hq htype
  have hread := le_antisymm
    ((SGPT.PSH.CompactPrimeNumerical.sourceIOrder_iff_presentationComparison hI.2.1 hI.2.2.1).mp hI.2 p)
    ((SGPT.PSH.CompactPrimeNumerical.sourceIOrder_iff_presentationComparison hI.1.1 hI.1.2.1).mp hI.1 p)
  rw [hread]
  have hne := originalHull_restriction_nontrivial_of_traceable hk omegaX omegaV hι D q htrace htype
  obtain ⟨N,K,hK,F,hF,heq⟩ := exists_realizedHull_physicalSlice f n EX a H hd D hD q htrace.1.le
  rw [heq] at hne ⊢
  simpa only [sectionsMaxLog, RationalHull.finiteMaximum] using
    (potentialAn_sectionMaximum_nativePrime_eq f n EX a H N K hK F.sections hF ι hι
      (by simpa only [sectionsMaxLog, RationalHull.finiteMaximum] using hne) p hz Φ c hc).symm

end SGPT.NAPotential.TraceComparison
