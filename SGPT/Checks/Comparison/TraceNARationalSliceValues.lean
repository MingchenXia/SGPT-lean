import SGPT.Checks.Comparison.TraceNARationalSlices

/-! The ORIGINAL rational section hull and the ACTUAL NA trace, at every
original semi-valuation of the same prescribed target.
Blueprint: `trace-rational-hull-slices.tex`, actual-slice node. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison

open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Envelope
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.PiecewiseLinearData
open SGPT.NAPotential.BJ.GfIm SGPT.NAPotential.BJ.GfIm.RationalHull
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.NATrace
open scoped Topology Manifold ContDiff

variable {X Y : Scheme.{0}} {L : X.Modules} (f : X ⟶ Spec (.of ℂ)) (i : Y ⟶ X) (n k : ℕ)
  [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension k (i ≫ f)]
  [IsIntegral X] [IsIntegral Y] [IsProjective f] [IsProjective (i ≫ f)]
  (EX : ClosedProjectiveEmbedding f) (EY : ClosedProjectiveEmbedding (i ≫ f))
local instance traceSliceXProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance traceSliceYProper : IsProper (i ≫ f) := (ProjectiveFactorizationRingIso.of_isProjective (i ≫ f)).isProper
local instance traceSliceXTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance traceSliceYTopology : TopologicalSpace (SchemeComplexPoint (i ≫ f)) := schemeAnalyticPointTopology (i ≫ f)
local instance traceSliceXCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance traceSliceYCharts : ChartedSpace (ComplexModel k) (SchemeComplexPoint (i ≫ f)) := schemeAnalyticTNChartedSpace (i ≫ f) k
local instance traceSliceXManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
local instance traceSliceYManifold : IsComplexManifold k (SchemeComplexPoint (i ≫ f)) := schemeAnalyticTN_isComplexManifold (i ≫ f) k

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  [MeasurableSpace (SchemeComplexPoint (i ≫ f))] [BorelSpace (SchemeComplexPoint (i ≫ f))]
  [CompactSpace (SchemeComplexPoint (i ≫ f))] [ConnectedSpace (SchemeComplexPoint (i ≫ f))]

/-- The actual original rational finite-section hull, analytified after the
ACTUAL NA trace, equals the SAME original hull at the actual image valuation.
All analytic type, trace-class, nontriviality and common products are produced
internally from the original finite section data. All valuations/dimensions. -/
theorem originalRationalHull_naTraceRes_slice_potentialAn_eq
    (hk : k ≤ n) (omegaX : KahlerBackground n (SchemeComplexPoint f))
    (omegaY : KahlerBackground k (SchemeComplexPoint (i ≫ f)))
    (hvol : SGPT.Trace.RIsoB.PullbackKahlerVolumePos
      (schemeComplexPointMap_contMDiff f i k n ∞))
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) (N K : ℕ) (hK : 0 < K)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (D : PiecewiseLinearData θ) (hτ : ∀ j, ∃ r : ℚ, D.τ j = r)
    (I : Fin (D.N + 1) → Type) [∀ j, Fintype (I j)] [∀ j, Nonempty (I j)]
    (t : (j : Fin (D.N + 1)) → I j → bundlePowerGlobalSections L N)
    (ht : ∀ j b, t j b ≠ 0)
    (hA : ∀ j, D.A j = fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) *
      finiteMaximum (fun b => H.sectionLogNormSq a N (t j b)) p)
    (hwd : TraceWellDefined (schemeComplexPointMap (i ≫ f) f i rfl) (hullNAPotential D))
    (κY : SourceKahlerForm k (SchemeComplexPoint (i ≫ f))) (q : ℚ)
    (hq : (q : ℝ) < ((TraceRes.naTraceRes hk omegaX omegaY
      (schemeComplexPointMap_contMDiff f i k n ∞) hvol (hullNAPotential D) hwd).component κY).val.max)
    (w : BerkovichPoint (i ≫ f)) :
    potentialAn k EY
      (((TraceRes.naTraceRes hk omegaX omegaY
        (schemeComplexPointMap_contMDiff f i k n ∞) hvol (hullNAPotential D) hwd).component κY).val.potential ⟨q, hq⟩) w =
      potentialAn n EX (uscRegularization (D.pointwiseUpperConcaveEnvelope (q : ℝ)))
        (schemeAnMap i rfl w) := by
  have htrace := sliceTraceable_of_lt_traceCutoff hwd (sourceKahlerFormOfBackground omegaX) hq
  have hq0 : (q : ℝ) ≤ D.τ 0 := htrace.1.le
  have htype := originalHull_hasManifoldAnalyticSingularityType f n EX H a N K hK D hτ I t ht hA q hq0
  have hI := originalHull_naTraceRes_slice_iEquivalent_restriction hk omegaX omegaY
    (schemeComplexPointMap_contMDiff f i k n ∞) hvol D hwd κY q hq htype
  have hne := originalHull_restriction_nontrivial_of_traceable hk omegaX omegaY
    (schemeComplexPointMap_contMDiff f i k n ∞) D q htrace htype
  rw [congrFun (potentialAn_eq_of_sourceIEquivalent k EY hI) w]
  obtain ⟨Q, hQ, F, hF, heq, _hval⟩ :=
    exists_originalHull_commonSectionFamily n EX H a N K hK D hτ I t ht hA q hq0
  rw [heq] at hne ⊢
  simpa only [sectionsMaxLog, RationalHull.finiteMaximum] using
    potentialAn_sectionMaximum_restriction_eq_of_nontrivial f i n k EX EY a H
      (N * Q) (K * Q) (Nat.mul_pos hK hQ) F.sections hF
      (by simpa only [sectionsMaxLog, RationalHull.finiteMaximum] using hne) w

end SGPT.NAPotential.TraceComparison
