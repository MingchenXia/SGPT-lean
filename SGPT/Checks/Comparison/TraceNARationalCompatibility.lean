import SGPT.Checks.Comparison.TraceNARationalSup

/-! Actual original rational hull NA trace compatibility, with the unchanged
actual cutoff, operator, section data and all original valuation points.
Blueprint: `trace-rational-hull-slices.tex`. This module states its scheme-target
scope explicitly; arbitrary analytic resolution algebraization is not assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison

open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Envelope
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.PiecewiseLinearData
open SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision
open SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision.WholeHull
open SGPT.NAPotential.BJ.GfIm SGPT.NAPotential.BJ.GfIm.RationalHull
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.NATrace
open scoped Topology Manifold ContDiff

section Source
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (EX : ClosedProjectiveEmbedding f) [IsProper f]
local instance traceCompatTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance traceCompatCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance traceCompatManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}

/-- The original hull's ACTUAL NA analytification is the rational supremum
of the SAME original unprojected regularized hull slices. -/
theorem hull_naPotentialAnAt_eq_rational_originalHullSup (D : PiecewiseLinearData θ)
    (κ : SourceKahlerForm n (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    naPotentialAnAt n EX (hullNAPotential D) κ v =
      ⨆ q : ℚ, ⨆ (_ : (q : ℝ) < D.τ 0),
        potentialAn n EX (uscRegularization (D.pointwiseUpperConcaveEnvelope (q : ℝ))) v +
          ((q : ℝ) : EReal) := by
  rw [naPotentialAnAt_eq_rational_parameterSup]
  apply iSup_congr
  intro q
  apply iSup_congr
  intro hq
  exact congrArg (fun a : EReal => a + ((q : ℝ) : EReal))
    (congrFun (potentialAn_eq_of_sourceIEquivalent n EX
      (originalHull_iEquivalent_component D κ q hq)) v).symm

end Source

section Compatibility
variable {X Y : Scheme.{0}} {L : X.Modules} (f : X ⟶ Spec (.of ℂ)) (i : Y ⟶ X) (n k : ℕ)
  [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension k (i ≫ f)]
  [IsIntegral X] [IsIntegral Y] [IsProjective f] [IsProjective (i ≫ f)]
  (EX : ClosedProjectiveEmbedding f) (EY : ClosedProjectiveEmbedding (i ≫ f))
local instance traceCompatXProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance traceCompatYProper : IsProper (i ≫ f) := (ProjectiveFactorizationRingIso.of_isProjective (i ≫ f)).isProper
local instance traceCompatXTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance traceCompatYTopology : TopologicalSpace (SchemeComplexPoint (i ≫ f)) := schemeAnalyticPointTopology (i ≫ f)
local instance traceCompatXCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance traceCompatYCharts : ChartedSpace (ComplexModel k) (SchemeComplexPoint (i ≫ f)) := schemeAnalyticTNChartedSpace (i ≫ f) k
local instance traceCompatXManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
local instance traceCompatYManifold : IsComplexManifold k (SchemeComplexPoint (i ≫ f)) := schemeAnalyticTN_isComplexManifold (i ≫ f) k
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  [MeasurableSpace (SchemeComplexPoint (i ≫ f))] [BorelSpace (SchemeComplexPoint (i ≫ f))]
  [CompactSpace (SchemeComplexPoint (i ≫ f))] [ConnectedSpace (SchemeComplexPoint (i ≫ f))]

/-- **The actual NA trace of the ORIGINAL rational finite-section hull
analytifies compatibly at EVERY target valuation.** Both actual cutoffs, all
common products, above-cutoff zero-family terms, endpoint removal and rational
cofinality are produced internally. The actual primitive scope includes n=0. -/
theorem originalRationalHull_naTraceRes_naPotentialAnAt_eq
    (hk : k ≤ n) (omegaX : KahlerBackground n (SchemeComplexPoint f))
    (omegaY : KahlerBackground k (SchemeComplexPoint (i ≫ f)))
    (hvol : SGPT.Trace.RIsoB.PullbackKahlerVolumePos (schemeComplexPointMap_contMDiff f i k n ∞))
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) (N K : ℕ) (hK : 0 < K)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (D : PiecewiseLinearData θ) (hτ : ∀ j, ∃ r : ℚ, D.τ j = r)
    (I : Fin (D.N + 1) → Type) [∀ j, Fintype (I j)] [∀ j, Nonempty (I j)]
    (t : (j : Fin (D.N + 1)) → I j → bundlePowerGlobalSections L N)
    (ht : ∀ j b, t j b ≠ 0)
    (hA : ∀ j, D.A j = fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) *
      finiteMaximum (fun b => H.sectionLogNormSq a N (t j b)) p)
    (hwd : TraceWellDefined (schemeComplexPointMap (i ≫ f) f i rfl) (hullNAPotential D))
    (κX : SourceKahlerForm n (SchemeComplexPoint f))
    (κY : SourceKahlerForm k (SchemeComplexPoint (i ≫ f))) (w : BerkovichPoint (i ≫ f)) :
    naPotentialAnAt k EY
      (TraceRes.naTraceRes hk omegaX omegaY (schemeComplexPointMap_contMDiff f i k n ∞)
        hvol (hullNAPotential D) hwd) κY w =
      naPotentialAnAt n EX (hullNAPotential D) κX (schemeAnMap i rfl w) := by
  let Δ := TraceRes.naTraceRes hk omegaX omegaY (schemeComplexPointMap_contMDiff f i k n ∞)
    hvol (hullNAPotential D) hwd
  let T := (Δ.component κY).val.max
  have hT : T = traceCutoff (schemeComplexPointMap (i ≫ f) f i rfl) (hullNAPotential D) κX :=
    TraceRes.naTraceRes_max hk omegaX omegaY (schemeComplexPointMap_contMDiff f i k n ∞)
      hvol (hullNAPotential D) hwd κY κX
  have hTS : T ≤ D.τ 0 := hT ▸ traceCutoff_le_max hwd κX
  let F : ℝ → EReal := fun s => potentialAn n EX
    (uscRegularization (D.pointwiseUpperConcaveEnvelope s)) (schemeAnMap i rfl w)
  have hpsh (s : ℝ) (hs : s ≤ D.τ 0) : IsThetaPshPotential (atlasClosedFormToNative θ).val
      (uscRegularization (D.pointwiseUpperConcaveEnvelope s)) := by
    rw [uscRegularization_pointwiseUpperConcaveEnvelope_eq_simplexValue]
    exact (isThetaPSH_iff_nativeThetaPotential θ _).mp (isThetaPSH_simplexValue D s hs)
  have hanti : ∀ {s t : ℝ}, s ≤ t → t < D.τ 0 → F t ≤ F s := by
    intro s r hsr hr
    apply BerkovichPoint.potentialAn_mono_of_multiplierIdealAlgebraic n EX
      (SGPT.GAGA.H0S.multiplierIdealAlgebraic f EX n) (hpsh r hr.le) (hpsh s (hsr.trans hr.le))
    intro p
    simp only [uscRegularization_pointwiseUpperConcaveEnvelope_eq_simplexValue]
    exact simplexValue_antitone D p hsr
  have hbot : ∀ q : ℚ, T < (q : ℝ) → (q : ℝ) < D.τ 0 → F q = ⊥ := by
    intro q hqT hq
    exact originalRationalHull_schemeAnMap_eq_bot_above_traceCutoff f i n k EX EY
      a H N K hK D hτ I t ht hA κX q hq (hT ▸ hqT) w
  change naPotentialAnAt k EY Δ κY w = _
  rw [naPotentialAnAt_eq_rational_parameterSup, hull_naPotentialAnAt_eq_rational_originalHullSup]
  change (⨆ q : ℚ, ⨆ (hq : (q : ℝ) < T),
    potentialAn k EY ((Δ.component κY).val.potential ⟨q, hq⟩) w + ((q : ℝ) : EReal)) =
    ⨆ q : ℚ, ⨆ (_ : (q : ℝ) < D.τ 0), F q + ((q : ℝ) : EReal)
  rw [rational_parameterSup_eq_below_of_bot_above F (D.τ 0) T hTS hanti hbot]
  refine iSup_congr fun q => iSup_congr fun hq => ?_
  exact congrArg (fun a : EReal => a + ((q : ℝ) : EReal))
    (originalRationalHull_naTraceRes_slice_potentialAn_eq f i n k EX EY hk omegaX omegaY
      hvol a H N K hK D hτ I t ht hA hwd κY q hq w)

end Compatibility
end SGPT.NAPotential.TraceComparison
