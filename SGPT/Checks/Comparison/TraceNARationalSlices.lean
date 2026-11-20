import SGPT.Checks.Comparison.TraceGFNontrivialRestriction
import SGPT.NAPotential.TraceResNATrace

/-! Actual original rational hull slices and the unchanged original NA trace.
Blueprint: `trace-rational-hull-slices.tex`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison

open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.PiecewiseLinearData
open SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision
open SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision.WholeHull
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SourceTraceRepresentativeDefinition
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.NATrace
open scoped Topology Manifold ContDiff

section ActualSlices
universe u
variable {n k : ℕ} {M V : Type u}
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The SAME original regularized hull slice and its ACTUAL NA component
have identical multiplier ideals. The envelope square is produced internally. -/
theorem originalHull_iEquivalent_component (D : PiecewiseLinearData θ)
    (κ : SourceKahlerForm n M) (s : ℝ)
    (hs : s < ((hullNAPotential D).component κ).val.max) :
    sourceIEquivalent (ofFixedModel n M)
      (uscRegularization (D.pointwiseUpperConcaveEnvelope s))
      (((hullNAPotential D).component κ).val.potential ⟨s, hs⟩) := by
  rw [hullNAPotential_component_potential]
  simp only [uscRegularization_pointwiseUpperConcaveEnvelope_eq_simplexValue]
  exact sourceIEquivalent_iEnvelope (simplexValue_componentPSH D κ hs.le)

omit [MeasurableSpace V] [BorelSpace V] [CompactSpace V] in
/-- The true below-cutoff generic Lelong condition transfers to the original
regularized hull, using the actual whole multiplier-ideal equivalence. -/
theorem originalHull_genericLelong_eq_zero (D : PiecewiseLinearData θ)
    {ι : V → M} (κ : SourceKahlerForm n M) (s : ℝ)
    (hs : SliceTraceable ι (hullNAPotential D) κ s) :
    sourceGenericLelongNumber (n := n) ι
      (uscRegularization (D.pointwiseUpperConcaveEnvelope s)) = 0 := by
  have hI := originalHull_iEquivalent_component D κ s hs.1
  exact SGPT.Trace.sourceGenericLelongNumber_eq_zero_of_iOrder
    (((hullNAPotential D).component κ).val.native_thetaPSH ⟨s, hs.1⟩)
    ((sourceIOrder_iff_native hI.2.1 hI.2.2.1).mp hI.2) hs.2

/-- The ACTUAL trace of the hull's component is intrinsically equivalent to
the literal restriction of the SAME analytic original hull slice. -/
theorem originalHull_traceSlice_pEquivalent_restriction
    (hk : k ≤ n) (omegaX : KahlerBackground n M) (omegaV : KahlerBackground k V)
    {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (D : PiecewiseLinearData θ) (s : ℝ)
    (hs : SliceTraceable ι (hullNAPotential D) (sourceKahlerFormOfBackground omegaX) s)
    (hA : HasManifoldAnalyticSingularityType (n := n)
      (uscRegularization (D.pointwiseUpperConcaveEnvelope s))) :
    SingularGlobalPOrder.SourcePEquivalent (n := k)
      (traceSlice hk omegaX omegaV hι (hullNAPotential D) s hs)
      (fun y => uscRegularization (D.pointwiseUpperConcaveEnvelope s) (ι y)) := by
  let κ := sourceKahlerFormOfBackground omegaX
  have hI := originalHull_iEquivalent_component D κ s hs.1
  have hu := (isThetaPSH_iff_nativeThetaPotential _ _).mp
    (simplexValue_componentPSH D κ hs.1.le)
  have hu' : IsGlobalQuasiPshPotential (n := n)
      (uscRegularization (D.pointwiseUpperConcaveEnvelope s)) := by
    simpa only [uscRegularization_pointwiseUpperConcaveEnvelope_eq_simplexValue]
      using hu.quasiPshPotential
  obtain ⟨uT, hT⟩ := SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential
    hk omegaX omegaV hu' hι (originalHull_genericLelong_eq_zero D κ s hs)
  have hspec := traceSlice_spec hk omegaX omegaV hι (hullNAPotential D) s hs
  have hforward := SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives
    hk omegaV omegaV hι hspec hT
      ((sourceIOrder_iff_native hI.2.1 hI.2.2.1).mp hI.2)
  have hback := SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives
    hk omegaV omegaV hι hT hspec
      ((sourceIOrder_iff_native hI.1.1 hI.1.2.1).mp hI.1)
  have hrestrict := SGPT.Trace.sourcePEquivalent_trace_restriction_of_analytic hk omegaV hι hT hA
  exact ⟨SingularGlobalPOrder.SourcePOrder.trans omegaV hforward hrestrict.1,
    SingularGlobalPOrder.SourcePOrder.trans omegaV hrestrict.2 hback⟩

/-- The actual NA trace component retains the true multiplier class of its
actual trace representative under only the original positive-volume hypothesis. -/
theorem actual_traceComponent_iEquivalent_traceSlice
    (hk : k ≤ n) (omegaX : KahlerBackground n M) (omegaV : KahlerBackground k V)
    {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hvol : SGPT.Trace.RIsoB.PullbackKahlerVolumePos (M := M) hι)
    (Γ : SourceNAPotential θ) (κV : SourceKahlerForm k V) (s : ℝ)
    (hs : SliceTraceable ι Γ (sourceKahlerFormOfBackground omegaX) s) :
    sourceIEquivalent (ofFixedModel k V)
      (traceComponentSlice hk omegaX omegaV hι Γ κV s hs)
      (traceSlice hk omegaX omegaV hι Γ s hs) := by
  obtain ⟨φ, hφ, hE⟩ := TraceRes.exists_goodTraceSlice' hk omegaX omegaV hι hvol Γ κV s hs
  rw [traceComponentSlice_eq hk omegaX omegaV hι Γ κV s hs hE]
  exact sourceIEquivalent_trans
    (sourceIEquivalent_symm (sourceIEquivalent_iEnvelope (thetaPSH_traceBackground_of_half hι κV hφ))) hE

/-- The true analytic hull slice and the ACTUAL trace-component slice have
identical multiplier ideals, with all trace/envelope representatives internal. -/
theorem originalHull_traceComponent_iEquivalent_restriction
    (hk : k ≤ n) (omegaX : KahlerBackground n M) (omegaV : KahlerBackground k V)
    {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hvol : SGPT.Trace.RIsoB.PullbackKahlerVolumePos (M := M) hι)
    (D : PiecewiseLinearData θ) (κV : SourceKahlerForm k V) (s : ℝ)
    (hs : SliceTraceable ι (hullNAPotential D) (sourceKahlerFormOfBackground omegaX) s)
    (hA : HasManifoldAnalyticSingularityType (n := n)
      (uscRegularization (D.pointwiseUpperConcaveEnvelope s))) :
    sourceIEquivalent (ofFixedModel k V)
      (traceComponentSlice hk omegaX omegaV hι (hullNAPotential D) κV s hs)
      (fun y => uscRegularization (D.pointwiseUpperConcaveEnvelope s) (ι y)) := by
  have hP := originalHull_traceSlice_pEquivalent_restriction hk omegaX omegaV hι D s hs hA
  have hqT := isQPSH_of_sourceTrace hι (traceSlice_spec hk omegaX omegaV hι (hullNAPotential D) s hs)
  have hqR : (ofFixedModel k V).IsQPSH
      (fun y => uscRegularization (D.pointwiseUpperConcaveEnvelope s) (ι y)) := by
    obtain ⟨β, _hβT, hβR, _⟩ := hP.1
    refine ⟨nativeClosedFormToAtlas β, (isThetaPSH_iff_nativeThetaPotential _ _).mpr ?_⟩
    rwa [sourceNativeAtlasForm_roundTrip]
  exact sourceIEquivalent_trans
    (actual_traceComponent_iEquivalent_traceSlice hk omegaX omegaV hι hvol (hullNAPotential D) κV s hs)
    ⟨sourceIOrder_of_sourcePOrder hqT hqR hP.1,
      sourceIOrder_of_sourcePOrder hqR hqT hP.2⟩

/-- The ORIGINAL restricted analytic hull is literally nontrivial below the
actual trace cutoff. This is derived from the actual trace, not supplied. -/
theorem originalHull_restriction_nontrivial_of_traceable
    (hk : k ≤ n) (omegaX : KahlerBackground n M) (omegaV : KahlerBackground k V)
    {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (D : PiecewiseLinearData θ) (s : ℝ)
    (hs : SliceTraceable ι (hullNAPotential D) (sourceKahlerFormOfBackground omegaX) s)
    (hA : HasManifoldAnalyticSingularityType (n := n)
      (uscRegularization (D.pointwiseUpperConcaveEnvelope s))) :
    ∃ y, uscRegularization (D.pointwiseUpperConcaveEnvelope s) (ι y) ≠ ⊥ := by
  have hP := originalHull_traceSlice_pEquivalent_restriction hk omegaX omegaV hι D s hs hA
  obtain ⟨β, _hβT, hβR, _⟩ := hP.1
  obtain ⟨y, _, hy⟩ := hβR.2 (Classical.arbitrary V) univ isOpen_univ (mem_univ _)
  exact ⟨y, hy⟩

/-- The SAME actual original NA trace operator, at every target Kähler
index and every actual below-cutoff parameter. No alternate trace operation. -/
theorem originalHull_naTraceRes_slice_iEquivalent_restriction
    (hk : k ≤ n) (omegaX : KahlerBackground n M) (omegaV : KahlerBackground k V)
    {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hvol : SGPT.Trace.RIsoB.PullbackKahlerVolumePos (M := M) hι)
    (D : PiecewiseLinearData θ) (hwd : TraceWellDefined ι (hullNAPotential D))
    (κV : SourceKahlerForm k V) (s : ℝ)
    (hs : s < ((TraceRes.naTraceRes hk omegaX omegaV hι hvol (hullNAPotential D) hwd).component κV).val.max)
    (hA : HasManifoldAnalyticSingularityType (n := n)
      (uscRegularization (D.pointwiseUpperConcaveEnvelope s))) :
    sourceIEquivalent (ofFixedModel k V)
      (((TraceRes.naTraceRes hk omegaX omegaV hι hvol (hullNAPotential D) hwd).component κV).val.potential ⟨s, hs⟩)
      (fun y => uscRegularization (D.pointwiseUpperConcaveEnvelope s) (ι y)) := by
  have htrace := sliceTraceable_of_lt_traceCutoff hwd (sourceKahlerFormOfBackground omegaX) hs
  exact originalHull_traceComponent_iEquivalent_restriction hk omegaX omegaV hι hvol D κV s htrace hA

end ActualSlices
end SGPT.NAPotential.TraceComparison
