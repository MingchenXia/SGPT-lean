import SGPT.Checks.Comparison.TraceResActualRepresentatives
import SGPT.Checks.Comparison.TracePrimeNativeLimit

/-! Actual ORIGINAL trace-component prime readers under an actual NA infimum.
Blueprint: `trace-res-prime-limit.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SGPT.NAPotential.TraceComparison

open Set Filter
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.NATrace
open SGPT.PSH.CompactPrimeOver SGPT.PSH.CompactPrimeNumerical
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SourceTraceRepresentativeDefinition ThetaPshL1Topology SingularCanonicalSingularityDistance
open scoped Topology Manifold ContDiff ENNReal

variable {n k : ℕ} {M V : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] [ConnectedSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  (hk : k ≤ n) (omegaX : KahlerBackground n M) (omegaV : KahlerBackground k V)
  {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
  (hvol : SGPT.Trace.RIsoB.PullbackKahlerVolumePos (M := M) hι)

/-- The UNCHANGED actual trace-component prime reader of the ACTUAL
original NA decreasing infimum is the limit of the UNCHANGED actual member
trace-component readers. All actual trace representatives, common target
background, native dS limits and same-prime dictionaries are internal. -/
theorem tendsto_traceRes_component_presentationReader_decreasingInf
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (Γ : I → SourceNAPotential θ) (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omegaX (Γ i)))
    (hwd : TraceWellDefined ι (SourceNAPotential.decreasingInf omegaX Γ ha hb))
    (κV : SourceKahlerForm k V) {s : ℝ}
    (hs : s < ((TraceRes.naTraceRes hk omegaX omegaV hι hvol
      (SourceNAPotential.decreasingInf omegaX Γ ha hb) hwd).component κV).val.max)
    (p : PrimePresentation k V) :
    Tendsto (fun i => presentationReader
      (((TraceRes.naTraceRes hk omegaX omegaV hι hvol (Γ i)
        (traceWellDefined_of_naOrder (SourceNAPotential.decreasingInf_le omegaX Γ ha hb i) hwd)).component κV).val.potential
          ⟨s, hs.trans_le (traceCutoff_mono_of_naOrder
            (SourceNAPotential.decreasingInf_le omegaX Γ ha hb i) hwd (sourceKahlerFormOfBackground omegaX))⟩) p) atTop
      (𝓝 (presentationReader
        (((TraceRes.naTraceRes hk omegaX omegaV hι hvol
          (SourceNAPotential.decreasingInf omegaX Γ ha hb) hwd).component κV).val.potential ⟨s,hs⟩) p)) := by
  classical
  let D := SourceNAPotential.decreasingInf omegaX Γ ha hb
  let κX := sourceKahlerFormOfBackground omegaX
  let αX := sourceNAComponentBackground θ κX
  let G : I → SourcePositiveIModelTestCurve αX := fun i => (Γ i).component κX
  have hGa := sourceNAFamily_component_antitone Γ ha κX
  have hGb := sourceNAFamily_component_bddBelow omegaX Γ hb κX
  have hGm := sourceNAFamily_component_massCondition omegaX Γ hb κX
  let hwdi (i : I) := traceWellDefined_of_naOrder
    (SourceNAPotential.decreasingInf_le omegaX Γ ha hb i) hwd
  let hsi (i : I) : s < ((TraceRes.naTraceRes hk omegaX omegaV hι hvol (Γ i) (hwdi i)).component κV).val.max :=
    hs.trans_le (traceCutoff_mono_of_naOrder (SourceNAPotential.decreasingInf_le omegaX Γ ha hb i) hwd κX)
  obtain ⟨ψ,hψ,hT,hI,hR⟩ := exists_actualTraceComponentRepresentative hk omegaX omegaV hι hvol D hwd κV s hs
  choose ψi hψi hTi hIi hRi using fun i =>
    exists_actualTraceComponentRepresentative hk omegaX omegaV hι hvol (Γ i) (hwdi i) κV s (hsi i)
  let β := ClosedRealOneOneForm.pullback hι (atlasClosedFormToNative θ) +
    (1/2 : ℝ) • (sourceKahlerFormRepresentative κV).form
  let αV := sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV
  let η := atlasClosedFormToNative αV
  have hη : η = β + (1/2 : ℝ) • (sourceKahlerFormRepresentative κV).form := by
    change atlasClosedFormToNative (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV) = _
    rw [traceBackground_native hι κV]
    dsimp only [β]
    rw [add_assoc, ← add_smul]
    norm_num
  have hbigV : IsBigClass (RealBottChern.ofRepresentative η) := by
    rw [hη]
    exact PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential
      (sourceKahlerFormRepresentative κV) β hψ (by norm_num : (0 : ℝ) < 1/2)
  let vi : I → ThetaPshL1 η.val := fun i =>
    ⟨ψi i, (isThetaPSH_iff_nativeThetaPotential αV _).mp (thetaPSH_traceBackground_of_half hι κV (hψi i))⟩
  let v : ThetaPshL1 η.val :=
    ⟨ψ, (isThetaPSH_iff_nativeThetaPotential αV _).mp (thetaPSH_traceBackground_of_half hι κV hψ)⟩
  have hsX := (sliceTraceable_of_lt_traceCutoff hwd κX hs).1
  have hsiX (i : I) : s < (G i).val.max :=
    hsX.trans_le (sourceTestCurveInfCutoff_le (fun i => (G i).val) hGb i)
  let wi : I → SourceThetaPotentialL1 αX := fun i => ⟨(G i).val.potential ⟨s,hsiX i⟩,(G i).val.thetaPSH _⟩
  let w : SourceThetaPotentialL1 αX := ⟨(D.component κX).val.potential ⟨s,hsX⟩,(D.component κX).val.thetaPSH _⟩
  obtain ⟨hbigX,hlimX⟩ := exists_sourceSingularityLimit_curve_decreasingInf
    (sourceKahlerFormRepresentative κX) G hGa hGb hGm hsX
  let := sourceSingularityPseudoMetricSpace (sourceKahlerFormRepresentative κX) αX hbigX
  let : UniformSpace (SourceThetaPotentialL1 αX) := sourceSingularityUniformSpace (sourceKahlerFormRepresentative κX) αX hbigX
  let : TopologicalSpace (SourceThetaPotentialL1 αX) := sourceSingularityTopology (sourceKahlerFormRepresentative κX) αX hbigX
  let := singularityPseudoMetricSpace (sourceKahlerFormRepresentative κX) (atlasClosedFormToNative αX) hbigX
  let : UniformSpace (ThetaPshL1 (atlasClosedFormToNative αX).val) :=
    (singularityPseudoMetricSpace (sourceKahlerFormRepresentative κX) (atlasClosedFormToNative αX) hbigX).toUniformSpace
  let : TopologicalSpace (ThetaPshL1 (atlasClosedFormToNative αX).val) :=
    (singularityPseudoMetricSpace (sourceKahlerFormRepresentative κX) (atlasClosedFormToNative αX) hbigX).toUniformSpace.toTopologicalSpace
  have hmap : Topology.IsInducing (sourceThetaPotentialL1EquivNative αX) := Topology.IsInducing.induced _
  have hlimN := hmap.tendsto_nhds_iff.mp hlimX
  have hanti : ∀ x, Antitone (fun i => (sourceThetaPotentialL1EquivNative αX (wi i)).val x) := by
    intro x i j hij
    exact sourceTestCurveInfSlice_antitone (sourceKahlerFormRepresentative κX)
      (fun i => (G i).val) hGa hGb ⟨s,hsX⟩ x hij
  have hlimT := SGPT.Trace.tendsto_trace_of_antitone_net hk
    (sourceKahlerFormRepresentative κX) omegaV (atlasClosedFormToNative αX) hbigX
    (fun i => sourceThetaPotentialL1EquivNative αX (wi i)) (sourceThetaPotentialL1EquivNative αX w)
    hanti hlimN hι η hbigV vi v hTi hT
  have hreader := tendsto_presentationReader_of_native omegaV η hbigV atTop vi v hlimT p
  change Tendsto (fun i => presentationReader
    (((TraceRes.naTraceRes hk omegaX omegaV hι hvol (Γ i) (hwdi i)).component κV).val.potential ⟨s,hsi i⟩) p) atTop
    (𝓝 (presentationReader
      (((TraceRes.naTraceRes hk omegaX omegaV hι hvol D hwd).component κV).val.potential ⟨s,hs⟩) p))
  rw [hR p]
  exact hreader.congr' (Eventually.of_forall fun i => (hRi i p).symm)

end SGPT.NAPotential.TraceComparison
