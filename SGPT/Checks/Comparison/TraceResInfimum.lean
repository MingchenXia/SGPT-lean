import SGPT.Checks.Comparison.TraceResPrimeLimit

/-! The UNCHANGED original NA trace commutes with its ACTUAL original infimum.
Blueprint: `trace-res-prime-limit.tex`. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
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

private theorem na_eq_of_component_readers
    {q : ℕ} {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [ChartedSpace (ComplexModel q) Y] [IsComplexManifold q Y] [CompactSpace Y] [ConnectedSpace Y]
    {α : AtlasClosedRealOneOneForm (ofFixedModel q Y)}
    (T E : SourceNAPotential α)
    (hmax : ∀ κ, (T.component κ).val.max = (E.component κ).val.max)
    (hreader : ∀ κ s hsT hsE (p : PrimePresentation q Y),
      presentationReader ((T.component κ).val.potential ⟨s,hsT⟩) p =
        presentationReader ((E.component κ).val.potential ⟨s,hsE⟩) p) : T = E := by
  apply SourceNAPotential.ext
  intro κ
  apply Subtype.ext
  apply SourceTestCurve.ext_of_max_potential _ _ (hmax κ)
  intro s hsT hsE
  have hqT : (ofFixedModel q Y).IsQPSH ((T.component κ).val.potential ⟨s,hsT⟩) :=
    ⟨_, (T.component κ).val.thetaPSH _⟩
  have hqE : (ofFixedModel q Y).IsQPSH ((E.component κ).val.potential ⟨s,hsE⟩) :=
    ⟨_, (E.component κ).val.thetaPSH _⟩
  have hI : sourceIEquivalent (ofFixedModel q Y)
      ((T.component κ).val.potential ⟨s,hsT⟩) ((E.component κ).val.potential ⟨s,hsE⟩) :=
    ⟨(sourceIOrder_iff_presentationComparison hqT hqE).mpr (fun p => (hreader κ s hsT hsE p).ge),
      (sourceIOrder_iff_presentationComparison hqE hqT).mpr (fun p => (hreader κ s hsT hsE p).le)⟩
  have hmT := ((sourceIModelTestCurvesPositive_iff_slices (sourceKahlerFormRepresentative κ)
    (T.component κ).val).mp (T.component κ).property) ⟨s,hsT⟩
  have hmE := ((sourceIModelTestCurvesPositive_iff_slices (sourceKahlerFormRepresentative κ)
    (E.component κ).val).mp (E.component κ).property) ⟨s,hsE⟩
  have he : sourceIEnvelope (sourceNAComponentBackground α κ) ((T.component κ).val.potential ⟨s,hsT⟩) =
      sourceIEnvelope (sourceNAComponentBackground α κ) ((E.component κ).val.potential ⟨s,hsE⟩) :=
    sourceIEnvelope_eq_of_equivalent hI
  have hmTS := (sourceIModel_iff_native (sourceNAComponentBackground α κ) _).mpr hmT
  have hmES := (sourceIModel_iff_native (sourceNAComponentBackground α κ) _).mpr hmE
  exact hmTS.2.trans (he.trans hmES.2.symm)

private theorem na_inf_component_max
    {q : ℕ} {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [ChartedSpace (ComplexModel q) Y] [IsComplexManifold q Y] [CompactSpace Y] [ConnectedSpace Y]
    {α : AtlasClosedRealOneOneForm (ofFixedModel q Y)} {I : Type*}
    [Preorder I] [IsDirectedOrder I] [Nonempty I] (omega : KahlerBackground q Y)
    (Δ : I → SourceNAPotential α) (ha : ∀ i j, i ≤ j → SourceNAPOrder (Δ j) (Δ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Δ i))) (κ : SourceKahlerForm q Y) :
    ((SourceNAPotential.decreasingInf omega Δ ha hb).component κ).val.max =
      sInf (range fun i => ((Δ i).component κ).val.max) := rfl

private theorem na_inf_prime_reader_limit
    {q : ℕ} {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [ChartedSpace (ComplexModel q) Y] [IsComplexManifold q Y] [CompactSpace Y] [ConnectedSpace Y]
    {α : AtlasClosedRealOneOneForm (ofFixedModel q Y)} {I : Type*}
    [Preorder I] [IsDirectedOrder I] [Nonempty I] (omega : KahlerBackground q Y)
    (Δ : I → SourceNAPotential α) (ha : ∀ i j, i ≤ j → SourceNAPOrder (Δ j) (Δ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Δ i))) (κ : SourceKahlerForm q Y)
    {s : ℝ} (hs : s < ((SourceNAPotential.decreasingInf omega Δ ha hb).component κ).val.max)
    (p : PrimePresentation q Y) :
    Tendsto (fun i => presentationReader (((Δ i).component κ).val.potential
      ⟨s, hs.trans_le (sourceTestCurveInfCutoff_le (fun i => ((Δ i).component κ).val)
        (sourceNAFamily_component_bddBelow omega Δ hb κ) i)⟩) p) atTop
      (𝓝 (presentationReader (((SourceNAPotential.decreasingInf omega Δ ha hb).component κ).val.potential ⟨s,hs⟩) p)) :=
  BJPrep.tendsto_presentationReader_decreasingInf (sourceKahlerFormRepresentative κ)
    (fun i => (Δ i).component κ) (sourceNAFamily_component_antitone Δ ha κ)
    (sourceNAFamily_component_bddBelow omega Δ hb κ) (sourceNAFamily_component_massCondition omega Δ hb κ) p hs

variable {n k : ℕ} {M V : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] [ConnectedSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  (hk : k ≤ n) (omegaX : KahlerBackground n M) (omegaV : KahlerBackground k V)
  {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
  (hvol : SGPT.Trace.RIsoB.PullbackKahlerVolumePos (M := M) hι)

variable {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]

/-- The SAME actual original member traces, with every well-definedness
proof produced from the ACTUAL original source infimum. -/
def traceResFamily (Γ : I → SourceNAPotential θ)
    (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omegaX (Γ i)))
    (hwd : TraceWellDefined ι (SourceNAPotential.decreasingInf omegaX Γ ha hb)) :
    I → SourceNAPotential (θ.nativeHolomorphicPullback hι) := fun i =>
  TraceRes.naTraceRes hk omegaX omegaV hι hvol (Γ i)
    (traceWellDefined_of_naOrder (SourceNAPotential.decreasingInf_le omegaX Γ ha hb i) hwd)

/-- Actual original member traces are intrinsically antitone, internally. -/
theorem traceResFamily_antitone (Γ : I → SourceNAPotential θ)
    (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omegaX (Γ i)))
    (hwd : TraceWellDefined ι (SourceNAPotential.decreasingInf omegaX Γ ha hb)) :
    ∀ i j, i ≤ j → SourceNAPOrder (traceResFamily hk omegaX omegaV hι hvol Γ ha hb hwd j)
      (traceResFamily hk omegaX omegaV hι hvol Γ ha hb hwd i) := by
  intro i j hij
  exact naTraceRes_mono_of_naOrder hk omegaX omegaV hι hvol (ha i j hij)
    (traceWellDefined_of_naOrder (SourceNAPotential.decreasingInf_le omegaX Γ ha hb j) hwd)

/-- The ACTUAL original member trace cutoffs have a genuine lower bound
provided by the ACTUAL original trace of the source infimum. -/
theorem traceResFamily_bddBelow (Γ : I → SourceNAPotential θ)
    (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omegaX (Γ i)))
    (hwd : TraceWellDefined ι (SourceNAPotential.decreasingInf omegaX Γ ha hb)) :
    BddBelow (range fun i => sourceNAPotentialCutoff omegaV
      (traceResFamily hk omegaX omegaV hι hvol Γ ha hb hwd i)) := by
  refine ⟨traceCutoff ι (SourceNAPotential.decreasingInf omegaX Γ ha hb)
    (sourceKahlerFormOfBackground omegaX), ?_⟩
  rintro _ ⟨i,rfl⟩
  exact traceCutoff_mono_of_naOrder (SourceNAPotential.decreasingInf_le omegaX Γ ha hb i) hwd
    (sourceKahlerFormOfBackground omegaX)

/-- **The UNCHANGED actual original NA trace COMMUTES with the ACTUAL
original decreasing NA infimum.** Every target family/order/boundedness,
actual source/trace slice reader limit and cutoff equality is internal. -/
theorem naTraceRes_decreasingInf (Γ : I → SourceNAPotential θ)
    (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omegaX (Γ i)))
    (hwd : TraceWellDefined ι (SourceNAPotential.decreasingInf omegaX Γ ha hb)) :
    TraceRes.naTraceRes hk omegaX omegaV hι hvol
      (SourceNAPotential.decreasingInf omegaX Γ ha hb) hwd =
      SourceNAPotential.decreasingInf omegaV (traceResFamily hk omegaX omegaV hι hvol Γ ha hb hwd)
        (traceResFamily_antitone hk omegaX omegaV hι hvol Γ ha hb hwd)
        (traceResFamily_bddBelow hk omegaX omegaV hι hvol Γ ha hb hwd) := by
  let D := SourceNAPotential.decreasingInf omegaX Γ ha hb
  let Δ := traceResFamily hk omegaX omegaV hι hvol Γ ha hb hwd
  let hΔa := traceResFamily_antitone hk omegaX omegaV hι hvol Γ ha hb hwd
  let hΔb := traceResFamily_bddBelow hk omegaX omegaV hι hvol Γ ha hb hwd
  let T := TraceRes.naTraceRes hk omegaX omegaV hι hvol D hwd
  let E := SourceNAPotential.decreasingInf omegaV Δ hΔa hΔb
  change T = E
  apply na_eq_of_component_readers T E
  · intro κV
    calc
      (T.component κV).val.max = traceCutoff ι D (sourceKahlerFormOfBackground omegaX) :=
        TraceRes.naTraceRes_max hk omegaX omegaV hι hvol D hwd κV (sourceKahlerFormOfBackground omegaX)
      _ = sInf (range fun i => traceCutoff ι (Γ i) (sourceKahlerFormOfBackground omegaX)) :=
        traceCutoff_decreasingInf omegaX Γ ha hb hwd (sourceKahlerFormOfBackground omegaX)
      _ = sInf (range fun i => ((Δ i).component κV).val.max) := rfl
      _ = (E.component κV).val.max := (na_inf_component_max omegaV Δ hΔa hΔb κV).symm
  · intro κV s hsT hsE p
    have hfirst := tendsto_traceRes_component_presentationReader_decreasingInf
      hk omegaX omegaV hι hvol Γ ha hb hwd κV hsT p
    have hsecond := na_inf_prime_reader_limit omegaV Δ hΔa hΔb κV hsE p
    exact tendsto_nhds_unique hfirst hsecond


/-- The EXISTING unchanged original native divisorial transforms of the
actual traces commute with the actual original source infimum. -/
theorem naTraceRes_divisorial_decreasingInf (Γ : I → SourceNAPotential θ)
    (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omegaX (Γ i)))
    (hwd : TraceWellDefined ι (SourceNAPotential.decreasingInf omegaX Γ ha hb))
    (κV : SourceKahlerForm k V) (p : PrimePresentation k V) {c : ℝ} (hc : 0 < c) :
    BJPrep.naDivisorialTransform (TraceRes.naTraceRes hk omegaX omegaV hι hvol
      (SourceNAPotential.decreasingInf omegaX Γ ha hb) hwd) κV p c =
      ⨅ i, BJPrep.naDivisorialTransform (traceResFamily hk omegaX omegaV hι hvol Γ ha hb hwd i) κV p c := by
  rw [naTraceRes_decreasingInf hk omegaX omegaV hι hvol Γ ha hb hwd]
  exact BJPrep.naDivisorialTransform_decreasingInf omegaV
    (traceResFamily hk omegaX omegaV hι hvol Γ ha hb hwd)
    (traceResFamily_antitone hk omegaX omegaV hι hvol Γ ha hb hwd)
    (traceResFamily_bddBelow hk omegaX omegaV hι hvol Γ ha hb hwd) κV p hc

end SGPT.NAPotential.TraceComparison
