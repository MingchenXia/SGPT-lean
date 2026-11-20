import SGPT.Checks.Comparison.TraceResOrder
import SGPT.Trace.BertiniGeneralMember

/-! Actual original trace representatives in the SAME native half background.
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
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SourceTraceRepresentativeDefinition
open scoped Topology Manifold ContDiff ENNReal

variable {n k : ℕ} {M V : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] [ConnectedSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  (hk : k ≤ n) (omegaX : KahlerBackground n M) (omegaV : KahlerBackground k V)
  {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
  (hvol : SGPT.Trace.RIsoB.PullbackKahlerVolumePos (M := M) hι)

/-- The SAME actual NA trace slice INTERNALLY produces a genuine actual
original trace representative in the SAME half-Kahler target background,
with exactly the SAME original I-class and every actual prime reader. -/
theorem exists_actualTraceComponentRepresentative
    (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ι Γ)
    (κV : SourceKahlerForm k V) (s : ℝ)
    (hs : s < ((TraceRes.naTraceRes hk omegaX omegaV hι hvol Γ hwd).component κV).val.max) :
    ∃ ψ : V → EReal,
      IsThetaPshPotential (ClosedRealOneOneForm.pullback hι (atlasClosedFormToNative θ) +
        (1/2 : ℝ) • (sourceKahlerFormRepresentative κV).form).val ψ ∧
      IsSourceTraceRepresentativeAlong omegaX omegaV hι
        (((Γ.component (sourceKahlerFormOfBackground omegaX)).val.potential
          ⟨s, (sliceTraceable_of_lt_traceCutoff hwd (sourceKahlerFormOfBackground omegaX) hs).1⟩)) ψ ∧
      sourceIEquivalent (ofFixedModel k V)
        (((TraceRes.naTraceRes hk omegaX omegaV hι hvol Γ hwd).component κV).val.potential ⟨s,hs⟩) ψ ∧
      ∀ p : PrimePresentation k V,
        presentationReader
          (((TraceRes.naTraceRes hk omegaX omegaV hι hvol Γ hwd).component κV).val.potential ⟨s,hs⟩) p =
          presentationReader ψ p := by
  let hs0 := sliceTraceable_of_lt_traceCutoff hwd (sourceKahlerFormOfBackground omegaX) hs
  obtain ⟨ψ, hψ, hP⟩ := TraceRes.exists_goodTraceSlice hk omegaX omegaV hι hvol Γ κV s hs0
  have hTψ := SGPT.Trace.BertiniGeneral.isSourceTraceRepresentativeAlong_of_sourcePEquivalent
    hι omegaX omegaV (traceSlice_spec hk omegaX omegaV hι Γ s hs0) hψ ⟨hP.2,hP.1⟩
  have hqψ : (ofFixedModel k V).IsQPSH ψ :=
    ⟨_, thetaPSH_traceBackground_of_half hι κV hψ⟩
  have hqT := isQPSH_of_sourceTrace hι (traceSlice_spec hk omegaX omegaV hι Γ s hs0)
  have hI : sourceIEquivalent (ofFixedModel k V) ψ (traceSlice hk omegaX omegaV hι Γ s hs0) :=
    ⟨sourceIOrder_of_sourcePOrder hqψ hqT hP.1, sourceIOrder_of_sourcePOrder hqT hqψ hP.2⟩
  have hcomp : sourceIEquivalent (ofFixedModel k V)
      (((TraceRes.naTraceRes hk omegaX omegaV hι hvol Γ hwd).component κV).val.potential ⟨s,hs⟩) ψ := by
    change sourceIEquivalent (ofFixedModel k V)
      (traceComponentSlice hk omegaX omegaV hι Γ κV s hs0) ψ
    rw [traceComponentSlice_eq hk omegaX omegaV hι Γ κV s hs0 hI]
    exact sourceIEquivalent_symm (sourceIEquivalent_iEnvelope (thetaPSH_traceBackground_of_half hι κV hψ))
  refine ⟨ψ,hψ,hTψ,hcomp,fun p => ?_⟩
  exact le_antisymm
    ((sourceIOrder_iff_presentationComparison hcomp.2.1 hcomp.2.2.1).mp hcomp.2 p)
    ((sourceIOrder_iff_presentationComparison hcomp.1.1 hcomp.1.2.1).mp hcomp.1 p)

end SGPT.NAPotential.TraceComparison
