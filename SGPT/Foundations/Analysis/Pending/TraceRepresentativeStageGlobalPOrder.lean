import SGPT.Foundations.Analysis.Pending.SingularNativeGlobalPOrderClosed
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeAllChoices

set_option autoImplicit false

/-! # Actual trace global P-order below every legitimate restricted stage -/

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.TraceRepresentativeStageGlobalPOrder

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  SingularGlobalPOrder ThetaPshL1Topology SingularCanonicalSingularityDistance
  TraceRepresentativeConstruction PluripolarCapacityDichotomy

noncomputable section

section NativeAntitone

variable {k : ℕ} {V : Type*} [TopologicalSpace V] [MeasurableSpace V]
  [BorelSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [CompactSpace V] [ConnectedSpace V]

/-- Literal antitonicity and actual native convergence internally give
the source global order from the limit to each genuine stage. -/
theorem sourcePOrder_le_stage_of_antitone_native_limit
    (omegaV : KahlerBackground k V) (θ : ClosedRealOneOneForm k V)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (a : ℕ → ThetaPshL1 θ.val) (p : ThetaPshL1 θ.val)
    (hanti : Antitone (fun j => (a j).val))
    (hlim : Tendsto a atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omegaV θ hbig).toUniformSpace.toTopologicalSpace p))
    (j : ℕ) : SourcePOrder (n := k) p.val (a j).val := by
  have horder : ∀ᶠ i in atTop, SourcePOrder (n := k) (a i).val (a j).val := by
    filter_upwards [eventually_ge_atTop j] with i hi
    exact sourcePOrder_of_moreSingularOn omegaV θ θ (a i).property (a j).property
      (MoreSingularOn.of_le fun y _ => hanti hi y)
  let := singularityPseudoMetricSpace omegaV θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omegaV θ hbig).toUniformSpace.toTopologicalSpace
  exact SingularNativeGlobalPOrderClosed.sourcePOrder_of_native_limits
    omegaV θ hbig atTop a (fun _ => a j) p (a j) hlim tendsto_const_nhds horder

end NativeAntitone

section ActualTrace

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- Every natural new complete QEA/admissible target internally yields
actual restricted-stage PSH and native convergence before the global order. -/
theorem sourcePOrder_restricted_stage_of_isTraceRepresentativeAlong
    {omega₀ omega₁ : KahlerBackground n M} (omegaV₀ omegaV₁ : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u : M → EReal} {τ : V → EReal}
    (htrace : IsTraceRepresentativeAlong omega₀ omegaV₀ hι u τ)
    {θ : ClosedRealOneOneForm n M} {ε : ℕ → ℝ} {vSeq : ℕ → M → EReal}
    (happ : IsQuasiEquisingularApproximation omega₁ θ u ε vSeq)
    (β : KahlerBackground k V)
    (hadm : IsAdmissibleTraceBackground hι omega₁ θ ε β.form)
    (hτ : IsThetaPshPotential β.form.val τ)
    (j : ℕ) : SourcePOrder (n := k) τ (fun y => vSeq j (ι y)) := by
  obtain ⟨hv, hlim, _⟩ := TraceRepresentativeAllChoices.native_limit_of_isTraceRepresentativeAlong
    omegaV₀ omegaV₁ hι htrace happ β hadm hτ
  let a : ℕ → ThetaPshL1 β.form.val := fun i => ⟨fun y => vSeq i (ι y), hv i⟩
  have hanti : Antitone (fun i => (a i).val) := by
    intro i l hil y
    exact happ.term_antitone (ι y) hil
  exact sourcePOrder_le_stage_of_antitone_native_limit omegaV₁ β.form (isBigClass_kahler β)
    a ⟨τ, hτ⟩ hanti hlim j

end ActualTrace

end

end SGPT.Foundations.Analysis.Pending.TraceRepresentativeStageGlobalPOrder
