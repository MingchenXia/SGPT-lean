import SGPT.Foundations.Analysis.Pending.QuasiEquisingularAdditionGenericLelong
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeAddition

set_option autoImplicit false

/-! # Natural trace addition, with the ambient sum domain internally produced -/

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.TraceAdditionNaturalDomain

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  TraceRepresentativeConstruction SingularGlobalPOrder

noncomputable section

variable {n k : ℕ} {M Y : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]

/-- The two original full readers alone produce the sum domain and its
complete additive reader; all original readers of the sum have this class. -/
theorem exists_additive_trace_reader_with_all_choices
    {omega₀ omega₁ : KahlerBackground n M}
    (omegaY₀ omegaY₁ omegaY : KahlerBackground k Y)
    {ι : Y → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u v : M → EReal} {τᵤ τᵥ : Y → EReal}
    (hTu : IsTraceRepresentativeAlong omega₀ omegaY₀ hι u τᵤ)
    (hTv : IsTraceRepresentativeAlong omega₁ omegaY₁ hι v τᵥ) :
    ∃ omega : KahlerBackground n M,
      IsTraceRepresentativeAlong omega omegaY hι
        (fun x => u x + v x) (fun y => τᵤ y + τᵥ y) ∧
      ∀ (omegaS : KahlerBackground n M) (omegaYS : KahlerBackground k Y)
        (τs : Y → EReal),
        IsTraceRepresentativeAlong omegaS omegaYS hι (fun x => u x + v x) τs →
        SourcePEquivalent (n := k) τs (fun y => τᵤ y + τᵥ y) := by
  have hTuKeep := hTu
  have hTvKeep := hTv
  obtain ⟨hgu, θ, ε, U, hu, _, _, _, _, _⟩ := hTu
  obtain ⟨hgv, σ, δ, V, hv, _, _, _, _, _⟩ := hTv
  obtain ⟨κ, hκ₀, hκ₁⟩ :=
    QuasiEquisingularAuxiliaryDomination.exists_common_auxiliary_kahler_background omega₀ omega₁
  have huκ := QuasiEquisingularAuxiliaryDomination.isQuasiEquisingularApproximation_of_auxiliary_domination
    hu hκ₀
  have hvκ := QuasiEquisingularAuxiliaryDomination.isQuasiEquisingularApproximation_of_auxiliary_domination
    hv hκ₁
  have hgsum := QuasiEquisingularAdditionGenericLelong.generic_lelong_inf_add_eq_zero
    huκ hvκ hι hgu hgv
  obtain ⟨omega, hadd⟩ := TraceRepresentativeAddition.isTraceRepresentativeAlong_add
    omegaY₀ omegaY₁ omegaY hι hTuKeep hTvKeep hgsum
  refine ⟨omega, hadd, ?_⟩
  intro omegaS omegaYS τs hTs
  exact TraceRepresentativeAllChoices.sourcePEquivalent_of_isTraceRepresentativeAlong
    omegaYS omegaY hι hTs hadd

end

end SGPT.Foundations.Analysis.Pending.TraceAdditionNaturalDomain
