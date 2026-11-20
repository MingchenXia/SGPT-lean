import SGPT.Foundations.Analysis.Pending.TraceRepresentativeGlobalPEquivalence
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeAuxiliaryDomination

set_option autoImplicit false

/-! # Global P-equivalence of actual trace readers with different auxiliaries -/

open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.TraceRepresentativeGlobalPEquivalenceAuxiliaries

open FirstPass FirstPass.PositiveClasses TraceRepresentativeConstruction SingularGlobalPOrder

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- A common auxiliary and both complete new trace predicates are produced
internally before applying genuine global P-equivalence. -/
theorem sourcePEquivalent_of_isTraceRepresentativeAlong
    {omega₀ omega₁ : KahlerBackground n M} (omegaV : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u : M → EReal} {τ₀ τ₁ : V → EReal}
    (hT₀ : IsTraceRepresentativeAlong omega₀ omegaV hι u τ₀)
    (hT₁ : IsTraceRepresentativeAlong omega₁ omegaV hι u τ₁) :
    SourcePEquivalent (n := k) τ₀ τ₁ := by
  obtain ⟨κ, h₀, h₁⟩ :=
    QuasiEquisingularAuxiliaryDomination.exists_common_auxiliary_kahler_background omega₀ omega₁
  have hT₀κ := TraceRepresentativeAuxiliaryDomination.isTraceRepresentativeAlong_of_auxiliary_domination
    omegaV hι hT₀ h₀
  have hT₁κ := TraceRepresentativeAuxiliaryDomination.isTraceRepresentativeAlong_of_auxiliary_domination
    omegaV hι hT₁ h₁
  exact TraceRepresentativeGlobalPEquivalence.sourcePEquivalent_of_isTraceRepresentativeAlong
    omegaV hι hT₀κ hT₁κ

end

end SGPT.Foundations.Analysis.Pending.TraceRepresentativeGlobalPEquivalenceAuxiliaries
