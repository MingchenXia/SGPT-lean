import SGPT.Foundations.Analysis.Pending.NumericalTraceMass
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshTraceExistence
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeGlobalPClass

set_option autoImplicit false

/-! # True positive trace domain and total numerical mass independence -/

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.PositiveTraceDomainAuxiliaryIndependence

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation TraceRepresentativeConstruction
  PositiveNormalizedTrace NumericalTraceMass

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

private theorem change_auxiliaries
    {omega₀ : KahlerBackground n M} (omega₁ : KahlerBackground n M)
    {omegaV₀ : KahlerBackground k V} (omegaV₁ : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    (hdefined : HasPositiveTraceRepresentativeAlong omega₀ omegaV₀ hι θ u) :
    HasPositiveTraceRepresentativeAlong omega₁ omegaV₁ hι θ u := by
  obtain ⟨τ, htrace, hτ, hpos⟩ := hdefined
  have hbase := htrace
  obtain ⟨hg, α, ε, U, happ, _, _, _, _, _⟩ := htrace
  obtain ⟨ψ, hψ, _⟩ := GlobalQuasiPshTraceExistence.exists_of_isThetaPshPotential
    omega₁ omegaV₁ happ.target hι hg
  have heq := TraceRepresentativeAllChoices.sourcePEquivalent_of_isTraceRepresentativeAlong
    omegaV₁ omegaV₀ hι hψ hbase
  have hnew := TraceRepresentativeGlobalPClass.isTraceRepresentativeAlong_of_sourcePEquivalent
    omegaV₁ hι hψ heq
  exact ⟨τ, hnew, hτ, hpos⟩

/-- Actual Demailly trace existence and complete global-class stability
produce the new positive domain, rather than assuming auxiliary independence. -/
theorem hasPositiveTraceRepresentativeAlong_iff_auxiliary_choices
    (omega₀ omega₁ : KahlerBackground n M) (omegaV₀ omegaV₁ : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal) :
    HasPositiveTraceRepresentativeAlong omega₀ omegaV₀ hι θ u ↔
      HasPositiveTraceRepresentativeAlong omega₁ omegaV₁ hι θ u := by
  exact ⟨change_auxiliaries omega₁ omegaV₁ hι,
    change_auxiliaries omega₀ omegaV₀ hι⟩

/-- Both positive mass definitions compute one actual reader's mass,
and the genuine auxiliary-domain equivalence handles both zero branches. -/
theorem numericalTraceMass_eq_of_auxiliary_choices
    (omega₀ omega₁ : KahlerBackground n M) (omegaV₀ omegaV₁ : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal) :
    numericalTraceMass omega₀ omegaV₀ hι θ u =
      numericalTraceMass omega₁ omegaV₁ hι θ u := by
  classical
  have hiff := hasPositiveTraceRepresentativeAlong_iff_auxiliary_choices
    omega₀ omega₁ omegaV₀ omegaV₁ hι θ u
  by_cases h₀ : HasPositiveTraceRepresentativeAlong omega₀ omegaV₀ hι θ u
  · have h₁ := hiff.mp h₀
    obtain ⟨htrace, hτ, hpos⟩ := Classical.choose_spec h₀
    have heq₀ := numericalTraceMass_eq_of_positive_reader omegaV₀ omegaV₀ hι θ u
      h₀ htrace hτ hpos
    have heq₁ := numericalTraceMass_eq_of_positive_reader omegaV₁ omegaV₀ hι θ u
      h₁ htrace hτ hpos
    exact heq₀.trans heq₁.symm
  · have h₁ : ¬ HasPositiveTraceRepresentativeAlong omega₁ omegaV₁ hι θ u :=
      fun h => h₀ (hiff.mpr h)
    rw [numericalTraceMass_eq_zero_of_undefined omega₀ omegaV₀ hι θ u h₀,
      numericalTraceMass_eq_zero_of_undefined omega₁ omegaV₁ hι θ u h₁]

end

end SGPT.Foundations.Analysis.Pending.PositiveTraceDomainAuxiliaryIndependence
