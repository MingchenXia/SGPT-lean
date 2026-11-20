import SGPT.Trace.BiholomorphicSingularityEnvelope
import SGPT.Trace.ModificationTrace
import SGPT.Trace.TraceEnvelope
import SGPT.Foundations.Analysis.Pending.AnalyticModificationMixedMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SGPT.Trace
open Set Filter MeasureTheory SGPT.PSH
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SourceTraceRepresentativeDefinition SingularGlobalPOrder DiagonalMass
open scoped Topology Manifold ContDiff ENNReal

section Mass
variable {k : ℕ} {V : Type u} [TopologicalSpace V]
  [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V]

/-- An actual biholomorphism preserving the original form produces the
strong PSH pullback AND its genuine unchanged non-pluripolar mass, all k. -/
theorem exists_psh_comp_biholomorphic_mass
    (β : ClosedRealOneOneForm k V) (f : V ≃ₜ V)
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ f)
    (hfi : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ f.symm)
    (hβ : (ClosedRealOneOneForm.pullback hf β).val.GeometricallyEq β.val)
    {τ : V → EReal} (hτ : IsThetaPshPotential β.val τ) :
    ∃ hτf : IsThetaPshPotential β.val (τ ∘ f),
      diagonalPotentialMass β (τ ∘ f) hτf = diagonalPotentialMass β τ hτ := by
  have hmod := nativeAnalyticModification_of_biholomorphic f hf hfi
  have hp := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hmod β hτ
  have hτf : IsThetaPshPotential β.val (τ ∘ f) := (hβ.thetaPshPotential_iff _).mp hp
  refine ⟨hτf, ?_⟩
  have hm := AnalyticModificationMixedMass.diagonalPotentialMass_pullback_of_isAnalyticModification
    hmod β hτ
  exact (ModificationMassInvariance.diagonalPotentialMass_congr_geometricallyEq
    hβ hp hτf).symm.trans hm
end Mass

section Trace
variable {n k : ℕ} {M V : Type u}
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- Actual commuting biholomorphisms transport the ORIGINAL source trace.
The modification data and P-comparison are internally produced; there is
no caller trace-equivariance or comparison certificate. -/
theorem sourcePEquivalent_trace_comp_biholomorphic_symmetry (hk : k ≤ n)
    (omegaM : KahlerBackground n M) (omegaV : KahlerBackground k V)
    {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (e : M ≃ₜ M) (f : V ≃ₜ V)
    (he : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm)
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ f)
    (hfi : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ f.symm)
    (hcomm : ∀ y, e (ι y) = ι (f y))
    {u : M → EReal} (huinv : u ∘ e = u) {τ : V → EReal}
    (htrace : IsSourceTraceRepresentativeAlong omegaM omegaV hι u τ) :
    SourcePEquivalent (n := k) (τ ∘ f) τ := by
  have hr := sourceTrace_modification_of_commuting hk
    (nativeAnalyticModification_of_biholomorphic e he hei)
    (nativeAnalyticModification_of_biholomorphic f hf hfi)
    omegaM omegaM omegaV omegaV hι hι hcomm htrace
  have ht : IsSourceTraceRepresentativeAlong omegaM omegaV hι (u ∘ e) τ := by
    simpa only [huinv] using htrace
  exact hr.2.2 omegaM omegaV τ ht

/-- The ACTUAL normalized source trace is pointwise invariant under every
actual commuting background-preserving biholomorphic symmetry of u.
All original poles and target dimension0 are retained. This internally
produces the invariance used in the toric trace theorem. -/
theorem sourceTraceEnvelope_comp_biholomorphic_symmetry (hk : k ≤ n)
    (omegaM : KahlerBackground n M) (omegaV : KahlerBackground k V)
    {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (e : M ≃ₜ M) (f : V ≃ₜ V)
    (he : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm)
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ f)
    (hfi : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ f.symm)
    (hcomm : ∀ y, e (ι y) = ι (f y))
    (hβ : (ClosedRealOneOneForm.pullback hf (ClosedRealOneOneForm.pullback hι θ)).val.GeometricallyEq
      (ClosedRealOneOneForm.pullback hι θ).val)
    (hβi : (ClosedRealOneOneForm.pullback hfi (ClosedRealOneOneForm.pullback hι θ)).val.GeometricallyEq
      (ClosedRealOneOneForm.pullback hι θ).val)
    {u : M → EReal} (huinv : u ∘ e = u)
    (hdefined : HasPositiveSourceTraceAlong omegaM omegaV hι θ u) (y : V) :
    sourceTraceEnvelope omegaM omegaV hι θ u hdefined (f y) =
      sourceTraceEnvelope omegaM omegaV hι θ u hdefined y := by
  obtain ⟨htrace, hτ, hpos⟩ := Classical.choose_spec hdefined
  let τ := Classical.choose hdefined
  have hr := sourceTrace_modification_of_commuting hk
    (nativeAnalyticModification_of_biholomorphic e he hei)
    (nativeAnalyticModification_of_biholomorphic f hf hfi)
    omegaM omegaM omegaV omegaV hι hι hcomm htrace
  obtain ⟨κ, htracef⟩ := hr.2.1
  have htracef' : IsSourceTraceRepresentativeAlong κ omegaV hι u (τ ∘ f) := by
    simpa only [huinv] using htracef
  obtain ⟨hτf, hmass⟩ := exists_psh_comp_biholomorphic_mass
    (ClosedRealOneOneForm.pullback hι θ) f hf hfi hβ hτ
  have hposf : HasPositivePotentialMass (ClosedRealOneOneForm.pullback hι θ) (τ ∘ f) hτf := by
    change 0 < diagonalPotentialMass _ _ _
    rw [hmass]
    exact hpos
  have hread := (sourceTraceEnvelope_eq_envelopes hk omegaV omegaV hι θ u hdefined
    htrace hτ hpos).1
  have hreadf := (sourceTraceEnvelope_eq_envelopes hk omegaV omegaV hι θ u hdefined
    htracef' hτf hposf).1
  calc
    sourceTraceEnvelope omegaM omegaV hι θ u hdefined (f y) =
        singularityEnvelope (ClosedRealOneOneForm.pullback hι θ).val τ (f y) := congrFun hread (f y)
    _ = singularityEnvelope (ClosedRealOneOneForm.pullback hι θ).val (τ ∘ f) y :=
      singularityEnvelope_comp_biholomorphic (ClosedRealOneOneForm.pullback hι θ)
        f hf hfi hβ hβi τ y
    _ = sourceTraceEnvelope omegaM omegaV hι θ u hdefined y := (congrFun hreadf y).symm
end Trace
end SGPT.Trace
