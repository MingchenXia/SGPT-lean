import SGPT.Foundations.Analysis.Pending.PositiveNormalizedTrace
import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeMassProof
import SGPT.Foundations.Analysis.Pending.RelativeFullMass

set_option autoImplicit false

/-! # Actual positive normalized model trace and numerical non-pluripolar mass -/

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.NumericalTraceMass

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.IEnvelope
  TraceRepresentativeConstruction DiagonalMass PositiveNormalizedTrace

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- The actual normalized potential is a genuine positive ordinary model
and an I-model; its domain supplies the original mass positivity. -/
theorem normalizedTraceAlong_models
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hdefined : HasPositiveTraceRepresentativeAlong omega omegaV hι θ u) :
    IsModelPotential (ClosedRealOneOneForm.pullback hι θ)
        (normalizedTraceAlong omega omegaV hι θ u hdefined) ∧
      IsIModelPotential (ClosedRealOneOneForm.pullback hι θ).val
        (normalizedTraceAlong omega omegaV hι θ u hdefined) := by
  obtain ⟨htrace, hτ, hpos⟩ := Classical.choose_spec hdefined
  let η := ClosedRealOneOneForm.pullback hι θ
  let τ := Classical.choose hdefined
  have heq := (normalizedTraceAlong_eq_envelopes omegaV omegaV hι θ u
    hdefined htrace hτ hpos).2
  have hI := iSingularityEnvelope_isIModelPotential η.val η.property.1 η.property.2
    hτ.1.hasSmoothLocalPotentials τ hτ
  have hN : IsIModelPotential η.val (normalizedTraceAlong omega omegaV hι θ u hdefined) :=
    heq.symm ▸ hI
  have hmass := singularityEnvelopeMassPreserving omegaV η τ hτ hN.plurisubharmonic
  refine ⟨⟨hN.plurisubharmonic, ?_, hmass.symm ▸ hpos⟩, hN⟩
  rw [heq]
  exact (singularityEnvelope_iSingularityEnvelope η.val η.property.1 η.property.2
    hτ.1.hasSmoothLocalPotentials τ hτ).symm

/-- The actual diagonal global NP mass of the defined normalized trace,
and zero exactly when its positive reader existence domain is absent. -/
def numericalTraceMass
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal) : ENNReal := by
  classical
  exact if hdefined : HasPositiveTraceRepresentativeAlong omega omegaV hι θ u then
    diagonalPotentialMass (ClosedRealOneOneForm.pullback hι θ)
      (normalizedTraceAlong omega omegaV hι θ u hdefined)
      (normalizedTraceAlong_models omega omegaV hι θ u hdefined).1.plurisubharmonic
  else 0

/-- Any natural positive reader computes the actual numerical trace mass,
even when its full approximation and auxiliary choices differ. -/
theorem numericalTraceMass_eq_of_positive_reader
    {omega₀ omega₁ : KahlerBackground n M} (omegaV₀ omegaV₁ : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hdefined : HasPositiveTraceRepresentativeAlong omega₀ omegaV₀ hι θ u)
    {τ : V → EReal}
    (htrace : IsTraceRepresentativeAlong omega₁ omegaV₁ hι u τ)
    (hτ : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val τ)
    (hpos : HasPositivePotentialMass (ClosedRealOneOneForm.pullback hι θ) τ hτ) :
    numericalTraceMass omega₀ omegaV₀ hι θ u =
      diagonalPotentialMass (ClosedRealOneOneForm.pullback hι θ) τ hτ := by
  classical
  simp only [numericalTraceMass, dif_pos hdefined]
  have heq := (normalizedTraceAlong_eq_envelopes omegaV₀ omegaV₁ hι θ u
    hdefined htrace hτ hpos).1
  let η := ClosedRealOneOneForm.pullback hι θ
  let hN := (normalizedTraceAlong_models omega₀ omegaV₀ hι θ u hdefined).1.plurisubharmonic
  have hP : IsThetaPshPotential η.val (singularityEnvelope η.val τ) := heq ▸ hN
  have hcongr (a b : V → EReal) (ha : IsThetaPshPotential η.val a)
      (hb : IsThetaPshPotential η.val b) (hab : a = b) :
      diagonalPotentialMass η a ha = diagonalPotentialMass η b hb := by
    subst b
    rfl
  exact (hcongr _ _ hN hP heq).trans (singularityEnvelopeMassPreserving omegaV₀ η τ hτ hP)

/-- This is the source's actual undefined-normalized-trace zero convention. -/
theorem numericalTraceMass_eq_zero_of_undefined
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hundefined : ¬ HasPositiveTraceRepresentativeAlong omega omegaV hι θ u) :
    numericalTraceMass omega omegaV hι θ u = 0 := by
  classical
  simp only [numericalTraceMass, dif_neg hundefined]

end

end SGPT.Foundations.Analysis.Pending.NumericalTraceMass
