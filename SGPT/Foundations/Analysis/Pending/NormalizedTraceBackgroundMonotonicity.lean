import SGPT.Foundations.Analysis.Pending.NumericalTraceMass
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeGlobalPClass
import SGPT.Foundations.Analysis.Pending.PositiveReferenceGlobalPOrder
import SGPT.Foundations.Analysis.Pending.TraceFreeLimit

set_option autoImplicit false

/-! # Actual normalized trace readers and semipositive background monotonicity -/

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.NormalizedTraceBackgroundMonotonicity

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.POrder TraceRepresentativeConstruction DiagonalMass
  PositiveNormalizedTrace NumericalTraceMass SingularGlobalPOrder

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

omit [CompactSpace M] in
/-- The actual normalized value belongs to the same complete reader class;
the full predicate is produced from its natural positive existence domain. -/
theorem isTraceRepresentativeAlong_normalizedTraceAlong
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hdefined : HasPositiveTraceRepresentativeAlong omega omegaV hι θ u) :
    IsTraceRepresentativeAlong omega omegaV hι u
      (normalizedTraceAlong omega omegaV hι θ u hdefined) := by
  obtain ⟨htrace, hτ, _⟩ := Classical.choose_spec hdefined
  exact TraceRepresentativeGlobalPClass.isTraceRepresentativeAlong_of_sourcePEquivalent
    omegaV hι htrace
    (SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope
      omegaV (ClosedRealOneOneForm.pullback hι θ) hτ)

/-- The natural positive domains and actual semipositive background difference
produce pointwise monotonicity, with every original auxiliary arbitrary. -/
theorem normalizedTraceAlong_le_of_semipositive_difference
    (omega₀ omega₁ : KahlerBackground n M)
    (omegaV₀ omegaV₁ : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ σ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hsemi : (σ - θ).val.IsSemipositive)
    (hdefined₀ : HasPositiveTraceRepresentativeAlong omega₀ omegaV₀ hι θ u)
    (hdefined₁ : HasPositiveTraceRepresentativeAlong omega₁ omegaV₁ hι σ u) :
    normalizedTraceAlong omega₀ omegaV₀ hι θ u hdefined₀ ≤
      normalizedTraceAlong omega₁ omegaV₁ hι σ u hdefined₁ := by
  let η := ClosedRealOneOneForm.pullback hι θ
  let ξ := ClosedRealOneOneForm.pullback hι σ
  let A := normalizedTraceAlong omega₀ omegaV₀ hι θ u hdefined₀
  let B := normalizedTraceAlong omega₁ omegaV₁ hι σ u hdefined₁
  have hA : IsModelPotential η A :=
    (normalizedTraceAlong_models omega₀ omegaV₀ hι θ u hdefined₀).1
  have hB : IsModelPotential ξ B :=
    (normalizedTraceAlong_models omega₁ omegaV₁ hι σ u hdefined₁).1
  have hT₀ : IsTraceRepresentativeAlong omega₀ omegaV₀ hι u A :=
    isTraceRepresentativeAlong_normalizedTraceAlong omega₀ omegaV₀ hι θ u hdefined₀
  have hT₁ : IsTraceRepresentativeAlong omega₁ omegaV₁ hι u B :=
    isTraceRepresentativeAlong_normalizedTraceAlong omega₁ omegaV₁ hι σ u hdefined₁
  have heq : SourcePEquivalent (n := k) A B :=
    TraceRepresentativeAllChoices.sourcePEquivalent_of_isTraceRepresentativeAlong
      omegaV₀ omegaV₁ hι hT₀ hT₁
  have hpull : ClosedRealOneOneForm.pullback hι (σ - θ) = ξ - η := by
    apply ClosedRealOneOneForm.ext
    intro e z
    ext v
    rfl
  have hdiff : (ξ - η).val.IsSemipositive := by
    rw [← hpull]
    exact ClosedRealOneOneForm.pullback_isSemipositive hι hsemi
  have hAξ : IsThetaPshPotential ξ.val A := by
    simpa only [add_sub_cancel] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hA.plurisubharmonic hdiff
  have hfixed : POrderWith ξ A B :=
    PositiveReferenceGlobalPOrder.pOrderWith_of_sourcePOrder_of_positive_right_mass
      omegaV₀ ξ hAξ hB.plurisubharmonic hB.positive_mass heq.1
  have hA0 : A ≤ 0 := by
    rw [hA.envelope_eq]
    exact singularityEnvelope_le_zero η.val A
  have hself : A ≤ singularityEnvelope ξ.val A :=
    le_singularityEnvelope hAξ hA0 ⟨0, by intro x _; simp⟩
  intro x
  exact (hself x).trans ((hfixed x).trans_eq (congrFun hB.envelope_eq x).symm)

end

end SGPT.Foundations.Analysis.Pending.NormalizedTraceBackgroundMonotonicity
