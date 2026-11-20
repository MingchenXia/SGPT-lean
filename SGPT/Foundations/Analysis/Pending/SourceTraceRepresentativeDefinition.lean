import SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeConstruction

set_option autoImplicit false

/-! # Source trace representatives in every ambient dimension

The generic condition uses the independently defined squared-logarithm
growth reader, including its source value zero in ambient dimension zero.
The actual QEA, admissible background, literal restrictions and native
metric topology agree with the existing trace predicate. This module does
not assert representative existence or order for an arbitrary fixed
admissible background.
-/

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  ThetaPshL1Topology SingularCanonicalSingularityDistance PluripolarCapacityDichotomy
  SquaredLogLelongSourceNormalization

noncomputable section

variable {n : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M]

/-- The whole-target infimum of the source growth reader. -/
def sourceGenericLelongNumber (ι : V → M) (u : M → EReal) : ℝ≥0∞ :=
  ⨅ y : V, squaredLogLelongNumber (n := n) u (ι y)

/-- The source generic condition does not discard zero-dimensional
ambient manifolds when the original target is nonempty. -/
theorem sourceGenericLelongNumber_zero_dimension [Nonempty V]
    (hn : n = 0) (ι : V → M) (u : M → EReal) :
    sourceGenericLelongNumber (n := n) ι u = 0 := by
  simp [sourceGenericLelongNumber, squaredLogLelongNumber, hn]

/-- The same target infimum has factor two in positive ambient dimension,
including infinite values and empty targets. -/
theorem nativeGeneric_eq_two_mul_source (hn : n ≠ 0)
    (ι : V → M) (u : M → EReal) :
    (⨅ y : V, lelongNumber (n := n) u (ι y)) =
      2 * sourceGenericLelongNumber (n := n) ι u := by
  unfold sourceGenericLelongNumber
  simp_rw [lelongNumber_eq_two_mul_squaredLog hn,
    ← ENNReal.mul_iInf_of_ne (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]

/-- Finite positive normalization preserves the generic zero condition. -/
theorem nativeGeneric_zero_iff_source (hn : n ≠ 0)
    (ι : V → M) (u : M → EReal) :
    (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0 ↔
      sourceGenericLelongNumber (n := n) ι u = 0 := by
  rw [nativeGeneric_eq_two_mul_source hn]
  simp

variable {k : ℕ} [IsComplexManifold n M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- Source Definition 8.1.1, with its source generic growth convention and
the complete actual approximation and native metric-limit clauses. -/
def IsSourceTraceRepresentativeAlong
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (u : M → EReal) (τ : V → EReal) : Prop :=
  sourceGenericLelongNumber (n := n) ι u = 0 ∧
    ∃ (θ : ClosedRealOneOneForm n M) (ε : ℕ → ℝ) (uSeq : ℕ → M → EReal),
      IsQuasiEquisingularApproximation omega θ u ε uSeq ∧
      ∃ β : KahlerBackground k V,
        IsAdmissibleTraceBackground hι omega θ ε β.form ∧
        ∃ hτ : IsThetaPshPotential β.form.val τ,
          ∃ hterms : ∀ j, IsThetaPshPotential β.form.val (fun y => uSeq j (ι y)),
            Tendsto (fun j => (⟨fun y => uSeq j (ι y), hterms j⟩ : ThetaPshL1 β.form.val))
              atTop (@nhds (ThetaPshL1 β.form.val)
                (singularityPseudoMetricSpace omegaV β.form
                  (isBigClass_kahler β)).toUniformSpace.toTopologicalSpace
                ⟨τ, hτ⟩)

/-- In positive ambient dimension the same witnesses give exactly the
existing native-growth trace predicate. -/
theorem isSourceTraceRepresentativeAlong_iff_native (hn : n ≠ 0)
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (u : M → EReal) (τ : V → EReal) :
    IsSourceTraceRepresentativeAlong omega omegaV hι u τ ↔
      TraceRepresentativeConstruction.IsTraceRepresentativeAlong omega omegaV hι u τ := by
  unfold IsSourceTraceRepresentativeAlong
    TraceRepresentativeConstruction.IsTraceRepresentativeAlong
  rw [← nativeGeneric_zero_iff_source hn]

end

end SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
