import SGPT.Foundations.Analysis.Pending.FullSpaceAmbientMass

/-!
# Order-theoretic reduction for the non-big ambient-volume branch

For the full-space branch of numerical restricted volume, the outstanding
analytic statement has two logically separate parts.

1. For every admissible presentation, identify (or bound) its restricted
   absolutely-continuous mass by the global diagonal non-pluripolar mass of
   the perturbed potential.  This is a local density and countable-chart-cover
   theorem; it is **not** supplied here.
2. Bound the resulting ambient envelopes along a cofinal sequence of positive
   errors by quantities tending to zero.  The geometric source of that bound
   is the Demailly--Păun/Boucksom volume theorem: positive limiting volume
   produces a Kähler current.  This file does **not** package either direction
   of that theorem as an assumption or a structure field.

Once those two inputs are available, the conclusion is pure order theory.  In
particular, no false implication `not big -> non-nef locus = univ` is used.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.NonBigVolumeReduction

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolume
  FirstPass.NumericalRestrictedVolumeScaffold FullSpaceAmbientMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The supremal full-space mass associated to an arbitrary assignment of a
mass to each admissible presentation.  `restrictedMassEnvelope` is the special
case in which the assigned mass is `acTopMass`. -/
def ambientMassEnvelope (omega : KahlerBackground n M)
    (ambientMass : ∀ {alpha : RealBottChern n M}
      {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError},
      AdmissibleRestrictedCurrentPresentation omega alpha V epsilon → ℝ≥0∞)
    (alpha : RealBottChern n M) (V : ClosedIrreducibleAnalyticSubvariety n M)
    (epsilon : PositiveError) : ℝ≥0∞ :=
  ⨆ p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon, ambientMass p

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- A pointwise comparison of masses promotes to the corresponding envelope
comparison.  For the intended diagonal mass, proving the premise requires the
missing full-space identification of `acTopMass` with the non-pluripolar mass;
this theorem merely performs the valid supremum step. -/
theorem restrictedMassEnvelope_le_ambientMassEnvelope
    (omega : KahlerBackground n M) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M) (epsilon : PositiveError)
    (ambientMass : ∀ {alpha : RealBottChern n M}
      {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError},
      AdmissibleRestrictedCurrentPresentation omega alpha V epsilon → ℝ≥0∞)
    (hcomparison : ∀ p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon,
      acTopMass p ≤ ambientMass p) :
    restrictedMassEnvelope (acTopMassData omega) alpha V epsilon ≤
      ambientMassEnvelope omega ambientMass alpha V epsilon := by
  unfold restrictedMassEnvelope acTopMassData ambientMassEnvelope
  refine iSup_le fun p => ?_
  exact (hcomparison p).trans (le_iSup (fun q => ambientMass q) p)

/-- The intended ambient envelope, formed from the project's actual diagonal
non-pluripolar mass of `theta + epsilon * omega + dd^c u`. -/
def perturbedDiagonalPotentialEnvelope
    (omega : KahlerBackground n M) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M) (epsilon : PositiveError) : ℝ≥0∞ :=
  ambientMassEnvelope omega (fun p => perturbedDiagonalPotentialMass p) alpha V epsilon

omit [BorelSpace M] in
/-- The envelope comparison specialized to the actual diagonal mass.  Its
premise is deliberately an ordinary theorem hypothesis, rather than a field
of a new axiom: the forthcoming local pole-complement density proof should
establish it. -/
theorem restrictedMassEnvelope_le_perturbedDiagonalPotentialEnvelope
    (omega : KahlerBackground n M) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M) (epsilon : PositiveError)
    (hcomparison : ∀ p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon,
      acTopMass p ≤ perturbedDiagonalPotentialMass p) :
    restrictedMassEnvelope (acTopMassData omega) alpha V epsilon ≤
      perturbedDiagonalPotentialEnvelope omega alpha V epsilon :=
  restrictedMassEnvelope_le_ambientMassEnvelope omega alpha V epsilon
    (fun p => perturbedDiagonalPotentialMass p) hcomparison

/-- A sequence which is bounded above by a sequence converging to zero has
zero infimum.  The proof uses the closed order topology of `ENNReal`, so it
also handles a priori infinite intermediate masses. -/
theorem iInf_eq_zero_of_le_tendsto_zero (f bound : ℕ → ℝ≥0∞)
    (hbound : ∀ k, f k ≤ bound k) (hlimit : Tendsto bound atTop (𝓝 0)) :
    (⨅ k, f k) = 0 := by
  apply bot_unique
  refine le_of_tendsto_of_tendsto tendsto_const_nhds hlimit ?_
  exact Eventually.of_forall fun k => (iInf_le f k).trans (hbound k)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Pure reduction from a local mass comparison and ambient envelope bounds to
vanishing of the full-space restricted-mass infimum along any specified
cofinal error sequence.  The equality `hreindex` is the separate cofinality
argument (for the manuscript's reciprocal errors it is already proved in
`LocusProperties`). -/
theorem iInf_restrictedMassEnvelope_eq_zero_of_ambient_bounds
    (omega : KahlerBackground n M) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (ambientMass : ∀ {alpha : RealBottChern n M}
      {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError},
      AdmissibleRestrictedCurrentPresentation omega alpha V epsilon → ℝ≥0∞)
    (errors : ℕ → PositiveError)
    (hreindex :
      (⨅ epsilon : PositiveError,
        restrictedMassEnvelope (acTopMassData omega) alpha V epsilon) =
      ⨅ k : ℕ,
        restrictedMassEnvelope (acTopMassData omega) alpha V (errors k))
    (hcomparison : ∀ k
      (p : AdmissibleRestrictedCurrentPresentation omega alpha V (errors k)),
      acTopMass p ≤ ambientMass p)
    (bound : ℕ → ℝ≥0∞)
    (hambient : ∀ k,
      ambientMassEnvelope omega ambientMass alpha V (errors k) ≤ bound k)
    (hlimit : Tendsto bound atTop (𝓝 0)) :
    (⨅ epsilon : PositiveError,
      restrictedMassEnvelope (acTopMassData omega) alpha V epsilon) = 0 := by
  rw [hreindex]
  apply iInf_eq_zero_of_le_tendsto_zero
  intro k
  exact (restrictedMassEnvelope_le_ambientMassEnvelope omega alpha V (errors k)
    ambientMass (hcomparison k)).trans (hambient k)
  exact hlimit

omit [BorelSpace M] in
/-- The same reduction expressed with the actual perturbed diagonal mass.  To
apply it to a pseudoeffective non-big class, the caller must prove `hambient`
from the Demailly--Păun volume-positivity contrapositive.  No implication from
`not IsBigClass alpha` is assumed in this statement. -/
theorem iInf_restrictedMassEnvelope_eq_zero_of_perturbedDiagonal_bounds
    (omega : KahlerBackground n M) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M) (errors : ℕ → PositiveError)
    (hreindex :
      (⨅ epsilon : PositiveError,
        restrictedMassEnvelope (acTopMassData omega) alpha V epsilon) =
      ⨅ k : ℕ,
        restrictedMassEnvelope (acTopMassData omega) alpha V (errors k))
    (hcomparison : ∀ k
      (p : AdmissibleRestrictedCurrentPresentation omega alpha V (errors k)),
      acTopMass p ≤ perturbedDiagonalPotentialMass p)
    (bound : ℕ → ℝ≥0∞)
    (hambient : ∀ k,
      perturbedDiagonalPotentialEnvelope omega alpha V (errors k) ≤ bound k)
    (hlimit : Tendsto bound atTop (𝓝 0)) :
    (⨅ epsilon : PositiveError,
      restrictedMassEnvelope (acTopMassData omega) alpha V epsilon) = 0 :=
  iInf_restrictedMassEnvelope_eq_zero_of_ambient_bounds omega alpha V
    (fun p => perturbedDiagonalPotentialMass p) errors hreindex hcomparison bound hambient hlimit

end

end SGPT.Foundations.Analysis.Pending.NonBigVolumeReduction
