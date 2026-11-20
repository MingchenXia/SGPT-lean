import SGPT.Foundations.Analysis.Pending.FullSpaceAmbientComparison

set_option autoImplicit false

/-!
# The exact Demailly--Păun residual: positive ambient-mass clusters

The remaining positive-dimensional Demailly--Păun input in
`Pending.DemaillyPaunAmbientVolume` is a convergence statement for the supremal
ambient non-pluripolar masses of the perturbed classes.  This file proves the
order/topology reduction which identifies its genuinely geometric residue.

For a fixed sequence of positive errors tending to zero, failure of convergence
of the ambient envelope to `0` is exactly the existence of a strictly positive
ambient-mass cluster along a cofinal subsequence.  Consequently, to prove the
Demailly--Păun conclusion it is enough to prove the contrapositive geometric
statement

```
positive ambient-mass cluster as ε → 0  ⟹  α is big.
```

No analytic assertion is placed in a structure field here.  The two directions
between the cluster formulation and the original `Tendsto` statement are proved
using the order topology of `ℝ≥0∞`; the residual implication is an ordinary
theorem hypothesis at its point of use.  Thus it records precisely the
remaining classical theorem, rather than strengthening it to a uniform estimate
or silently assuming a volume formula.
-/

open Filter Set
open scoped Topology ENNReal

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.DemaillyPaunAmbientClusterReduction

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume
open NonBigVolumeReduction FullSpaceAmbientMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- A strictly positive cluster of the ambient envelopes along a prescribed
error sequence.  The quantifier `∀ N, ∃ k ≥ N` is deliberately explicit: it
says that the lower mass bound occurs arbitrarily far out, with no monotonicity
assumption on the chosen errors or on the envelopes. -/
def HasPositiveAmbientMassCluster
    (omega : KahlerBackground n M) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (errors : ℕ → PositiveError) : Prop :=
  ∃ eta : ℝ≥0∞, 0 < eta ∧
    ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧
      eta < perturbedDiagonalPotentialEnvelope omega alpha V (errors k)

omit [BorelSpace M] in
/-- A positive ambient-mass cluster is incompatible with convergence of the
ambient envelopes to zero. -/
theorem not_tendsto_perturbedDiagonalPotentialEnvelope_of_hasPositiveAmbientMassCluster
    (omega : KahlerBackground n M) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (errors : ℕ → PositiveError)
    (hcluster : HasPositiveAmbientMassCluster omega alpha V errors) :
    ¬ Tendsto (fun k => perturbedDiagonalPotentialEnvelope omega alpha V (errors k))
      atTop (𝓝 0) := by
  rintro hlimit
  obtain ⟨eta, heta, htail⟩ := hcluster
  rw [ENNReal.tendsto_atTop_zero] at hlimit
  obtain ⟨N, hN⟩ := hlimit eta heta
  obtain ⟨k, hkN, hk⟩ := htail N
  exact (not_lt_of_ge (hN k hkN)) hk

omit [BorelSpace M] in
/-- If the ambient envelopes do not converge to zero, then they have a strictly
positive cluster.  This is the complete order-theoretic converse; it does not
use pseudoeffectivity, compactness, or any regularity of the potentials. -/
theorem hasPositiveAmbientMassCluster_of_not_tendsto_perturbedDiagonalPotentialEnvelope
    (omega : KahlerBackground n M) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (errors : ℕ → PositiveError)
    (hlimit : ¬ Tendsto
      (fun k => perturbedDiagonalPotentialEnvelope omega alpha V (errors k))
      atTop (𝓝 0)) :
    HasPositiveAmbientMassCluster omega alpha V errors := by
  rw [ENNReal.tendsto_atTop_zero] at hlimit
  push Not at hlimit
  obtain ⟨eta, heta, htail⟩ := hlimit
  refine ⟨eta, heta, ?_⟩
  intro N
  obtain ⟨k, hkN, hk⟩ := htail N
  exact ⟨k, hkN, hk⟩

omit [BorelSpace M] in
/-- The ambient-envelope convergence statement is equivalent to the absence of
positive mass clusters. -/
theorem tendsto_perturbedDiagonalPotentialEnvelope_nhds_zero_iff_no_positiveAmbientMassCluster
    (omega : KahlerBackground n M) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (errors : ℕ → PositiveError) :
    Tendsto (fun k => perturbedDiagonalPotentialEnvelope omega alpha V (errors k))
      atTop (𝓝 0) ↔
      ¬ HasPositiveAmbientMassCluster omega alpha V errors := by
  constructor
  · intro hlimit hcluster
    exact not_tendsto_perturbedDiagonalPotentialEnvelope_of_hasPositiveAmbientMassCluster
      omega alpha V errors hcluster hlimit
  · intro hnocluster
    by_contra hlimit
    exact hnocluster
      (hasPositiveAmbientMassCluster_of_not_tendsto_perturbedDiagonalPotentialEnvelope
        omega alpha V errors hlimit)

omit [BorelSpace M] in
/-- **Demailly--Păun reduction.**  Once the geometric positive-cluster
criterion is available for the chosen error sequence, non-bigness forces the
ambient envelope to converge to zero.  The criterion has exactly the classical
content remaining after the present project-local order and measure reductions:
a positive limiting non-pluripolar volume of `α + ε{ω}` produces a Kähler
current in `α`.

The geometric theorem which establishes the supplied implication will use
positive dimension, pseudoeffectivity, full-space data, and a vanishing error
sequence.  The purely formal reduction itself needs only the implication and
the non-bigness contradiction, so it does not introduce irrelevant hypotheses.
-/
theorem tendsto_perturbedDiagonalPotentialEnvelope_nhds_zero_of_positiveAmbientMassCluster_big
    (omega : KahlerBackground n M) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (errors : ℕ → PositiveError) (hnotbig : ¬ IsBigClass alpha)
    (hpositiveCluster_big :
      HasPositiveAmbientMassCluster omega alpha V errors → IsBigClass alpha) :
    Tendsto (fun k => perturbedDiagonalPotentialEnvelope omega alpha V (errors k))
      atTop (𝓝 0) := by
  rw [tendsto_perturbedDiagonalPotentialEnvelope_nhds_zero_iff_no_positiveAmbientMassCluster]
  intro hcluster
  exact hnotbig (hpositiveCluster_big hcluster)

end SGPT.Foundations.Analysis.Pending.DemaillyPaunAmbientClusterReduction
