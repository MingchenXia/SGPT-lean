import SGPT.Foundations.Analysis.Pending.DemaillyPaunAmbientClusterReduction
import SGPT.Foundations.Analysis.Pending.UniformAmbientVolumeBignessInterface

set_option autoImplicit false

/-!
# Positive-dimensional Demailly--Păun ambient-volume input

This is the sole external analytic input in the full-space non-big branch.
It is deliberately restricted to positive complex dimension.  The omitted
zero-dimensional branch is proved in `FullSpaceAmbientDimZero`: there every
Bott--Chern class is big, so the non-big hypotheses are contradictory.

Mathematically, the remaining source fact is the Demailly--Păun/Boucksom
positive-volume-implies-bigness implication, in the presentation-level
normalization used here: a strictly positive cofinal cluster of supremal ambient
non-pluripolar masses of `alpha + epsilon {omega}` as `epsilon` tends to zero
produces a Kähler current in `alpha`.  The project-local order/topology
reduction in `DemaillyPaunAmbientClusterReduction` proves that this is exactly
what is needed for the downstream ambient-envelope convergence statement.

Nothing here is a `sorry` any more.  The error sequence and its cofinal cluster
are removed by the monotonicity of the ambient envelope, proved in
`Pending.PerturbedAmbientEnvelopeMonotone`, and the residue is the sequence-free
literature statement isolated in
`Pending.UniformAmbientVolumeBignessInterface`:
`v(alpha + epsilon {omega}) > eta > 0` for every `epsilon` implies `alpha` big
(`bou02-volume:page-0014` and `bou02-volume:4.8`).
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.DemaillyPaunAmbientVolume

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume
open NonBigVolumeReduction
open DemaillyPaunAmbientClusterReduction
open PerturbedAmbientEnvelopeMonotone UniformAmbientVolumeBigness

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- **External classical input (Demailly--Păun; Boucksom).**  In positive
complex dimension, a pseudoeffective class whose perturbed full-space
ambient-volume envelopes retain a strictly positive cofinal cluster as the
error tends to zero is big.  This is the direct positive-volume-implies-bigness
form of the classical theorem.  The zero-dimensional case is proved separately,
rather than silently included in this interface. -/
theorem isBigClass_of_hasPositiveAmbientMassCluster_of_pos
    (hn : 0 < n) (omega : KahlerBackground n M) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (hcarrier : V.carrier = univ)
    (hpsef : ClassPseudoeffectiveViaPotentials alpha)
    (errors : ℕ → PositiveError)
    (herrors : Tendsto (fun k => ((errors k : ℝ))) atTop (𝓝 0))
    (hcluster : HasPositiveAmbientMassCluster omega alpha V errors) :
    IsBigClass alpha :=
  isBigClass_of_hasPositiveAmbientMassCluster_of_uniform omega alpha V errors herrors hcluster
    fun eta heta hbound =>
      isBigClass_of_hasUniformAmbientMassLowerBound hn omega alpha V hcarrier hpsef eta heta hbound

/-- In positive complex dimension, the exact external positive-cluster
criterion implies the ambient-envelope convergence statement consumed by the
full-space volume reduction. -/
theorem tendsto_perturbedDiagonalPotentialEnvelope_nhds_zero_of_pos
    (hn : 0 < n) (omega : KahlerBackground n M) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (hcarrier : V.carrier = univ) (_hdim : V.dim = n)
    (hpsef : ClassPseudoeffectiveViaPotentials alpha) (hnotbig : ¬ IsBigClass alpha)
    (errors : ℕ → PositiveError)
    (herrors : Tendsto (fun k => ((errors k : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun k => perturbedDiagonalPotentialEnvelope omega alpha V (errors k))
      atTop (𝓝 0) := by
  apply tendsto_perturbedDiagonalPotentialEnvelope_nhds_zero_of_positiveAmbientMassCluster_big
    omega alpha V errors hnotbig
  intro hcluster
  exact isBigClass_of_hasPositiveAmbientMassCluster_of_pos hn omega alpha V hcarrier
    hpsef errors herrors hcluster

end SGPT.Foundations.Analysis.Pending.DemaillyPaunAmbientVolume
