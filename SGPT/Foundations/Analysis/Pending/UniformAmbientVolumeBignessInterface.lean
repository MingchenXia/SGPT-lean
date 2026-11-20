import SGPT.Foundations.Analysis.Pending.PerturbedAmbientEnvelopeMonotone
import SGPT.Foundations.Analysis.Pending.UniformNefCore
import SGPT.Foundations.Analysis.Pending.BoucksomResolutionStep

set_option autoImplicit false

/-!
# Positive perturbed volume produces a Kähler current (formerly a named input; PROVED)

This is the sequence-free form of the last classical input in the full-space
non-big branch.  `Pending.DemaillyPaunAmbientVolume` used to state it along a
prescribed vanishing error sequence, with the sequence, the cofinal cluster and
the ambient envelope all visible in the hypothesis.  None of that is part of the
classical theorem.

`Pending.PerturbedAmbientEnvelopeMonotone` removes it: the ambient envelope
`epsilon ↦ perturbedDiagonalPotentialEnvelope omega alpha V epsilon` is
nondecreasing, so a strictly positive cluster along *some* vanishing sequence is
the same thing as a strictly positive bound at *every* error
(`exists_hasUniformAmbientMassLowerBound_of_hasPositiveAmbientMassCluster`).
That reduction is proved; it is the proved half of the split recorded here, and
it is what makes the present statement a narrowing rather than a restatement of
its consumer.

What is left is exactly the literature statement.  Writing `v` for the volume of
a pseudoeffective class (`bou02-volume:1.3`), Boucksom's Grauert--Riemenschneider
criterion (`bou02-volume:4.8`, published as Theorem 4.7) says that a
pseudoeffective `(1,1)`-class on a compact Kähler manifold is big — that is,
contains a Kähler current — exactly when `v(alpha) > 0`; and the volume sandwich
`v(alpha) ≤ lim_{epsilon → 0} v(alpha + epsilon {omega}) ≤ v(alpha)` of
`bou02-volume:page-0014` (published Proposition 4.5, in the upper-semicontinuity
form `v(alpha) ≥ limsup_k v(alpha_k)`) turns a lower bound valid at every
`epsilon > 0` into a lower bound on `v(alpha)` itself.  The arXiv restatement
numbered 4.7 is NOT the same statement; `locators.tsv` records the discrepancy.  The hypothesis below is stronger than
`v(alpha + epsilon {omega}) > eta`, because the ambient envelope is a supremum
over `epsilon`-admissible presentations only, so the classical theorem applies a
fortiori.

The zero-dimensional case is not covered here and is not needed: it is proved
outright in `Pending.FullSpaceAmbientDimZero`, where every class is big.

PROVED (TN.4 #1, human decisions I-0902 items 3 and 4): the `sorry` is discharged in place by
Boucksom's proof of 4.8, `BoucksomResolutionAssembly.isBigClass_of_resolutionStep_of_uniformNefCore`,
with the resolution step `BoucksomResolutionStep.resolutionStep` (which uses
`RelativePrincipalization.exists_factorizationData` as given, F2 = (B); since proved in place) and the uniform nef core
`UniformNefCore.uniformNefCore_of_pos` (Boucksom 4.10 on `Y × X` along the graph of the blowup; it uses
Yau's theorem `YauTheorem.exists_kahler_mongeAmpere_eq_exp`, once a TEMPORARY named input, since proved
in place by the continuity method).  The manifold
is connected because the irreducible subvariety `V` is all of `M` (`hcarrier`).  The statement is
unchanged; the proof does not use `hpsef` (pseudoeffectivity is implied by the uniform lower bound).
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.UniformAmbientVolumeBigness

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume
open NonBigVolumeReduction PerturbedAmbientEnvelopeMonotone

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

-- The hypothesis `hpsef` turns out to be redundant: Boucksom's proof only uses the uniform lower
-- bound `hbound`.  It is part of an existing statement, so it is kept and the unused-binder linter
-- is switched off here rather than the signature being changed (precedent 19231ce1).
set_option linter.unusedVariables false in
/-- **Boucksom's Grauert--Riemenschneider criterion** (`bou02-volume:4.8`, together with the volume
sandwich `bou02-volume:page-0014`; formerly an external classical input, now PROVED, using
`RelativePrincipalization.exists_factorizationData` and Yau's theorem, both since proved in place).  In
positive complex dimension, a pseudoeffective class whose perturbed full-space
ambient volumes stay above a fixed `eta > 0` at **every** error is big.  No error
sequence and no cluster occurs: the reduction from the sequential form is proved
in `Pending.PerturbedAmbientEnvelopeMonotone`. -/
theorem isBigClass_of_hasUniformAmbientMassLowerBound
    (hn : 0 < n) (omega : KahlerBackground n M) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (hcarrier : V.carrier = univ)
    (hpsef : ClassPseudoeffectiveViaPotentials alpha)
    (eta : ℝ≥0∞) (heta : 0 < eta)
    (hbound : HasUniformAmbientMassLowerBound omega alpha V eta) :
    IsBigClass alpha := by
  have : ConnectedSpace M := UniformNefCore.connectedSpace_of_isComplexAnalyticallyIrreducible_univ
    (hcarrier ▸ V.irreducible_carrier)
  exact BoucksomResolutionAssembly.isBigClass_of_resolutionStep_of_uniformNefCore omega alpha V eta
    heta hbound (BoucksomResolutionStep.resolutionStep hn omega)
    (UniformNefCore.uniformNefCore_of_pos hn omega)

end

end SGPT.Foundations.Analysis.Pending.UniformAmbientVolumeBigness
