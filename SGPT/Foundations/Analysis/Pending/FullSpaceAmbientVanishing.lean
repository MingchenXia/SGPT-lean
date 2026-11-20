import SGPT.Foundations.Analysis.Pending.DemaillyPaunAmbientVolume
import SGPT.Foundations.Analysis.Pending.FullSpaceAmbientDimZero

set_option autoImplicit false

/-!
# Vanishing of the ambient volume of a pseudoeffective non-big class

`Pending.NonBigVolumeReduction` splits the full-space non-big branch of the
numerical restricted volume into two independent inputs.  The first — the
comparison `acTopMass p ≤ perturbedDiagonalPotentialMass p` — is derived in
`Pending.FullSpaceAmbientComparison` from one named localization statement.
This module names the second one.

`tendsto_perturbedDiagonalPotentialEnvelope_nhds_zero` is the
Demailly--Păun/Boucksom volume theorem in the contrapositive form the reduction
consumes: along any sequence of errors tending to zero, the supremum of the
ambient diagonal non-pluripolar masses of the perturbed presentations — that is,
`vol(α + ε{ω})` — tends to `0` when `α` is pseudoeffective and not big.  It is a
genuine classical input: no order argument produces it, because the non-nef
branch of the definition is not implied by non-bigness (a nef non-big boundary
class has `E_nn(α) ≠ X`).

With it, `Pending.LocusProperties.numericalRestrictedVolume_eq_zero_of_not_isBigClass`
is fully assembled; see `iInf_restrictedMassEnvelope_eq_zero`.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.FullSpaceAmbientVanishing

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume
open NonBigVolumeReduction FullSpaceAmbientComparison
open DemaillyPaunAmbientVolume FullSpaceAmbientDimZero

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- **MISSING CLASSICAL INPUT (Demailly--Păun, Boucksom: positive volume produces
a Kähler current).**  For a pseudoeffective class that is not big, the ambient
diagonal non-pluripolar masses of the perturbed admissible presentations tend to
zero along every sequence of errors tending to zero. -/
theorem tendsto_perturbedDiagonalPotentialEnvelope_nhds_zero
    (omega : KahlerBackground n M) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (hcarrier : V.carrier = univ) (hdim : V.dim = n)
    (hpsef : ClassPseudoeffectiveViaPotentials alpha) (hnotbig : ¬ IsBigClass alpha)
    (errors : ℕ → PositiveError)
    (herrors : Tendsto (fun k => ((errors k : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun k => perturbedDiagonalPotentialEnvelope omega alpha V (errors k))
      atTop (𝓝 0) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact (hnotbig (FullSpaceAmbientDimZero.isBigClass_of_dim_zero hn omega alpha)).elim
  · exact DemaillyPaunAmbientVolume.tendsto_perturbedDiagonalPotentialEnvelope_nhds_zero_of_pos
      hn omega alpha V hcarrier hdim hpsef hnotbig errors herrors

/-- **The full-space restricted-mass infimum vanishes for a pseudoeffective
non-big class.**  Everything except the two named inputs is discharged: the
comparison with the ambient mass comes from
`FullSpaceAmbientComparison.acTopMass_le_perturbedDiagonalPotentialMass`, and the
order-theoretic assembly from `NonBigVolumeReduction`. -/
theorem iInf_restrictedMassEnvelope_eq_zero
    (omega : KahlerBackground n M) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (hcarrier : V.carrier = univ) (hdim : V.dim = n)
    (hpsef : ClassPseudoeffectiveViaPotentials alpha) (hnotbig : ¬ IsBigClass alpha)
    (errors : ℕ → PositiveError)
    (herrors : Tendsto (fun k => ((errors k : ℝ))) atTop (𝓝 0))
    (hreindex :
      (⨅ epsilon : PositiveError,
        restrictedMassEnvelope (acTopMassData omega) alpha V epsilon) =
      ⨅ k : ℕ, restrictedMassEnvelope (acTopMassData omega) alpha V (errors k)) :
    (⨅ epsilon : PositiveError,
      restrictedMassEnvelope (acTopMassData omega) alpha V epsilon) = 0 :=
  NonBigVolumeReduction.iInf_restrictedMassEnvelope_eq_zero_of_perturbedDiagonal_bounds
    omega alpha V errors hreindex
    (fun _ p => acTopMass_le_perturbedDiagonalPotentialMass hcarrier hdim p)
    (fun k => perturbedDiagonalPotentialEnvelope omega alpha V (errors k))
    (fun _ => le_rfl)
    (tendsto_perturbedDiagonalPotentialEnvelope_nhds_zero omega alpha V hcarrier hdim
      hpsef hnotbig errors herrors)

end SGPT.Foundations.Analysis.Pending.FullSpaceAmbientVanishing
