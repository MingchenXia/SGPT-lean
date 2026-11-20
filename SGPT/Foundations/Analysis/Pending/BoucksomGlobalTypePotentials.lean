import SGPT.Foundations.Analysis.Pending.PerturbedAmbientEnvelopeMonotone
import SGPT.Foundations.Analysis.Pending.PotentialMassComparison
import SGPT.Foundations.Analysis.Pending.DemaillyApproximationSmoothOffPole
import SGPT.Foundations.Analysis.Pending.GlobalMeasureInvariance

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Potentials of global analytic type carrying the mass (Boucksom 4.8, first step)

Source: Boucksom, proof of Theorem 4.8 (`bou02-volume:4.8`, with Demailly's approximation
`bou02-volume:2.6`); blueprint `bou:global-type-potentials`.  TN.4 plan, step B6.

The named input `UniformAmbientVolumeBigness.isBigClass_of_hasUniformAmbientMassLowerBound`
assumes `HasUniformAmbientMassLowerBound ω α V η`: at every error `ε > 0` some
`ε`-admissible presentation of `α` has ambient non-pluripolar mass `> η`.  The presentations
have *local* analytic singularities (the bounded-remainder convention, exponents and remainders varying
from chart to chart), while the resolution step of Boucksom's proof needs one rational exponent
and one coherent ideal.  This module supplies them, for a FIXED smooth representative `θ` of `α`:

* `exists_globalTypePotential`: for every `ε > 0` there is a `(θ + 2εω)`-psh potential `ψ` with
  analytic singularities of global type `(c, 𝔞)` (`c ∈ ℚ_{>0}`, `𝔞` coherent, bounded
  remainders: `GlobalAnalyticSingularities.HasAnalyticSingularities`), also smooth off its poles
  in the bounded-remainder convention, with `∫(θ + 2εω)_ψⁿ > η`.

Proof (`bou:global-type-potentials`): take a presentation `(θ_p, u)` of mass `> η`; as
`{θ_p} = {θ}`, `θ = θ_p + dd^c h` with `h` smooth, so `u - h` is `(θ + εω)`-psh with the same
non-pluripolar measure (`GlobalMeasureInvariance.globalMixedMeasure_changeRepresentative`);
Demailly's approximation of `u - h` (proved:
`DemaillyApproximationSmoothOffPole.exists_algebraicApproximation`) gives `ψ ≥ u - h` of global
analytic type which is `(θ + εω + δω)`-psh with `δ < ε`, hence `(θ + 2εω)`-psh, and
`∫(θ + 2εω)_ψⁿ ≥ ∫(θ + εω)_{u-h}ⁿ > η` (`PotentialMassComparison.diagonalPotentialMass_le_of_le_add_smul`:
background and singularity monotonicity of the mass).  Neither Yau's theorem nor any resolution
of singularities is used.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.BoucksomGlobalTypePotentials

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.GlobalAnalyticSingularities NonBigVolumeReduction FullSpaceAmbientMass DiagonalMass
  PerturbedAmbientEnvelopeMonotone

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- **Changing the representative of the class of a presentation.**  If `θ` represents the
class of the presentation `p`, then `θ + εω` carries a potential (`p.potential - h`, with
`θ = θ_p + dd^c h`) whose non-pluripolar mass is that of `p`. -/
theorem exists_potential_of_presentation (omega : KahlerBackground n M)
    {alpha : RealBottChern n M} {V : ClosedIrreducibleAnalyticSubvariety n M}
    {ε : PositiveError} (p : AdmissibleRestrictedCurrentPresentation omega alpha V ε)
    (θ : ClosedRealOneOneForm n M) (hθ : RealBottChern.ofRepresentative θ = alpha) :
    ∃ (u : M → EReal) (hu : IsThetaPshPotential (θ + (ε : ℝ) • omega.form).val u),
      diagonalPotentialMass (θ + (ε : ℝ) • omega.form) u hu = perturbedDiagonalPotentialMass p := by
  obtain ⟨h, hh, hθp⟩ := (RealBottChern.ofRepresentative_eq_iff p.representative θ).mp
    (p.represents.trans hθ.symm)
  have hθη : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      (θ + (ε : ℝ) • omega.form).val.coeff e z =
        (p.representative + (ε : ℝ) • omega.form).val.coeff e z +
          smoothDDC (fun y => h (e.val.symm y)) z := by
    intro e z hz
    rw [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_add, hθp e z hz]
    abel
  have hu : IsThetaPshPotential (θ + (ε : ℝ) • omega.form).val
      (fun x => p.potential x - (h x : EReal)) :=
    thetaPshPotential_sub_smooth hh hθη p.potential_psh
  refine ⟨_, hu, ?_⟩
  have hinv := GlobalMeasureInvariance.globalMixedMeasure_changeRepresentative
    (θ := fun _ : Fin n => p.representative + (ε : ℝ) • omega.form)
    (η := fun _ : Fin n => θ + (ε : ℝ) • omega.form)
    (u := fun _ : Fin n => p.potential) (f := fun _ : Fin n => h) (fun _ => hh)
    (fun _ => hθη) (fun _ => p.potential_psh.1)
  exact congrArg (fun μ : Measure M => μ univ) hinv

/-- **Potentials of global analytic type carrying the mass** (`bou:global-type-potentials`).
Under the hypothesis of Boucksom's criterion, for every smooth representative `θ` of `α` and
every `ε > 0` there is a `(θ + 2εω)`-psh potential with analytic singularities of global type
`(c, 𝔞)` (`c ∈ ℚ_{>0}`, `𝔞` coherent, bounded remainders), smooth off its poles, whose
non-pluripolar mass exceeds `η`. -/
theorem exists_globalTypePotential (omega : KahlerBackground n M) {alpha : RealBottChern n M}
    {V : ClosedIrreducibleAnalyticSubvariety n M} {eta : ℝ≥0∞}
    (hbound : HasUniformAmbientMassLowerBound omega alpha V eta)
    (θ : ClosedRealOneOneForm n M) (hθ : RealBottChern.ofRepresentative θ = alpha)
    (ε : PositiveError) :
    ∃ (ψ : M → EReal) (hψ : IsThetaPshPotential (θ + (2 * (ε : ℝ)) • omega.form).val ψ),
      HasAnalyticSingularities (n := n) ψ ∧
        HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) ψ ∧
          eta < diagonalPotentialMass (θ + (2 * (ε : ℝ)) • omega.form) ψ hψ := by
  -- a presentation of mass `> η`
  have hlt := hbound ε
  unfold perturbedDiagonalPotentialEnvelope ambientMassEnvelope at hlt
  obtain ⟨p, hp⟩ := lt_iSup_iff.mp hlt
  -- move it to the representative `θ`
  obtain ⟨u, hu, hmass⟩ := exists_potential_of_presentation omega p θ hθ
  -- Demailly's approximation of `u`, with error `< ε`
  obtain ⟨ψs, δ, hglob, hsop, -, hinf, -, hδ, hψs⟩ :=
    DemaillyApproximationSmoothOffPole.exists_algebraicApproximation omega
      (θ + (ε : ℝ) • omega.form) u hu
  obtain ⟨j, hj⟩ : ∃ j, δ j < (ε : ℝ) := (hδ.eventually (gt_mem_nhds ε.2)).exists
  have hle : u ≤ ψs j := fun x => by
    rw [← hinf x]
    exact iInf_le (fun i => ψs i x) j
  have hpsh : IsThetaPshPotential (θ + (ε : ℝ) • omega.form + (ε : ℝ) • omega.form).val
      (ψs j) := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive (hψs j)
      (KahlerDomination.isSemipositive_smul omega.isSemipositive (sub_nonneg.2 hj.le))
    rwa [show θ + (ε : ℝ) • omega.form + δ j • omega.form + ((ε : ℝ) - δ j) • omega.form =
      θ + (ε : ℝ) • omega.form + (ε : ℝ) • omega.form by module] at h
  have hform : θ + (ε : ℝ) • omega.form + (ε : ℝ) • omega.form =
      θ + (2 * (ε : ℝ)) • omega.form := by module
  have hpsh' : IsThetaPshPotential (θ + (2 * (ε : ℝ)) • omega.form).val (ψs j) := hform ▸ hpsh
  refine ⟨ψs j, hpsh', hglob j, hsop j, ?_⟩
  calc eta < perturbedDiagonalPotentialMass p := hp
    _ = diagonalPotentialMass (θ + (ε : ℝ) • omega.form) u hu := hmass.symm
    _ ≤ diagonalPotentialMass (θ + (ε : ℝ) • omega.form + (ε : ℝ) • omega.form) (ψs j) hpsh :=
        PotentialMassComparison.diagonalPotentialMass_le_of_le_add_smul omega ε.2 hu hpsh hle
    _ = diagonalPotentialMass (θ + (2 * (ε : ℝ)) • omega.form) (ψs j) hpsh' :=
        diagonalPotentialMass_congr_form hform hpsh hpsh'

end

end SGPT.Foundations.Analysis.Pending.BoucksomGlobalTypePotentials
