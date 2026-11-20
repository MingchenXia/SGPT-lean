import SGPT.Foundations.Analysis.Pending.AmbientMassBackgroundMonotone
import SGPT.Foundations.Analysis.Pending.DemaillyPaunAmbientClusterReduction
import SGPT.Foundations.Analysis.Pending.RestrictedMassEnvelopeMonotone

set_option autoImplicit false

/-!
# The perturbed ambient volume envelope is nondecreasing in the error

`NonBigVolumeReduction.perturbedDiagonalPotentialEnvelope omega alpha V ε` is the
supremum, over `ε`-admissible presentations of `alpha` along `V`, of the global
diagonal non-pluripolar mass of `θ + εω + ddᶜu`.  This file proves that it is
nondecreasing in `ε`, and draws the consequence that matters for the remaining
Demailly--Păun input.

Monotonicity has two ingredients, both already proved.
`AdmissibleRestrictedCurrentPresentation.raiseError` carries an `ε`-admissible
presentation to an `ε'`-admissible one for `ε ≤ ε'` with the same representative
and potential, and
`AmbientMassBackgroundMonotone.diagonalPotentialMass_le_add_smul` says the
diagonal non-pluripolar mass does not decrease when the background grows by a
semipositive form.  Since
`θ + ε'ω = (θ + εω) + (ε' - ε)ω` with `ω` semipositive, the two combine.

The consequence: a strictly positive *cluster* of the envelopes along some
vanishing error sequence is the same thing as a strictly positive bound valid at
*every* error.  So the residual classical statement can be taken in the
sequence-free form "the perturbed volumes of `alpha + ε{omega}` stay above a
fixed `η > 0` implies `alpha` is big", which is the textbook Demailly--Păun
statement.  Nothing here weakens or replaces
`DemaillyPaunAmbientVolume.isBigClass_of_hasPositiveAmbientMassCluster_of_pos`:
the residual implication stays an ordinary theorem hypothesis at its point of
use, exactly as in `DemaillyPaunAmbientClusterReduction`, so no new named
interface and no new `sorry` is introduced.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.PerturbedAmbientEnvelopeMonotone

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.NumericalRestrictedVolumeScaffold FirstPass.NumericalRestrictedVolume
open NonBigVolumeReduction FullSpaceAmbientMass DiagonalMass
open AmbientMassBackgroundMonotone DemaillyPaunAmbientClusterReduction

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [BorelSpace M] in
/-- The diagonal mass depends on the background only through its value. -/
theorem diagonalPotentialMass_congr_form {θ θ' : ClosedRealOneOneForm n M}
    (h : θ = θ') {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hu' : IsThetaPshPotential θ'.val u) :
    diagonalPotentialMass θ u hu = diagonalPotentialMass θ' u hu' := by
  subst h
  rfl

variable {omega : KahlerBackground n M} {alpha : RealBottChern n M}
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- **Raising the error does not decrease the ambient non-pluripolar mass of a
presentation.** -/
theorem perturbedDiagonalPotentialMass_le_raiseError {eps eps' : PositiveError}
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V eps)
    (h : (eps : ℝ) ≤ (eps' : ℝ)) :
    perturbedDiagonalPotentialMass p ≤ perturbedDiagonalPotentialMass (p.raiseError h) := by
  rcases eq_or_lt_of_le h with heq | hlt
  · have : eps = eps' := Subtype.ext heq
    subst this
    exact le_of_eq rfl
  · have hc : 0 < (eps' : ℝ) - (eps : ℝ) := sub_pos.mpr hlt
    have hform : (p.representative + (eps : ℝ) • omega.form) +
        ((eps' : ℝ) - (eps : ℝ)) • omega.form =
          p.representative + (eps' : ℝ) • omega.form := by
      rw [add_assoc, ← add_smul, add_sub_cancel]
    have hu' : IsThetaPshPotential
        ((p.representative + (eps : ℝ) • omega.form) +
          (((eps' : ℝ) - (eps : ℝ)) • omega.form)).val p.potential := by
      rw [hform]
      exact (p.raiseError h).potential_psh
    calc perturbedDiagonalPotentialMass p
        = diagonalPotentialMass (p.representative + (eps : ℝ) • omega.form)
            p.potential p.potential_psh := rfl
      _ ≤ diagonalPotentialMass ((p.representative + (eps : ℝ) • omega.form) +
            (((eps' : ℝ) - (eps : ℝ)) • omega.form)) p.potential hu' :=
          diagonalPotentialMass_le_add_smul omega.isSemipositive hc p.potential_psh hu'
      _ = diagonalPotentialMass (p.representative + (eps' : ℝ) • omega.form)
            p.potential (p.raiseError h).potential_psh :=
          diagonalPotentialMass_congr_form hform hu' (p.raiseError h).potential_psh

/-- **The perturbed ambient volume envelope is nondecreasing in the error.** -/
theorem perturbedDiagonalPotentialEnvelope_mono (omega : KahlerBackground n M)
    (alpha : RealBottChern n M) (V : ClosedIrreducibleAnalyticSubvariety n M)
    {eps eps' : PositiveError} (h : (eps : ℝ) ≤ (eps' : ℝ)) :
    perturbedDiagonalPotentialEnvelope omega alpha V eps ≤
      perturbedDiagonalPotentialEnvelope omega alpha V eps' := by
  unfold perturbedDiagonalPotentialEnvelope ambientMassEnvelope
  refine iSup_le fun p => ?_
  exact (perturbedDiagonalPotentialMass_le_raiseError p h).trans
    (le_iSup (fun q => perturbedDiagonalPotentialMass q) (p.raiseError h))

/-- The sequence-free positive lower bound: the perturbed ambient volumes stay
above `eta` at **every** error.  By monotonicity this is no stronger than the
same bound at arbitrarily small errors. -/
def HasUniformAmbientMassLowerBound (omega : KahlerBackground n M)
    (alpha : RealBottChern n M) (V : ClosedIrreducibleAnalyticSubvariety n M)
    (eta : ℝ≥0∞) : Prop :=
  ∀ epsilon : PositiveError,
    eta < perturbedDiagonalPotentialEnvelope omega alpha V epsilon

/-- **A positive cluster along a vanishing error sequence is a positive bound at
every error.**  This is where monotonicity is used: the cluster only supplies
the bound at *some* arbitrarily small errors, and monotonicity propagates it
upward.  No analytic input. -/
theorem exists_hasUniformAmbientMassLowerBound_of_hasPositiveAmbientMassCluster
    (omega : KahlerBackground n M) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M) (errors : ℕ → PositiveError)
    (herrors : Tendsto (fun k => ((errors k : ℝ))) atTop (𝓝 0))
    (hcluster : HasPositiveAmbientMassCluster omega alpha V errors) :
    ∃ eta : ℝ≥0∞, 0 < eta ∧ HasUniformAmbientMassLowerBound omega alpha V eta := by
  obtain ⟨eta, heta, htail⟩ := hcluster
  refine ⟨eta, heta, fun epsilon => ?_⟩
  have hev : ∀ᶠ k in atTop, ((errors k : ℝ)) < (epsilon : ℝ) := by
    have := herrors.eventually (eventually_lt_nhds epsilon.2)
    simpa using this
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  obtain ⟨k, hkN, hk⟩ := htail N
  exact hk.trans_le
    (perturbedDiagonalPotentialEnvelope_mono omega alpha V (hN k hkN).le)

/-- **Reduction of the remaining Demailly--Păun input to its sequence-free
form.**  To conclude that `alpha` is big from a positive cluster along a
vanishing error sequence it is enough to prove the classical theorem in the
uniform form.  The implication is an ordinary hypothesis, not a structure field
or a new interface. -/
theorem isBigClass_of_hasPositiveAmbientMassCluster_of_uniform
    (omega : KahlerBackground n M) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M) (errors : ℕ → PositiveError)
    (herrors : Tendsto (fun k => ((errors k : ℝ))) atTop (𝓝 0))
    (hcluster : HasPositiveAmbientMassCluster omega alpha V errors)
    (huniform : ∀ eta : ℝ≥0∞, 0 < eta →
      HasUniformAmbientMassLowerBound omega alpha V eta → IsBigClass alpha) :
    IsBigClass alpha := by
  obtain ⟨eta, heta, hbound⟩ :=
    exists_hasUniformAmbientMassLowerBound_of_hasPositiveAmbientMassCluster
      omega alpha V errors herrors hcluster
  exact huniform eta heta hbound

end

end SGPT.Foundations.Analysis.Pending.PerturbedAmbientEnvelopeMonotone
