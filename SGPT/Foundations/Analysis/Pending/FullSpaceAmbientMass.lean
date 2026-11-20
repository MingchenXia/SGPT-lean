import SGPT.Foundations.Analysis.Pending.GlobalDiagonalScaling
import SGPT.Foundations.Analysis.Pending.DiagonalMass
import SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolume

set_option autoImplicit false

/-!
# Ambient non-pluripolar mass of an admissible restricted presentation

For an admissible presentation at error `ε`, the perturbed form
`θ + εω + ddᶜu` is a genuine global theta-PSH potential.  This module attaches
to it the project's actual diagonal non-pluripolar mass and proves its two
basic measure-theoretic properties: it is finite on a compact Kähler manifold
and it charges none of the pole set.

This does **not** identify this ambient mass with `acTopMass p`: that equality
on the full space requires the still-missing local comparison between the
Bedford--Taylor truncation measure and the smooth top-degree density away from
the analytic poles.  Separating the two quantities avoids silently replacing
the CT22 absolutely-continuous mass by a different non-pluripolar product.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.FullSpaceAmbientMass

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume DiagonalMass MixedMass GlobalNonPluripolar
  GlobalDiagonalScaling

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

variable {omega : KahlerBackground n M} {alpha : RealBottChern n M}
  {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError}

/-- The actual ambient diagonal non-pluripolar mass associated with an
admissible restricted-current presentation. -/
def perturbedDiagonalPotentialMass
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon) : ℝ≥0∞ :=
  diagonalPotentialMass (p.representative + (epsilon : ℝ) • omega.form)
    p.potential p.potential_psh

/-- The ambient non-pluripolar mass of an admissible presentation is finite.
This uses the compact Kähler finite-mass theorem for the actual global measure,
not the unrelated finiteness theorem for restricted absolutely-continuous
masses. -/
theorem perturbedDiagonalPotentialMass_lt_top
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon) :
    perturbedDiagonalPotentialMass p < ⊤ := by
  change globalMixedMass (fun _ : Fin n => p.representative + (epsilon : ℝ) • omega.form)
    (fun _ => p.potential) (fun _ => p.potential_psh.1) < ⊤
  exact globalMixedMass_lt_top omega (fun _ => p.potential_psh.1)

/-- The diagonal non-pluripolar measure associated with an admissible
presentation gives zero mass to its analytic pole set. -/
theorem diagonalPotentialMeasure_poleSet_eq_zero
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon) :
    diagonalPotentialMeasure (p.representative + (epsilon : ℝ) • omega.form)
      p.potential p.potential_psh (poleSet p.potential) = 0 := by
  change globalMixedMeasure (fun _ : Fin n => p.representative + (epsilon : ℝ) • omega.form)
    (fun _ => p.potential) (fun _ => p.potential_psh.1) {x | p.potential x = ⊥} = 0
  exact globalMixedMeasure_pole_null_of_nondegenerate (fun _ => p.potential_psh.1)
    p.potential_psh

end

end SGPT.Foundations.Analysis.Pending.FullSpaceAmbientMass
