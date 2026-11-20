import SGPT.Foundations.Analysis.Pending.SingularModelDarvasDiagonalUpperComparison
import SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyGapMax

set_option autoImplicit false

/-!
# Actual singular-model Darvas maximum distance bound

Xia SGPT PDF0164 Corollary 4.3.1, equation (4.20). Actual maximum
finite-energy closure and actual nonnegative diagonal-gap decomposition,
followed by the actual source two-sided diagonal comparison, produce
its exact dimension constant. No maximum or comparison certificate is assumed.
-/

open Set Filter MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularModelDarvasMaximumBound

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelFiniteEnergyDiagonalGap

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal} {hφ : IsModelPotential θ φ}

/-- The actual source Corollary 4.3.1 bound with the exact source dimension constant. -/
theorem relativeD1_max_le_mul (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ) :
    relativeD1 θ φ hφ (fun x => max (u x) (v x)) u ≤
      (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)) * relativeD1 θ φ hφ u v := by
  have hm := SingularModelFiniteEnergyGapMax.relativeFiniteEnergyPreceq_max omega hu hv
  have hsplit := SingularModelFiniteEnergyGapMax.diagonalGapIntegral_max_decomposition
    hu.1.plurisubharmonic hv.1.plurisubharmonic
  have hgap : diagonalGapIntegral θ (fun x => max (u x) (v x)) u
      hm.1.plurisubharmonic hu.1.plurisubharmonic ≤
      diagonalGapIntegral θ u v hu.1.plurisubharmonic hv.1.plurisubharmonic := by
    rw [hsplit]
    exact le_add_of_nonneg_right zero_le
  have h := ((SingularModelDarvasDiagonalComparison.ofReal_relativeD1_le_diagonalGapIntegral
    omega hm hu).trans hgap).trans
      (SingularModelDarvasDiagonalUpperComparison.diagonalGapIntegral_le_mul_relativeD1 omega hu hv)
  apply (ENNReal.ofReal_le_ofReal_iff ?_).mp h
  exact mul_nonneg (by positivity) (SingularModelDarvasBasic.relativeD1_nonneg omega hu hv)

end

end SGPT.Foundations.Analysis.Pending.SingularModelDarvasMaximumBound
