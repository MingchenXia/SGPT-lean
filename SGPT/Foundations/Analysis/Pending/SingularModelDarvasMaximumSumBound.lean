import SGPT.Foundations.Analysis.Pending.SingularModelDarvasDiagonalUpperComparison

set_option autoImplicit false

/-! # Actual maximum-distance sum with Xia's precise dimension constant -/

namespace SGPT.Foundations.Analysis.Pending.SingularModelDarvasMaximumSumBound

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelFiniteEnergyDiagonalGap

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M}
  {φ u v : M → EReal} {hφ : IsModelPotential θ φ}

/-- Actual E1 maximum closure, the actual maximum gap decomposition and one actual upper comparison produce the source constant for the sum of both maximum distances. -/
theorem relativeD1_max_sum_le_mul (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ)
    (hv : RelativeFiniteEnergyPreceq θ φ v hφ) :
    relativeD1 θ φ hφ (fun x => max (u x) (v x)) u +
      relativeD1 θ φ hφ (fun x => max (u x) (v x)) v ≤
        (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)) * relativeD1 θ φ hφ u v := by
  have hm := SingularModelFiniteEnergyGapMax.relativeFiniteEnergyPreceq_max omega hu hv
  have ha := SingularModelDarvasDiagonalComparison.ofReal_relativeD1_le_diagonalGapIntegral
    omega hm hu
  have hb := SingularModelDarvasDiagonalComparison.ofReal_relativeD1_le_diagonalGapIntegral
    omega hm hv
  have h := add_le_add ha hb
  rw [← ENNReal.ofReal_add
    (SingularModelDarvasBasic.relativeD1_nonneg omega hm hu)
    (SingularModelDarvasBasic.relativeD1_nonneg omega hm hv),
    ← SingularModelFiniteEnergyGapMax.diagonalGapIntegral_max_decomposition
      hu.1.plurisubharmonic hv.1.plurisubharmonic] at h
  have hbound := h.trans
    (SingularModelDarvasDiagonalUpperComparison.diagonalGapIntegral_le_mul_relativeD1 omega hu hv)
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (by positivity) (SingularModelDarvasBasic.relativeD1_nonneg omega hu hv))).mp hbound

end

end SGPT.Foundations.Analysis.Pending.SingularModelDarvasMaximumSumBound
