import SGPT.Foundations.Analysis.Pending.ActualCodimensionOneInvertibleIdeal
import SGPT.Foundations.Analysis.Pending.DivisorMetric
import SGPT.Foundations.Analysis.Pending.LelongPoincareDivisor
import SGPT.Foundations.Analysis.Pending.VanishingIdealZeroLocus

set_option autoImplicit false

/-! # Internally metered divisor current of a genuine singular prime

The actual ideal, support, smooth metric and native global current properties
are produced. Native Haar and log-norm-squared normalizations are retained.
-/

noncomputable section
open Set
namespace SGPT.Foundations.Analysis.Pending.ActualCodimensionOneDivisorCurrent
open FirstPass HolomorphicIdealSheaves GlobalCurrents

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (n + 1)) M] [IsComplexManifold (n + 1) M]

/-- The actual effective divisor of a possibly singular geometric prime.
Its invertibility is internally produced from the actual codimension. -/
def effectiveDivisor (V : ClosedIrreducibleAnalyticSubvariety (n + 1) M)
    (hdim : V.dim = n) : EffectiveDivisor (n + 1) M :=
  ⟨vanishingIdeal V.carrier,
    ActualCodimensionOneInvertibleIdeal.isInvertible_vanishingIdeal V hdim⟩

/-- Its literal support is the entire original geometric subvariety. -/
theorem support_effectiveDivisor
    (V : ClosedIrreducibleAnalyticSubvariety (n + 1) M) (hdim : V.dim = n) :
    (effectiveDivisor V hdim).support = V.carrier :=
  VanishingIdealZeroLocus.zeroLocus_vanishingIdeal V.isClosed_carrier

/-- Compactness internally produces a smooth metric and all the genuine native
global current properties, with its exact local divisor-current coefficients.
No metered divisor/current or positivity certificate is a premise. -/
theorem exists_metered_current [CompactSpace M]
    (V : ClosedIrreducibleAnalyticSubvariety (n + 1) M) (hdim : V.dim = n)
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel (n + 1)))) ℝ
      (ComplexModel (n + 1))) :
    ∃ E : MeteredEffectiveQDivisor (n + 1) M,
      E.support = V.carrier ∧ DivisorMetric.IsDivisorMetric (effectiveDivisor V hdim) E ∧
      ChartLocallyIntegrable b E.weight ∧
      LelongPoincareDivisor.ddCWeight b (Nat.succ_pos n) E =
        LelongPoincareDivisor.integrationCurrent b (Nat.succ_pos n) E -
          smoothGlobalCurrent b (k := degreeTwo (Nat.succ_pos n)) E.curvature.val ∧
      (LelongPoincareDivisor.integrationCurrent b (Nat.succ_pos n) E).IsClosed b ∧
      (LelongPoincareDivisor.integrationCurrent b (Nat.succ_pos n) E).IsTypeOneOne b
        (Nat.succ_pos n) ∧
      (LelongPoincareDivisor.integrationCurrent b (Nat.succ_pos n) E).IsSquarePositive b
        (Nat.succ_pos n) ∧
      ∀ (P : LelongPoincareDivisor.LocalPresentation E) (e : ComplexChart (n + 1) M),
        LelongPoincareDivisor.restrictForm
          ((LelongPoincareDivisor.integrationCurrent b (Nat.succ_pos n) E).coefficients b e)
          (P.chartDomain_le e) =
          (LelongPoincareDivisor.haarFactor b : ℝ) • ∑ i, (P.a i : ℝ) •
            DivisorIntegrationCurrent.divisorCurrent (P.differentiableOn_chartG e i)
              (P.frequently_chartG_ne e i) := by
  obtain ⟨E, hE, hmetric⟩ := DivisorMetric.exists_divisorMetric (effectiveDivisor V hdim)
  exact ⟨E, hE.trans (support_effectiveDivisor V hdim), hmetric,
    LelongPoincareDivisor.lelongPoincare b (Nat.succ_pos n) E⟩

end SGPT.Foundations.Analysis.Pending.ActualCodimensionOneDivisorCurrent
