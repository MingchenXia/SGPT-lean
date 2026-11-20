import SGPT.Foundations.Analysis.Pending.MixedMassProductCalculus
import SGPT.Foundations.Analysis.Pending.RelativeEnergyIntegrability

set_option autoImplicit false

/-!
# Actual canonical weighted mixed positive expansion

The polynomial integral input in Lu, arXiv:2005.04264v1, Theorem 1.2.
Actual nonnegative slotwise measure expansion combines with produced
same-type canonical integrability, retaining zero coefficients and dimension zero.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.CanonicalMixedIntegralExpansion

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar
open GlobalMultilinearExpansion MixedMassProductCalculus RelativeEnergyIntegrability

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] {iota : Type*} [Fintype iota] [DecidableEq iota]

/-- Integrate the actual nonnegative mixed-product expansion against the
canonical difference, producing integrability for every actual summand. -/
theorem integral_canonicalDiff_sumPot_expand (omega : KahlerBackground n M)
    {alpha beta : SmoothRealForm n M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential alpha u) (hv : IsThetaPshPotential beta v)
    (htype : SameSingularityTypeOn u v univ)
    {c : Fin n → iota → ℝ} (hc : ∀ k i, 0 ≤ c k i)
    {forms : iota → ClosedRealOneOneForm n M} {pots : iota → M → EReal}
    (hpots : ∀ i, IsThetaPshPotential (forms i).val (pots i)) :
    (∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂globalMixedMeasure (fun k => sumForm Finset.univ (c k) forms)
        (fun k => sumPot Finset.univ (c k) pots)
        (fun k => thetaPlurisubharmonic_sumPot_of_nonneg (hc k) fun i => (hpots i).1)) =
    ∑ g : Fin n → iota, (∏ k, c k (g k)) *
      ∫ x, canonicalERealDiffToReal (u x) (v x)
        ∂globalMixedMeasure (fun k => forms (g k)) (fun k => pots (g k))
          (fun k => (hpots (g k)).1) := by
  classical
  rw [globalMixedMeasure_sumPot_expand omega hc hpots, integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [integral_smul_measure]
    simp only [ENNReal.toReal_ofReal (Finset.prod_nonneg fun k _ => hc k (g k)),
      smul_eq_mul]
  · intro g _
    exact (integrable_canonicalDiff_globalMixedMeasure omega hu.1 hv.1 htype
      (fun k => (hpots (g k)).1)).smul_measure ENNReal.ofReal_ne_top

end

end SGPT.Foundations.Analysis.Pending.CanonicalMixedIntegralExpansion
