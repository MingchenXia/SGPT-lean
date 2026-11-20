import SGPT.PSH.LocalIntegralPullbackCoefficients

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending HironakaEffectiveDivisorSum
open scoped Topology Manifold ContDiff

universe u
variable {n : ℕ} {X Y : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {π : Y → X}

/-- The existing literal ideal-image total transform, with its genuine
finite additive arithmetic. Modification geometry supplies thinness internally. -/
def cartierModificationPullback
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π) :
    EffectiveDivisor n X →+ EffectiveDivisor n Y where
  toFun := GermIdealTotalTransform.EffectiveDivisor.totalTransform hπ.1
    (interior_exceptionalLocus_eq_empty_of_native_analyticModification hπ)
  map_zero' := by
    apply effectiveDivisor_eq_of_ideal_eq
    exact BlowupExceptionalDivisor.pullback_unitIdeal
  map_add' D E := by
    apply effectiveDivisor_eq_of_ideal_eq
    exact GermIdealTotalTransform.pullback_mul hπ.1
      (DivisorMetric.isCoherent_of_isInvertible D.isInvertible)
      (DivisorMetric.isCoherent_of_isInvertible E.isInvertible)

theorem cartierModificationPullback_ideal
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    (D : EffectiveDivisor n X) :
    (cartierModificationPullback hπ D).ideal = GermIdeal.pullback (m := n) π D.ideal := rfl

/-- Actual original local generators give ENTIRE pulled finite-product
stalks at the original upstairs point, in both directions. -/
theorem finite_cartier_pullback_generator_product {ι : Type*}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    (s : Finset ι) (F : ι → EffectiveDivisor n X) (a : ι → ℕ)
    (g : ι → X → ℂ) (y : Y) (hg : ∀ i ∈ s, HolomorphicAt n (g i) (π y))
    (hgen : ∀ i ∈ s, ∀ h, (F i).ideal.mem (π y) h ↔
      IsInSpanAt (n := n) (· = g i) (π y) h) (h : Y → ℂ) :
    (∑ i ∈ s, a i • cartierModificationPullback hπ (F i)).ideal.mem y h ↔
      IsInSpanAt (n := n) (· = fun z => ∏ i ∈ s, g i (π z) ^ a i) y h := by
  exact finite_cartier_sum_generator_product s (fun i => cartierModificationPullback hπ (F i)) a
    (fun i => g i ∘ π) y
    (fun i hi => (hg i hi).comp_contMDiff (Eventually.of_forall fun _ => hπ.1.contMDiffAt))
    (fun i hi b => MemberPullback.pullback_mem_iff_of_generator hπ.1 (hg i hi) (hgen i hi) b) h

section Prime
variable {m : ℕ} {M N : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [TopologicalSpace N] [ChartedSpace (ComplexModel (m + 1)) N] [IsComplexManifold (m + 1) N]
  {f : N → M}

theorem cartierModificationPullback_reduced_prime
    (hf : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) f)
    (P : GeometricPrimeCarrier (m + 1) M) :
    cartierModificationPullback hf (geometricPrimeCarrierEffectiveDivisor P) =
      geometricPrimeCarrierTotalTransform P hf := by
  apply effectiveDivisor_eq_of_ideal_eq
  rw [cartierModificationPullback_ideal, geometricPrimeCarrierEffectiveDivisor_ideal,
    geometricPrimeCarrierTotalTransform_ideal]

theorem cartierModificationPullback_finite_prime_sum {ι : Type*}
    (hf : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) f)
    (s : Finset ι) (P : ι → GeometricPrimeCarrier (m + 1) M) (a : ι → ℕ) :
    cartierModificationPullback hf (∑ i ∈ s, a i • geometricPrimeCarrierEffectiveDivisor (P i)) =
      ∑ i ∈ s, a i • geometricPrimeCarrierTotalTransform (P i) hf := by
  simp only [map_sum, map_nsmul, cartierModificationPullback_reduced_prime]

end Prime
end SGPT.PSH
