import SGPT.Okounkov.EffectiveDivisorOrder
import SGPT.Okounkov.DivisorResidualGenericZero

set_option autoImplicit false
noncomputable section

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SourceTraceRepresentativeDefinition SquaredLogLelongSourceNormalization

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The original Cartier ideal internally supplies nondegeneracy of its
actual smooth metric, and hence genuine theta-PSH membership. -/
theorem isThetaPshPotential_effectiveDivisorMetric
    (D : EffectiveDivisor n M) (E : MeteredEffectiveQDivisor n M)
    (hmetric : DivisorMetric.IsDivisorMetric D E) :
    IsThetaPshPotential E.curvature.val E.weight := by
  refine ⟨MeteredDivisorPositivity.thetaPlurisubharmonic_weight E, ?_⟩
  intro x U hU hxU
  obtain ⟨V, hV, hxV, g, _hgd, hgen, h, _hh, hweq⟩ := hmetric x
  obtain ⟨f, hf, hfreq⟩ := effectiveDivisor_isNonzeroAt D x
  obtain ⟨_hfhol, c, _hc, hfg⟩ := isInSpanAt_eq_iff.mp ((hgen x hxV f).mp hf)
  obtain ⟨y, hy⟩ := (hfreq.and_eventually
    (Filter.Eventually.and (hU.mem_nhds hxU)
      (Filter.Eventually.and (hV.mem_nhds hxV) hfg))).exists
  have hgy : g y ≠ 0 := by
    intro hg0
    apply hy.1
    rw [hy.2.2.2]
    change c y * g y = 0
    rw [hg0, mul_zero]
  refine ⟨y, hy.2.1, ?_⟩
  rw [hweq y hy.2.2.1, MeteredDivisorWeightBounds.generatorLog_single_eq_coe hgy,
    ← EReal.coe_add]
  exact EReal.coe_ne_bot _

/-- Actual residual support noncontainment produces literal original
generic reader zero, through a genuine finite carrier point. -/
theorem sourceGeneric_effectiveDivisorMetric_eq_zero_of_not_contains {m : ℕ}
    {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
    [IsComplexManifold (m + 1) M] {W : Set M}
    (D : EffectiveDivisor (m + 1) M) (E : MeteredEffectiveQDivisor (m + 1) M)
    (hEW : E.support = D.support) (hnot : ¬ W ⊆ D.support) :
    sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) E.weight = 0 := by
  obtain ⟨p, hpW, hpD⟩ := not_subset.mp hnot
  have hpE : p ∉ E.support := by rwa [hEW]
  have hpbot : E.weight p ≠ ⊥ := hpE
  have hnative : lelongNumber (n := m + 1) E.weight p = 0 := by
    by_contra hne
    exact hpbot (eq_bot_of_lelongNumber_pos (Nat.succ_pos m)
      (MeteredDivisorPositivity.thetaPlurisubharmonic_weight E)
      (pos_iff_ne_zero.mpr hne))
  have hsource : squaredLogLelongNumber (n := m + 1) E.weight p = 0 := by
    apply (ENNReal.mul_right_inj (a := 2) (by norm_num) (by norm_num)).mp
    simpa only [mul_zero] using
      (lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m) E.weight p).symm.trans hnative
  apply le_antisymm _ bot_le
  exact (iInf_le _ (⟨p, hpW⟩ : W)).trans_eq hsource

end SGPT.Okounkov
