import SGPT.Foundations.Analysis.Pending.RawWeightedLogFamilyReverseIntegrability
import SGPT.Foundations.Analysis.Pending.WeightedHolomorphicGermIdealIntegralClosure

set_option autoImplicit false

/-! # An actual raw weighted ideal supplies a finite family before all reverse tests -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.RawMultiplierFiniteFamilyReverseMembership

open FirstPass IEquivalentMax WeightedHolomorphicGermIdealIntegralClosure

noncomputable section

/-- The actual original weighted ideal supplies its full finite holomorphic
family and one common neighborhood before every later margin and test. -/
theorem exists_full_family_with_reverse_membership
    {n : ℕ} {v : ComplexModel n → EReal} (hv : QuasiPlurisubharmonicAt v 0)
    {μ : Measure (ComplexModel n)} [IsFiniteMeasureOnCompacts μ]
    {k : ℝ} (hk : 0 < k) :
    ∃ (N : ℕ) (g : Fin N → ComplexModel n → ℂ)
      (hg : ∀ j, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (g j) z),
      Ideal.span (range fun j => HolGerm.mk (g j) (hg j)) = weightedGermIdeal hk hv μ ∧
      (∀ j, MultiplierIntegrableAt v k (g j) 0 μ) ∧
      ∃ O : Set (ComplexModel n), IsOpen O ∧ (0 : ComplexModel n) ∈ O ∧
        QuasiPlurisubharmonicOn v O ∧ (∀ j, WeightedL2On v k (g j) O μ) ∧
        ∀ (c δ : ℝ), 0 < c → 0 < δ → 2 * (c * (1 + δ)) / δ ≤ k →
          ∀ f : ComplexModel n → ℂ,
            MultiplierIntegrableAt (generatorLog g) (c * (1 + δ) / k) f 0 μ →
            MultiplierIntegrableAt v c f 0 μ := by
  classical
  let : IsNoetherianRing (HolGerm (ComplexModel n)) := isNoetherianRing_holGerm_euclidean n
  let J : Ideal (HolGerm (ComplexModel n)) := weightedGermIdeal hk hv μ
  obtain ⟨N, G, hgen⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    J.fg_of_isNoetherianRing
  change Ideal.span (range G) = J at hgen
  have hG : ∀ j, G j ∈ J := fun j => hgen ▸ Ideal.subset_span ⟨j, rfl⟩
  choose g hg heq hint using hG
  have hspan : Ideal.span (range fun j => HolGerm.mk (g j) (hg j)) =
      weightedGermIdeal hk hv μ := by
    simpa only [heq] using hgen
  obtain ⟨Q, hQ, h0Q, hvQ⟩ := exists_open_quasiPlurisubharmonicOn_of_at hv
  choose W hW h0W hhol hL2 using fun j => (hint j).2
  let O := Q ∩ ⋂ j, W j
  have hO : IsOpen O := hQ.inter (isOpen_iInter_of_finite hW)
  have h0O : (0 : ComplexModel n) ∈ O := ⟨h0Q, mem_iInter.mpr h0W⟩
  have hOQ : O ⊆ Q := inter_subset_left
  have hOW : ∀ j, O ⊆ W j := fun j z hz => mem_iInter.mp hz.2 j
  have hvO : QuasiPlurisubharmonicOn v O := hvQ.mono hOQ
  have hgO : ∀ j, WeightedL2On v k (g j) O μ :=
    fun j => (hL2 j).mono (hOW j)
  refine ⟨N, g, hg, hspan, hint, O, hO, h0O, hvO, hgO, ?_⟩
  intro c δ hc hδ hlevel f hsource
  exact RawWeightedLogFamilyReverseIntegrability.multiplierIntegrableAt_of_finite_weighted_log_family
    hc hδ hlevel hsource hO h0O hvO hgO

end
end SGPT.Foundations.Analysis.Pending.RawMultiplierFiniteFamilyReverseMembership
