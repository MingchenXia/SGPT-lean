import SGPT.Foundations.Analysis.Pending.OrderMultiplicativity
import SGPT.Foundations.Analysis.Pending.ActualFiniteGeneratorLelongNormalization

set_option autoImplicit false

/-! # Coordinate normal powers compared with the actual least point jet

Natural coordinate factors imply full point-jet vanishing via the actual
point ideal. The original finite family supplies its least jet before all
coordinate factor tests. No whole-prime generic minimum is inferred.
Reference: Demailly, CADG, holomorphic Taylor germs; supplementary coordinate
consumer of the proved point-ideal and finite-family reader producers.
-/

open Set Filter
open scoped Topology Manifold ENNReal

namespace SGPT.Foundations.Analysis.Pending.CoordinateNormalOrderPointJetComparison

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus
  GermIdealOrder IdealWeightPowers

noncomputable section

/-- An actual coordinate factor produces full point-jet vanishing. The
holomorphic residual need not be a unit and the original germ may be zero. -/
theorem iteratedFDeriv_eq_zero_of_coordinate_factorization {n b : ℕ}
    (j : Fin n) {F H : ComplexModel n → ℂ}
    (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ H z)
    (heq : F =ᶠ[𝓝 0] fun z => H z * z j ^ b) :
    ∀ k < b, iteratedFDeriv ℂ k F 0 = 0 := by
  have hHhol : HolomorphicAt n H 0 := hH.mono fun _ hz =>
    mdifferentiableAt_iff_differentiableAt.mpr hz
  have hjhol : HolomorphicAt n (fun z : ComplexModel n => z j) 0 :=
    Eventually.of_forall fun z => mdifferentiableAt_iff_differentiableAt.mpr
      (EuclideanSpace.proj (𝕜 := ℂ) j).differentiableAt
  have hjmem := mem_pointIdeal_of_apply_eq_zero hjhol (by simp)
  have hp := OrderMultiplicativity.pow_mem_idealPow hjmem hjhol b
  have hprod := mul_mem_idealPow hHhol hp
  have hFmem := OrderTaylor.mem_idealPow_congr hprod heq.symm
  have hFhol := holomorphicAt_of_mem_idealPow hFmem
  have hjet := (OrderMultiplicativity.mem_idealPow_pointIdeal_iff_iteratedFDeriv
    hFhol b).mp hFmem
  simpa [complexChartAt, chartAt_self_eq] using hjet

/-- The original finite family supplies the least point jet and exact reader
before all coordinate normal factors, coefficients and bounded remainders. -/
theorem exists_finite_generator_normal_order_bound {m N : ℕ}
    (f : Fin N → ComplexModel (m + 1) → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (f i) z)
    (hne : ∃ i, ¬ ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), f i z = 0) :
    ∃ a : ℕ,
      (∀ i k, k < a → iteratedFDeriv ℂ k (f i) 0 = 0) ∧
      (∃ i, iteratedFDeriv ℂ a (f i) 0 ≠ 0) ∧
      (∀ c : ℝ, 0 < c → ∀ B : ComplexModel (m + 1) → ℝ, BoundedRealGermAt B 0 →
        lelongNumber (n := m + 1) (fun z => (c : EReal) * generatorLog f z + (B z : EReal)) 0 =
          ENNReal.ofReal (2 * c * (a : ℝ))) ∧
      ∀ (j : Fin (m + 1)) (b : ℕ) (H : Fin N → ComplexModel (m + 1) → ℂ),
        (∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (H i) z) →
        (∀ i, f i =ᶠ[𝓝 0] fun z => H i z * z j ^ b) → b ≤ a := by
  obtain ⟨a, hlow, hnon, hreader⟩ :=
    ActualFiniteGeneratorLelongNormalization.exists_finite_generator_lelong_normalization f hf hne
  refine ⟨a, hlow, hnon, hreader, ?_⟩
  intro j b H hH heq
  by_contra hnot
  have hab : a < b := lt_of_not_ge hnot
  obtain ⟨i, hi⟩ := hnon
  exact hi (iteratedFDeriv_eq_zero_of_coordinate_factorization j (hH i) (heq i) a hab)

end
end SGPT.Foundations.Analysis.Pending.CoordinateNormalOrderPointJetComparison
