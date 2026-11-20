import SGPT.Foundations.Analysis.Pending.BoundedMultiplierGeneratorWeight
import SGPT.Foundations.Analysis.Pending.MultiplierIdealWeightLowerBound

set_option autoImplicit false

/-! # Actual coherent multiplier generators produce potential comparison -/

open Set Filter
open scoped Topology ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.BoundedMultiplierPotentialComparison

open FirstPass FirstPass.HolomorphicIdealSheaves AnalyticBoundedMultiplierIdeal

noncomputable section

/-- Genuine coherence produces the full multiplier generators, and the
actual Demailly lower bound turns their bounded weighted membership into
a uniform compact potential comparison. -/
theorem moreSingularOn_of_multiplierIdeal_le_boundedMultiplierIdeal
    {n : ℕ} (hn : 0 < n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
    {ζ : ClosedRealOneOneForm n M} {ψ Φ : M → EReal}
    (hψ : IsThetaPshPotential ζ.val ψ) {m : ℕ} (hm : 0 < m)
    {p : ℝ}
    (hle : (multiplierIdeal (n := n) (m : ℝ) ψ).Le
      (boundedMultiplierIdeal (n := n) (fun y => (p : EReal) * Φ y))) :
    MoreSingularOn ψ (fun y => (((p / (m : ℝ) : ℝ)) : EReal) * Φ y) univ := by
  apply IdealWeightComparison.moreSingularOn_univ_of_forall_moreSingularAt
  intro x
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨U, hU, hxU, N, h, hhdiff, hhiff⟩ :=
    MultiplierIdealBergmanNadelManifold.isCoherent_multiplierIdeal_of_pos hn hψ.1 hmR x
  have hbounded (i : Fin N) :
      (boundedMultiplierIdeal (n := n) (fun y => (p : EReal) * Φ y)).mem x (h i) :=
    hle x (h i) (IdealWeightComparison.mem_of_isPresentation hU hxU hhdiff hhiff i)
  obtain ⟨C₂, hC₂⟩ := BoundedMultiplierGeneratorWeight.exists_generatorLog_le_weight_add hbounded
  obtain ⟨C₁, hC₁⟩ := MultiplierIdealWeightLowerBound.exists_le_inv_mul_generatorLog hn hψ hm x
    (g := h) (fun f hf => (hhiff x hxU f).mp hf)
  have hmi : 0 < (m : ℝ)⁻¹ := inv_pos.mpr hmR
  refine ⟨C₁ + (m : ℝ)⁻¹ * C₂, ?_⟩
  filter_upwards [hC₁, hC₂] with y hy₁ hy₂
  calc ψ y ≤ (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog h y + (C₁ : EReal) := hy₁
    _ ≤ (((m : ℝ)⁻¹ : ℝ) : EReal) * ((p : EReal) * Φ y + (C₂ : EReal)) + (C₁ : EReal) :=
      add_le_add (mul_le_mul_of_nonneg_left hy₂ (EReal.coe_nonneg.mpr hmi.le)) le_rfl
    _ = (((p / (m : ℝ) : ℝ)) : EReal) * Φ y +
        ((C₁ + (m : ℝ)⁻¹ * C₂ : ℝ) : EReal) := by
      rw [ThetaPshConvexCombination.coe_mul_add_coe hmi,
        MultiplierIdealWeightLowerBound.coe_mul_coe_mul, add_assoc,
        ← EReal.coe_add]
      congr 1
      · congr 1
        simp only [div_eq_mul_inv, mul_comm]
      · congr 1
        ring

end

end SGPT.Foundations.Analysis.Pending.BoundedMultiplierPotentialComparison
