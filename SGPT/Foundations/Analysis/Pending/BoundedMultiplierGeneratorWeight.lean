import SGPT.Foundations.Analysis.Pending.AnalyticBoundedMultiplierIdeal

set_option autoImplicit false

/-! # Actual bounded weighted germs control the literal finite generator logarithm -/

open Set Filter
open scoped Topology ENNReal ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.BoundedMultiplierGeneratorWeight

open FirstPass FirstPass.HolomorphicIdealSheaves AnalyticBoundedMultiplierIdeal

noncomputable section

/-- Literal bounded weighted membership for every actual finite family
member internally supplies a logarithmic bound for the whole family. -/
theorem exists_generatorLog_le_weight_add
    {n N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {P : M → EReal} {x : M} {h : Fin N → M → ℂ}
    (hh : ∀ i, (boundedMultiplierIdeal (n := n) P).mem x (h i)) :
    ∃ D : ℝ, ∀ᶠ y in 𝓝 x, generatorLog h y ≤ P y + (D : EReal) := by
  classical
  choose K hK hbound using fun i => (hh i).2
  let C : ℝ := 1 + ∑ i : Fin N, K i
  have hsumK : 0 ≤ ∑ i : Fin N, K i := Finset.sum_nonneg fun i _ => (hK i).le
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨Real.log C, ?_⟩
  have hall : ∀ᶠ y in 𝓝 x, ∀ i, multiplierDensity P 1 (h i) y ≤ ENNReal.ofReal (K i) :=
    eventually_all.mpr hbound
  filter_upwards [hall] with y hy
  cases hPy : P y with
  | bot =>
    have hz (i : Fin N) : h i y = 0 := by
      by_contra hi
      have htop := multiplierDensity_eq_top_at_pole zero_lt_one hPy hi
      have hle := hy i
      rw [htop] at hle
      exact ENNReal.ofReal_ne_top (top_le_iff.mp hle)
    rw [(generatorLog_eq_bot_iff h y).mpr hz]
    simp
  | top => simp
  | coe t =>
    have hreal (i : Fin N) : ‖h i y‖ ^ 2 * Real.exp (-t) ≤ K i := by
      apply (ENNReal.ofReal_le_ofReal_iff (hK i).le).mp
      simpa only [multiplierDensity, hPy, multiplierWeight_coe, one_mul,
        ← ENNReal.ofReal_mul (sq_nonneg (‖h i y‖))] using hy i
    have hsum : generatorNormSq h y * Real.exp (-t) ≤ ∑ i : Fin N, K i := by
      rw [generatorNormSq, Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ => hreal i
    have hgen : generatorNormSq h y ≤ C * Real.exp t := by
      calc generatorNormSq h y
          = (generatorNormSq h y * Real.exp (-t)) * Real.exp t := by
            rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
        _ ≤ (∑ i : Fin N, K i) * Real.exp t :=
          mul_le_mul_of_nonneg_right hsum (Real.exp_pos _).le
        _ ≤ _ := by dsimp [C]; nlinarith [Real.exp_pos t]
    rw [generatorLog_eq_log_sum]
    calc ENNReal.log (ENNReal.ofReal (∑ i, ‖h i y‖ ^ 2))
        ≤ ENNReal.log (ENNReal.ofReal (C * Real.exp t)) :=
          ENNReal.log_monotone (ENNReal.ofReal_le_ofReal hgen)
      _ = _ := by
        rw [ENNReal.ofReal_mul hC.le, ENNReal.log_mul_add,
          ENNReal.log_ofReal_of_pos hC, ENNReal.log_ofReal_of_pos (Real.exp_pos t),
          Real.log_exp, add_comm]

end

end SGPT.Foundations.Analysis.Pending.BoundedMultiplierGeneratorWeight
