import SGPT.Foundations.Analysis.Pending.StrictMonomialTruncationAllDimensions

set_option autoImplicit false

/-! # Actual all-power source integrals force the zero original test germ -/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.PointPowerTruncationZeroTest

open FirstPass HolomorphicGermReducednessBridge

noncomputable section

/-- Actual integrals against every genuine point-power family force a zero germ;
zero-dimensional Haar mass and all pole densities are retained. -/
theorem eventually_eq_zero_of_all_point_power_integrals {n : ℕ} {q : ℝ}
    {F : ComplexModel n → ℂ}
    (htrunc : ∀ N : ℕ, ∃ (r : ℕ) (Q : Fin r → ComplexModel n → ℂ)
      (hQ : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (Q i) z),
      (∀ i, HolGerm.mk (Q i) (hQ i) ∈
        (Ideal.span (Set.range fun j : Fin n => HolGerm.mk
          (fun z : ComplexModel n => z j) (eventually_differentiableAt_coordinate j))) ^ N) ∧
      MultiplierIntegrableAt (generatorLog Q) q F 0 volume) :
    F =ᶠ[𝓝 (0 : ComplexModel n)] (fun _ => (0 : ℂ)) := by
  classical
  cases n with
  | zero =>
    obtain ⟨r, Q, hQ, hmem, hsource⟩ := htrunc 1
    have hI : Ideal.span (Set.range fun j : Fin 0 => HolGerm.mk
        (fun z : ComplexModel 0 => z j) (eventually_differentiableAt_coordinate j)) = ⊥ := by
      simp
    have hQg (i : Fin r) : HolGerm.mk (Q i) (hQ i) = 0 := by
      simpa only [hI, pow_one, Submodule.mem_bot] using hmem i
    have hQ0 (i : Fin r) : Q i 0 = 0 := by
      have h := congrArg HolGerm.eval (hQg i)
      simpa only [HolGerm.eval_mk, map_zero] using h
    have hQz (i : Fin r) (z : ComplexModel 0) : Q i z = 0 :=
      (congrArg (Q i) (Subsingleton.elim z 0)).trans (hQ0 i)
    have hbot (z : ComplexModel 0) : generatorLog Q z = ⊥ := by
      simp only [generatorLog_eq_log_sum, hQz, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        Finset.sum_const_zero, ENNReal.ofReal_zero, ENNReal.log_zero]
    obtain ⟨hq, U, hU, h0, _hhol, _hmeas, hint⟩ := hsource
    have hF0 : F 0 = 0 := by
      by_contra hn
      have hdens : multiplierDensity (generatorLog Q) q F = fun _ => (⊤ : ℝ≥0∞) := by
        funext z
        exact multiplierDensity_eq_top_at_pole hq (hbot z)
          (by simpa only [Subsingleton.elim z 0] using hn)
      have hμ : volume U ≠ 0 := (hU.measure_pos volume ⟨0, h0⟩).ne'
      have heq : (∫⁻ z in U, multiplierDensity (generatorLog Q) q F z ∂volume) = ⊤ := by
        rw [hdens, lintegral_const, Measure.restrict_apply_univ, ENNReal.top_mul hμ]
      rw [heq] at hint
      exact lt_irrefl _ hint
    exact Eventually.of_forall fun z => (congrArg F (Subsingleton.elim z 0)).trans hF0
  | succ m =>
    obtain ⟨r, Q, hQ, _hmem, hsource⟩ := htrunc 0
    obtain ⟨hq, U, hU, h0, hhol, _hint⟩ := hsource
    have hF : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ F z := by
      filter_upwards [hU.mem_nhds h0] with z hz
      exact hhol.differentiableAt (hU.mem_nhds hz)
    have hno : ¬∃ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), F z ≠ 0 := by
      intro hne
      obtain ⟨d, H, hH, _hHne, heq, hnot⟩ :=
        HolomorphicCoordinateOrders.exists_coordinate_factorization_of_nonzero_germ hF hne
      have hhalf : 0 < q / 2 := by positivity
      obtain ⟨A, hA⟩ := exists_nat_gt (((d (0 : Fin (m + 1)) : ℝ) + 1) / (q / 2))
      have hlarge : (d (0 : Fin (m + 1)) : ℝ) + 1 < (q / 2) * (A : ℝ) := by
        have h := (div_lt_iff₀ hhalf).mp hA
        simpa only [mul_comm] using h
      let a : Fin (m + 1) → ℕ := fun j => if j = 0 then A else 0
      have htruncM : ∀ N : ℕ, ∃ (r : ℕ) (Q : Fin r → ComplexModel (m + 1) → ℂ)
          (hQ : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (Q i) z),
          (∀ i, HolGerm.mk (Q i) (hQ i) ∈
            Ideal.span {∏ j : Fin (m + 1), HolGerm.mk (fun z : ComplexModel (m + 1) => z j)
              (eventually_differentiableAt_coordinate j) ^ a j} ⊔
            (Ideal.span (Set.range fun j : Fin (m + 1) => HolGerm.mk
              (fun z : ComplexModel (m + 1) => z j) (eventually_differentiableAt_coordinate j))) ^ N) ∧
          MultiplierIntegrableAt (generatorLog Q) q F 0 volume := by
        intro N
        obtain ⟨r, Q, hQ, hmem, hint⟩ := htrunc N
        refine ⟨r, Q, hQ, ?_, hint⟩
        intro i
        exact (show
          (Ideal.span (Set.range fun j : Fin (m + 1) => HolGerm.mk
            (fun z : ComplexModel (m + 1) => z j) (eventually_differentiableAt_coordinate j))) ^ N ≤
          Ideal.span {∏ j : Fin (m + 1), HolGerm.mk (fun z : ComplexModel (m + 1) => z j)
            (eventually_differentiableAt_coordinate j) ^ a j} ⊔
          (Ideal.span (Set.range fun j : Fin (m + 1) => HolGerm.mk
            (fun z : ComplexModel (m + 1) => z j) (eventually_differentiableAt_coordinate j))) ^ N
          from le_sup_right) (hmem i)
      have hM := StrictMonomialTruncationAllDimensions.multiplierIntegrableAt_of_all_monomial_truncations
        a hhalf (by linarith : q / 2 < q) htruncM
      have hρ : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
          ContinuousAt (fun _ : ComplexModel (m + 1) => (0 : ℝ)) z :=
        Eventually.of_forall fun _ => continuousAt_const
      have hthreshold := SNCHolomorphicTestMultiplierCriterion.thresholds_of_multiplier_integrable
        d (fun j => (a j : ℝ)) hH hnot heq hρ
        (by simpa only [EReal.coe_zero, add_zero] using hM) (0 : Fin (m + 1))
      have hsmall : (q / 2) * (A : ℝ) < (d (0 : Fin (m + 1)) : ℝ) + 1 := by
        simpa only [a, if_true] using hthreshold
      exact (not_lt_of_ge hsmall.le) hlarge
    filter_upwards [Filter.not_frequently.mp hno] with z hz
    exact not_ne_iff.mp hz

/-- The actual zero-germ boundary supplies the original multiplier predicate
for every raw weight, with zero times infinity kept at all poles. -/
theorem multiplierIntegrableAt_of_all_point_power_integrals {n : ℕ} {q c : ℝ}
    {F : ComplexModel n → ℂ} (ψ : ComplexModel n → EReal) (hc : 0 < c)
    (htrunc : ∀ N : ℕ, ∃ (r : ℕ) (Q : Fin r → ComplexModel n → ℂ)
      (hQ : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (Q i) z),
      (∀ i, HolGerm.mk (Q i) (hQ i) ∈
        (Ideal.span (Set.range fun j : Fin n => HolGerm.mk
          (fun z : ComplexModel n => z j) (eventually_differentiableAt_coordinate j))) ^ N) ∧
      MultiplierIntegrableAt (generatorLog Q) q F 0 volume) :
    MultiplierIntegrableAt ψ c F 0 volume :=
  (multiplierIntegrableAt_zero ψ hc (0 : ComplexModel n) volume).congr
    EventuallyEq.rfl (eventually_eq_zero_of_all_point_power_integrals htrunc).symm

end
end SGPT.Foundations.Analysis.Pending.PointPowerTruncationZeroTest
