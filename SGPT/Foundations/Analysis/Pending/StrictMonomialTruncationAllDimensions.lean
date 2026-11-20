import SGPT.Foundations.Analysis.Pending.StrictMonomialTruncationStability
import SGPT.Foundations.Analysis.Pending.HolomorphicNormalOrderDiscrepancy
import SGPT.Foundations.Analysis.Pending.CoordinateLineUnitMultiplierBound

set_option autoImplicit false

/-! # Genuine strict monomial truncation stability in every dimension -/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.StrictMonomialTruncationAllDimensions

open FirstPass HolomorphicGermReducednessBridge WeightedAffineMonomialMultiplierPullback

noncomputable section

private theorem one_dimensional_factor_threshold (a : Fin 1 → ℕ) {q q' : ℝ}
    (hqq' : q' < q) {F : ComplexModel 1 → ℂ}
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel 1), DifferentiableAt ℂ F z)
    (hne : ∃ᶠ z in 𝓝 (0 : ComplexModel 1), F z ≠ 0)
    (htrunc : ∀ N : ℕ, ∃ (r : ℕ) (Q : Fin r → ComplexModel 1 → ℂ)
      (hQ : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel 1), DifferentiableAt ℂ (Q i) z),
      (∀ i, HolGerm.mk (Q i) (hQ i) ∈
        Ideal.span {∏ j : Fin 1, HolGerm.mk (fun z : ComplexModel 1 => z j)
          (eventually_differentiableAt_coordinate j) ^ a j} ⊔
        (Ideal.span (Set.range fun j : Fin 1 => HolGerm.mk
          (fun z : ComplexModel 1 => z j) (eventually_differentiableAt_coordinate j))) ^ N) ∧
      MultiplierIntegrableAt (generatorLog Q) q F 0 volume) :
    ∃ (b : ℕ) (H : ComplexModel 1 → ℂ),
      (∀ᶠ z in 𝓝 (0 : ComplexModel 1), DifferentiableAt ℂ H z) ∧
      F =ᶠ[𝓝 0] (fun z => z 0 ^ b * H z) ∧ q' * (a 0 : ℝ) < (b : ℝ) + 1 := by
  classical
  obtain ⟨b, H, hH, hfact, hfreq⟩ :=
    HolomorphicNormalOrderDiscrepancy.exists_finite_normal_order_of_nonzero_germ hF hne
  have hH0 : H 0 ≠ 0 := by
    obtain ⟨z, hz, hHz⟩ := hfreq.exists
    have hz0 : z = 0 := by
      ext i
      have hi : i = Fin.last 0 := by omega
      simpa only [hi, PiLp.zero_apply] using hz
    simpa only [hz0] using hHz
  obtain ⟨U, hsub, hU, h0⟩ := _root_.mem_nhds_iff.mp hH
  have hHa : AnalyticAt ℂ H 0 := HolomorphicAnalytic.analyticAt_of_differentiableOn hU
    (fun z hz => (hsub hz).differentiableWithinAt) h0
  let ep : ComplexModel 1 := EuclideanSpace.single (0 : Fin 1) (1 : ℂ)
  let line : ℂ → ComplexModel 1 := fun t => t • ep
  have hla : AnalyticAt ℂ line 0 := analyticAt_id.smul analyticAt_const
  have hHla : AnalyticAt ℂ (fun t => H (line t)) 0 :=
    AnalyticAt.comp (g := H) (f := line) (by simpa only [line, zero_smul] using hHa) hla
  have hline0 : H (line 0) ≠ 0 := by simpa only [line, zero_smul] using hH0
  have hTline : Tendsto line (𝓝 (0 : ℂ)) (𝓝 0) := by
    have hcont : Continuous line := continuous_id.smul continuous_const
    simpa only [line, zero_smul] using hcont.continuousAt.tendsto (x := (0 : ℂ))
  have hline : (fun t => F (t • ep)) =ᶠ[𝓝 (0 : ℂ)]
      (fun t => t ^ b * H (line t)) := by
    filter_upwards [hTline.eventually hfact] with t ht
    simpa [line, ep] using ht
  obtain ⟨r, Q, hQ, hmem, hint⟩ := htrunc (a 0)
  have hM : ∀ᶠ z in 𝓝 (0 : ComplexModel 1),
      DifferentiableAt ℂ (fun z : ComplexModel 1 => ∏ i, z i ^ a i) z := by
    have hdiff (z : ComplexModel 1) :
        DifferentiableAt ℂ (fun w : ComplexModel 1 => w 0 ^ a 0) z :=
      ((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1)).differentiableAt).pow (a 0)
    filter_upwards [] with z
    simpa only [Fin.prod_univ_one] using hdiff z
  have hmk : HolGerm.mk (fun z : ComplexModel 1 => ∏ i, z i ^ a i) hM =
      ∏ j : Fin 1, HolGerm.mk (fun z : ComplexModel 1 => z j)
        (eventually_differentiableAt_coordinate j) ^ a j := by
    simp only [Fin.prod_univ_one]
    exact HolGerm.mk_pow _ _ _
  have hmem' (i : Fin r) : HolGerm.mk (Q i) (hQ i) ∈
      Ideal.span {HolGerm.mk (fun z : ComplexModel 1 => ∏ j, z j ^ a j) hM} ⊔
        (Ideal.span (Set.range fun j : Fin 1 => HolGerm.mk
          (fun z : ComplexModel 1 => z j) (eventually_differentiableAt_coordinate j))) ^ a 0 := by
    rw [hmk]
    exact hmem i
  have hT : affineMonomial (fun _ : Fin 1 => 1) (0 : ComplexModel 1) (0 : Fin 1) = id := by
    funext z
    ext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    simp [affineMonomial]
  obtain ⟨C, hC⟩ := WeightedTruncatedGeneratorGrowth.exists_log_upper_of_truncated_ideal_membership
    (0 : Fin 1) a (fun _ => 1) 0 (fun i hi => (hi (Subsingleton.elim _ _)).elim)
    (a 0) (by simp) Q hQ hmem'
  have hupper : ∀ᶠ z in 𝓝 (0 : ComplexModel 1),
      generatorLog Q z ≤ ((a 0 : ℕ) : EReal) * logNormSq (z 0) + (C : EReal) := by
    simpa only [hT, Function.comp_id, Fin.sum_univ_one, if_true, one_mul] using hC
  have hqa : q * (a 0 : ℝ) < (b : ℝ) + 1 :=
    CoordinateLineUnitMultiplierBound.threshold_of_integrability_and_line_unit
      (0 : Fin 1) (by positivity : (0 : ℝ) ≤ (a 0 : ℝ)) hint
      ⟨C, by simpa only [EReal.coe_natCast] using hupper⟩ hHla hline0 hline
  refine ⟨b, H, hH, ?_, ?_⟩
  · simpa only [show (Fin.last 0 : Fin 1) = 0 from rfl] using hfact
  · exact (mul_le_mul_of_nonneg_right hqq'.le (Nat.cast_nonneg _)).trans_lt hqa

/-- Every original dimension and test germ, including zero germs, is retained;
all source integrals and source ideal memberships are actual natural data. -/
theorem multiplierIntegrableAt_of_all_monomial_truncations {n : ℕ}
    (a : Fin n → ℕ) {q q' : ℝ} (hq' : 0 < q') (hqq' : q' < q)
    {F : ComplexModel n → ℂ}
    (htrunc : ∀ N : ℕ, ∃ (r : ℕ) (Q : Fin r → ComplexModel n → ℂ)
      (hQ : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (Q i) z),
      (∀ i, HolGerm.mk (Q i) (hQ i) ∈
        Ideal.span {∏ j : Fin n, HolGerm.mk (fun z : ComplexModel n => z j)
          (eventually_differentiableAt_coordinate j) ^ a j} ⊔
        (Ideal.span (Set.range fun j : Fin n => HolGerm.mk
          (fun z : ComplexModel n => z j) (eventually_differentiableAt_coordinate j))) ^ N) ∧
      MultiplierIntegrableAt (generatorLog Q) q F 0 volume) :
    MultiplierIntegrableAt (fun z : ComplexModel n =>
      ∑ j, (((2 * (a j : ℝ)) : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z j‖))
      q' F 0 volume := by
  classical
  obtain ⟨r, Q, hQ, _hmem, hsource⟩ := htrunc 0
  obtain ⟨_hq, U, hU, h0, hhol, _hint⟩ := hsource
  have hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z := by
    filter_upwards [hU.mem_nhds h0] with z hz
    exact hhol.differentiableAt (hU.mem_nhds hz)
  by_cases hne : ∃ᶠ z in 𝓝 (0 : ComplexModel n), F z ≠ 0
  · cases n with
    | zero =>
      have heq : F =ᶠ[𝓝 (0 : ComplexModel 0)]
          (fun z => F z * ∏ j : Fin 0, z j ^ (0 : ℕ)) := by simp
      have hρ : ∀ᶠ z in 𝓝 (0 : ComplexModel 0),
          ContinuousAt (fun _ : ComplexModel 0 => (0 : ℝ)) z :=
        Eventually.of_forall fun _ => continuousAt_const
      simpa only [EReal.coe_zero, add_zero] using
        HolomorphicCoordinateOrders.multiplierIntegrableAt_of_coordinate_factorization
          (fun _ : Fin 0 => 0) (fun j => (a j : ℝ)) hq' hF heq hρ (fun j => Fin.elim0 j)
    | succ k =>
      cases k with
      | zero =>
        obtain ⟨b, H, hH, heq, hb⟩ := one_dimensional_factor_threshold a hqq' hF hne htrunc
        have heq' : F =ᶠ[𝓝 (0 : ComplexModel 1)]
            (fun z => H z * ∏ j : Fin 1, z j ^ b) := by
          filter_upwards [heq] with z hz
          simpa only [Fin.prod_univ_one, mul_comm] using hz
        have hρ : ∀ᶠ z in 𝓝 (0 : ComplexModel 1),
            ContinuousAt (fun _ : ComplexModel 1 => (0 : ℝ)) z :=
          Eventually.of_forall fun _ => continuousAt_const
        simpa only [EReal.coe_zero, add_zero] using
          HolomorphicCoordinateOrders.multiplierIntegrableAt_of_coordinate_factorization
            (fun _ : Fin 1 => b) (fun j => (a j : ℝ)) hq' hH heq' hρ
            (fun j => by have hj : j = (0 : Fin 1) := Subsingleton.elim _ _; simpa only [hj] using hb)
      | succ m =>
        exact StrictMonomialTruncationStability.multiplierIntegrableAt_of_all_monomial_truncations
          a hq' hqq' hF hne htrunc
  · have hzero : F =ᶠ[𝓝 (0 : ComplexModel n)] (fun _ => (0 : ℂ)) := by
      filter_upwards [Filter.not_frequently.mp hne] with z hz
      exact not_ne_iff.mp hz
    exact (multiplierIntegrableAt_zero _ hq' (0 : ComplexModel n) volume).congr
      EventuallyEq.rfl hzero.symm

end
end SGPT.Foundations.Analysis.Pending.StrictMonomialTruncationAllDimensions
