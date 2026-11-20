import SGPT.Foundations.Analysis.Pending.WeightedNormalTestJacobianLineOrder
import SGPT.Foundations.Analysis.Pending.WeightedTruncatedGeneratorGrowth
import SGPT.Foundations.Analysis.Pending.CoordinateLineUnitMultiplierBound
import SGPT.Foundations.Analysis.Pending.AnalyticSingularities

set_option autoImplicit false

/-! # Actual truncated integrals force the strict normal threshold -/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.WeightedTruncationNormalThreshold

open FirstPass HolomorphicGermReducednessBridge DivisorialChangeOfVariables
  WeightedAffineMonomialMultiplierPullback

noncomputable section

private theorem normal_bound_of_weighted_inequalities {q : ℝ} {a b k m : ℕ}
    (h : ∀ L : ℕ, k < L →
      q * ((L * a : ℕ) : ℝ) < ((L * b + k + L + m : ℕ) : ℝ) + 1) :
    q * (a : ℝ) ≤ (b : ℝ) + 1 := by
  by_contra hn
  have hgap : 0 < q * (a : ℝ) - ((b : ℝ) + 1) := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨L, hL⟩ := exists_nat_gt
    (max (k : ℝ) (((k : ℝ) + (m : ℝ) + 1) /
      (q * (a : ℝ) - ((b : ℝ) + 1))))
  have hkL : k < L := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hL)
  have hlarge : (k : ℝ) + (m : ℝ) + 1 <
      (L : ℝ) * (q * (a : ℝ) - ((b : ℝ) + 1)) :=
    (div_lt_iff₀ hgap).mp (lt_of_le_of_lt (le_max_right _ _) hL)
  have hsmall := h L hkL
  push_cast at hsmall
  nlinarith

private theorem psh_generatorLog_of_near_holomorphic {n r : ℕ}
    (Q : Fin r → ComplexModel n → ℂ)
    (hQ : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (Q i) z) :
    PlurisubharmonicAt (generatorLog Q) 0 := by
  have hall : ∀ᶠ z in 𝓝 (0 : ComplexModel n), ∀ i, DifferentiableAt ℂ (Q i) z :=
    Filter.eventually_all.mpr hQ
  obtain ⟨U, hsub, hU, h0⟩ := _root_.mem_nhds_iff.mp hall
  have hgen : HolomorphicGeneratorsAt Q 0 :=
    ⟨U, hU, h0, fun i z hz => (hsub hz i).differentiableWithinAt⟩
  simpa only [EReal.coe_one, one_mul] using
    plurisubharmonicAt_scaled_generatorLog hgen (by norm_num : (0 : ℝ) < 1)

/-- Actual source integrals for all point truncations force the strict normal
threshold after lowering the level; the original test supplies every order. -/
theorem exists_normal_factor_with_strict_threshold {m : ℕ} (a : ℕ) {q : ℝ}
    {F : ComplexModel (m + 2) → ℂ}
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), DifferentiableAt ℂ F z)
    (hne : ∃ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), F z ≠ 0)
    (htrunc : ∀ N : ℕ, ∃ (r : ℕ) (Q : Fin r → ComplexModel (m + 2) → ℂ)
      (hQ : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), DifferentiableAt ℂ (Q i) z),
      (∀ i, HolGerm.mk (Q i) (hQ i) ∈
        Ideal.span {HolGerm.mk (fun z : ComplexModel (m + 2) => z (Fin.last (m + 1)))
          (eventually_differentiableAt_coordinate (Fin.last (m + 1))) ^ a} ⊔
        (Ideal.span (Set.range fun i : Fin (m + 2) => HolGerm.mk
          (fun z : ComplexModel (m + 2) => z i) (eventually_differentiableAt_coordinate i))) ^ N) ∧
      MultiplierIntegrableAt (generatorLog Q) q F 0 volume) :
    ∃ (b : ℕ) (H : ComplexModel (m + 2) → ℂ),
      (∀ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), DifferentiableAt ℂ H z) ∧
      F =ᶠ[𝓝 0] (fun z => z (Fin.last (m + 1)) ^ b * H z) ∧
      (∃ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), z (Fin.last (m + 1)) = 0 ∧ H z ≠ 0) ∧
      ∀ q' : ℝ, q' < q → q' * (a : ℝ) < (b : ℝ) + 1 := by
  classical
  let j : Fin (m + 2) := Fin.last (m + 1)
  let av : Fin (m + 2) → ℕ := fun i => if i = j then a else 0
  obtain ⟨b, H, hH, hfact, hfreq, k, p, c, hpj, hcj, hcp, hlines⟩ :=
    WeightedNormalTestJacobianLineOrder.exists_charts_before_all_weighted_jacobian_line_orders hF hne
  refine ⟨b, H, hH, hfact, hfreq, ?_⟩
  have hweighted (L : ℕ) (hL : k < L) :
      q * ((L * a : ℕ) : ℝ) < ((L * b + k + L + m : ℕ) : ℝ) + 1 := by
    let w : Fin (m + 2) → ℕ := fun i => if i = j then L else 1
    let T : ComplexModel (m + 2) → ComplexModel (m + 2) := affineMonomial w c p
    have hLpos : 0 < L := lt_of_le_of_lt (Nat.zero_le k) hL
    have hw : ∀ i, i ≠ p → 1 ≤ w i := by
      intro i _
      dsimp [w]
      split_ifs
      · exact hLpos
      · rfl
    have hdegree : ∑ i, (if i = p then 1 else w i) * av i = L * a := by
      have hjp : j ≠ p := Ne.symm hpj
      calc
        _ = (if j = p then 1 else w j) * av j := by
          apply Finset.sum_eq_single j
          · intro i _ hij
            simp [av, hij]
          · simp
        _ = _ := by simp [w, av, hjp]
    have hT0 : T 0 = 0 := by
      ext i
      by_cases hip : i = p
      · simp [T, affineMonomial, hip]
      · have hiw : w i ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) (hw i hip))
        simp [T, affineMonomial, hip, zero_pow hiw]
    obtain ⟨r, Q, hQ, hmem, hint⟩ := htrunc (L * a)
    have hmon (hM : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 2)),
        DifferentiableAt ℂ (fun z : ComplexModel (m + 2) => ∏ i, z i ^ av i) z) :
        HolGerm.mk (fun z : ComplexModel (m + 2) => ∏ i, z i ^ av i) hM =
          HolGerm.mk (fun z : ComplexModel (m + 2) => z j)
            (eventually_differentiableAt_coordinate j) ^ a := by
      calc
        _ = HolGerm.mk (fun z : ComplexModel (m + 2) => z j ^ a)
            (eventually_differentiableAt_pow (eventually_differentiableAt_coordinate j) a) := by
          apply HolGerm.mk_eq_mk_iff.mpr
          filter_upwards with z
          calc
            _ = z j ^ av j := by
              apply Finset.prod_eq_single j
              · intro i _ hij
                simp [av, hij]
              · simp
            _ = _ := by simp [av]
        _ = _ := HolGerm.mk_pow (fun z : ComplexModel (m + 2) => z j)
          (eventually_differentiableAt_coordinate j) a
    obtain ⟨C, hupper⟩ :=
      WeightedTruncatedGeneratorGrowth.exists_log_upper_of_truncated_ideal_membership
        p av w c hw (L * a) hdegree.le Q hQ (by
          intro i
          rw [hmon]
          exact hmem i)
    have hψ : QuasiPlurisubharmonicAt (generatorLog Q) (T 0) := by
      rw [hT0]
      exact (psh_generatorLog_of_near_holomorphic Q hQ).quasiPlurisubharmonicAt
    have hintT : MultiplierIntegrableAt (generatorLog Q) q F (T 0) volume := by
      simpa only [hT0] using hint
    have hpull := multiplierIntegrableAt_comp_affineMonomial w c p hψ hintT
    have hJac := (geometry_affineMonomial w c p).2.1
    have hpull' : MultiplierIntegrableAt (fun z => generatorLog Q (T z)) q
        (fun z => F (T z) * complexJacobian T z) 0 volume := by
      simpa only [T, hJac] using hpull
    obtain ⟨u, hu, hu0, hline⟩ := hlines L hL
    apply CoordinateLineUnitMultiplierBound.threshold_of_integrability_and_line_unit
      p (by positivity : (0 : ℝ) ≤ ((L * a : ℕ) : ℝ)) hpull'
      (by
        refine ⟨C, ?_⟩
        simpa only [generatorLog, generatorVector, Function.comp_apply, T, hdegree,
          EReal.coe_natCast] using hupper) hu hu0
    exact hline
  have hnormal := normal_bound_of_weighted_inequalities hweighted
  intro q' hq'
  by_cases ha : a = 0
  · simp only [ha, Nat.cast_zero, mul_zero]
    positivity
  · exact (mul_lt_mul_of_pos_right hq' (by exact_mod_cast Nat.pos_of_ne_zero ha)).trans_le hnormal

end
end SGPT.Foundations.Analysis.Pending.WeightedTruncationNormalThreshold
