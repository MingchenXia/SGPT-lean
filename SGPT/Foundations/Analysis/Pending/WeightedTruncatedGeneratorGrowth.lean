import SGPT.Foundations.Analysis.Pending.WeightedAffineMonomialMultiplierPullback
import SGPT.Foundations.Analysis.Pending.HolomorphicIdealPowerGeneratorBound
import SGPT.Foundations.Analysis.FirstPass.AnalyticSingularities

set_option autoImplicit false

/-! # Actual truncated germ ideals supply weighted monomial growth -/

open Set Filter Metric
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.WeightedTruncatedGeneratorGrowth

open FirstPass HolomorphicGermReducednessBridge WeightedAffineMonomialMultiplierPullback

noncomputable section

private theorem near_monomial {n : ℕ} (a : Fin n → ℕ) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      DifferentiableAt ℂ (fun z : ComplexModel n => ∏ i, z i ^ a i) z := by
  have hprod (s : Finset (Fin n)) (z : ComplexModel n) :
      DifferentiableAt ℂ (fun z : ComplexModel n => ∏ i ∈ s, z i ^ a i) z := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using (differentiableAt_const (c := (1 : ℂ)))
    | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact ((EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt.pow (a i)).mul ih
  exact Eventually.of_forall (hprod Finset.univ)

private theorem exists_norm_bound_of_truncated_mem {n : ℕ} (a : Fin n → ℕ) (N : ℕ)
    {Q : ComplexModel n → ℂ}
    (hQ : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ Q z)
    (hmem : HolGerm.mk Q hQ ∈
      Ideal.span {HolGerm.mk (fun z : ComplexModel n => ∏ i, z i ^ a i) (near_monomial a)} ⊔
        (Ideal.span (Set.range fun i : Fin n => HolGerm.mk
          (fun z : ComplexModel n => z i) (eventually_differentiableAt_coordinate i))) ^ N) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      ‖Q z‖ ≤ C * ‖∏ i, z i ^ a i‖ + D * (∑ i, ‖z i‖) ^ N := by
  obtain ⟨g, hg, h, hh, heq⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨G, hG, rfl⟩ := HolGerm.exists_eq_mk g
  obtain ⟨H, hH, rfl⟩ := HolGerm.exists_eq_mk h
  have hGp : HolGerm.mk G hG ∈
      (Ideal.span (Set.range fun _ : Fin 1 => HolGerm.mk
        (fun z : ComplexModel n => ∏ i, z i ^ a i) (near_monomial a))) ^ 1 := by
    simpa only [Set.range_const, pow_one] using hg
  obtain ⟨C, hC, hCb⟩ := HolomorphicIdealPowerGeneratorBound.exists_norm_bound_of_mem_span_pow
    (fun _ : Fin 1 => fun z : ComplexModel n => ∏ i, z i ^ a i)
    (fun _ => near_monomial a) G hG 1 hGp
  have hCbound : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      ‖G z‖ ≤ C * ‖∏ i, z i ^ a i‖ := by
    simpa only [Fin.sum_univ_one, pow_one] using hCb
  obtain ⟨D, hD, hDb⟩ := HolomorphicIdealPowerGeneratorBound.exists_norm_bound_of_mem_span_pow
    (fun i : Fin n => fun z : ComplexModel n => z i)
    eventually_differentiableAt_coordinate H hH N hh
  have hfun : Q =ᶠ[𝓝 (0 : ComplexModel n)] (fun z => G z + H z) :=
    HolGerm.mk_eq_mk_iff.mp (heq.symm.trans (HolGerm.mk_add G H hG hH).symm)
  refine ⟨C, D, hC, hD, ?_⟩
  filter_upwards [hfun, hCbound, hDb] with z hz hcz hdz
  rw [hz]
  exact (norm_add_le _ _).trans (add_le_add hcz hdz)

private theorem exists_weighted_norm_bounds {n : ℕ} (p : Fin n)
    (a w : Fin n → ℕ) (v : ComplexModel n) (hw : ∀ i, i ≠ p → 1 ≤ w i) :
    let A := ∑ i, (if i = p then 1 else w i) * a i
    ∃ B D : ℝ, 0 ≤ B ∧ 0 ≤ D ∧ ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      (∑ i, ‖affineMonomial w v p z i‖) ≤ B * ‖z p‖ ∧
      ‖∏ i, (affineMonomial w v p z) i ^ a i‖ ≤ D * ‖z p‖ ^ A ∧ ‖z p‖ ≤ 1 := by
  classical
  dsimp only
  let e : Fin n → ℕ := fun i => if i = p then 1 else w i
  let b : Fin n → ℝ := fun i => if i = p then 1 else ‖v i‖ + 1
  let B : ℝ := ∑ i, b i
  let D : ℝ := ∏ i, b i ^ a i
  have hb : ∀ i, 0 ≤ b i := fun i => by dsimp [b]; split_ifs <;> positivity
  refine ⟨B, D, Finset.sum_nonneg (fun i _ => hb i),
    Finset.prod_nonneg (fun i _ => pow_nonneg (hb i) _), ?_⟩
  have hsmall : ∀ᶠ z in 𝓝 (0 : ComplexModel n), ‖z‖ < 1 := by
    filter_upwards [ball_mem_nhds (0 : ComplexModel n)
      (by norm_num : (0 : ℝ) < 1)] with z hz
    exact mem_ball_zero_iff.mp hz
  filter_upwards [hsmall] with z hz
  have hr : ‖z p‖ ≤ 1 := (PiLp.norm_apply_le z p).trans hz.le
  have hcomponent (i : Fin n) :
      ‖affineMonomial w v p z i‖ ≤ ‖z p‖ ^ e i * b i := by
    by_cases hip : i = p
    · subst i
      simp [affineMonomial, e, b]
    · simp only [affineMonomial, PiLp.toLp_apply, e, b, if_neg hip]
      rw [norm_mul, norm_pow]
      gcongr
      exact (norm_add_le _ _).trans
        (add_le_add le_rfl ((PiLp.norm_apply_le z i).trans hz.le))
  have hsum : (∑ i, ‖affineMonomial w v p z i‖) ≤ B * ‖z p‖ := by
    calc
      _ ≤ ∑ i, ‖z p‖ * b i := by
        apply Finset.sum_le_sum
        intro i _
        apply (hcomponent i).trans
        apply mul_le_mul_of_nonneg_right _ (hb i)
        have he : 1 ≤ e i := by dsimp [e]; split_ifs with hi; rfl; exact hw i hi
        simpa only [pow_one] using pow_le_pow_of_le_one (norm_nonneg (z p)) hr he
      _ = _ := by
        dsimp only [B]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        exact mul_comm _ _
  have hmono : ‖∏ i, (affineMonomial w v p z) i ^ a i‖ ≤
      D * ‖z p‖ ^ (∑ i, e i * a i) := by
    calc
      _ = ∏ i, ‖affineMonomial w v p z i‖ ^ a i := by simp only [norm_prod, norm_pow]
      _ ≤ ∏ i, (‖z p‖ ^ e i * b i) ^ a i := by
        apply Finset.prod_le_prod
        · intro i _; exact pow_nonneg (norm_nonneg _) _
        · intro i _; exact pow_le_pow_left₀ (norm_nonneg _) (hcomponent i) _
      _ = D * ‖z p‖ ^ (∑ i, e i * a i) := by
        simp_rw [mul_pow, ← pow_mul]
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
        exact mul_comm _ _
  exact ⟨hsum, hmono, hr⟩

private theorem log_upper_of_square_bound {r n A : ℕ} (Q : Fin r → ComplexModel n → ℂ)
    (y z : ComplexModel n) (p : Fin n) {K : ℝ} (hK : 0 < K)
    (hbound : (∑ i, ‖Q i y‖ ^ 2) ≤ K * (‖z p‖ ^ A) ^ 2) :
    generatorLog Q y ≤ (A : EReal) * logNormSq (z p) + (Real.log K : EReal) := by
  have hsnon : 0 ≤ ∑ i, ‖Q i y‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases hs0 : (∑ i, ‖Q i y‖ ^ 2) = 0
  · rw [generatorLog_eq_log_sum, hs0, ENNReal.ofReal_zero, ENNReal.log_zero]
    exact bot_le
  have hspos : 0 < ∑ i, ‖Q i y‖ ^ 2 := lt_of_le_of_ne hsnon (Ne.symm hs0)
  by_cases hz : z p = 0
  · have hA : A = 0 := by
      by_contra ha
      have hb : (∑ i, ‖Q i y‖ ^ 2) ≤ 0 := by
        simpa only [hz, norm_zero, zero_pow ha, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
          mul_zero] using hbound
      exact (not_lt_of_ge hb hspos).elim
    rw [generatorLog_eq_log_sum, ENNReal.log_ofReal_of_pos hspos]
    simp only [hA, Nat.cast_zero, zero_mul, zero_add]
    apply EReal.coe_le_coe_iff.mpr
    apply Real.log_le_log hspos
    simpa only [hA, pow_zero, one_pow, mul_one] using hbound
  · have hnorm : 0 < ‖z p‖ := norm_pos_iff.mpr hz
    have hpow : 0 < (‖z p‖ ^ A) ^ 2 := pow_pos (pow_pos hnorm _) _
    have hlog := Real.log_le_log hspos hbound
    rw [Real.log_mul hK.ne' hpow.ne', Real.log_pow, Real.log_pow] at hlog
    rw [generatorLog_eq_log_sum, ENNReal.log_ofReal_of_pos hspos,
      logNormSq_of_ne_zero hz, Real.log_pow, ← EReal.coe_natCast,
      ← EReal.coe_mul, ← EReal.coe_add]
    apply EReal.coe_le_coe_iff.mpr
    nlinarith [hlog]

/-- Actual membership of every original generator in the monomial principal
ideal plus a coordinate-ideal power internally supplies the all-point bound. -/
theorem exists_log_upper_of_truncated_ideal_membership {n r : ℕ} (p : Fin n)
    (a w : Fin n → ℕ) (v : ComplexModel n) (hw : ∀ i, i ≠ p → 1 ≤ w i)
    (N : ℕ) (hN : (∑ i, (if i = p then 1 else w i) * a i) ≤ N)
    (Q : Fin r → ComplexModel n → ℂ)
    (hQ : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (Q i) z)
    (hmem : ∀ j, HolGerm.mk (Q j) (hQ j) ∈
      Ideal.span {HolGerm.mk (fun z : ComplexModel n => ∏ i, z i ^ a i) (near_monomial a)} ⊔
        (Ideal.span (Set.range fun i : Fin n => HolGerm.mk
          (fun z : ComplexModel n => z i) (eventually_differentiableAt_coordinate i))) ^ N) :
    ∃ C : ℝ, ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      generatorLog (fun i => (Q i) ∘ affineMonomial w v p) z ≤
        ((∑ i, (if i = p then 1 else w i) * a i : ℕ) : EReal) * logNormSq (z p) + (C : EReal) := by
  classical
  let A : ℕ := ∑ i, (if i = p then 1 else w i) * a i
  let T : ComplexModel n → ComplexModel n := affineMonomial w v p
  have hT0 : T 0 = 0 := by
    ext i
    by_cases hip : i = p
    · simp [T, affineMonomial, hip]
    · have hw0 : w i ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) (hw i hip))
      simp [T, affineMonomial, hip, zero_pow hw0]
  have hT : Tendsto T (𝓝 0) (𝓝 0) := by
    have hc : Tendsto T (𝓝 0) (𝓝 (T 0)) :=
      (geometry_affineMonomial w v p).1.continuous.continuousAt.tendsto
    rw [hT0] at hc
    exact hc
  obtain ⟨B, D, hB, hD, hbounds⟩ := exists_weighted_norm_bounds p a w v hw
  choose C E hC hE hbound using fun j => exists_norm_bound_of_truncated_mem a N (hQ j) (hmem j)
  let K : Fin r → ℝ := fun j => C j * D + E j * B ^ N
  have hfamily : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      ∀ j, ‖Q j (T z)‖ ≤ K j * ‖z p‖ ^ A := by
    apply Filter.eventually_all.mpr
    intro j
    filter_upwards [hT.eventually (hbound j), hbounds] with z hz hb
    calc
      _ ≤ C j * ‖∏ i, (T z) i ^ a i‖ + E j * (∑ i, ‖T z i‖) ^ N := hz
      _ ≤ C j * (D * ‖z p‖ ^ A) + E j * (B * ‖z p‖) ^ N := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ (hC j)
          simpa only [T, A] using hb.2.1
        · apply mul_le_mul_of_nonneg_left _ (hE j)
          apply pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _) _ N
          simpa only [T] using hb.1
      _ = C j * D * ‖z p‖ ^ A + E j * B ^ N * ‖z p‖ ^ N := by rw [mul_pow]; ring
      _ ≤ C j * D * ‖z p‖ ^ A + E j * B ^ N * ‖z p‖ ^ A := by
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hE j) (pow_nonneg hB N))
        exact pow_le_pow_of_le_one (norm_nonneg _) hb.2.2 hN
      _ = _ := by dsimp only [K]; ring
  let Kall : ℝ := (∑ j, (K j) ^ 2) + 1
  have hKall : 0 < Kall := by dsimp only [Kall]; positivity
  refine ⟨Real.log Kall, ?_⟩
  filter_upwards [hfamily] with z hz
  have hsq : (∑ j, ‖Q j (T z)‖ ^ 2) ≤ Kall * (‖z p‖ ^ A) ^ 2 := by
    calc
      _ ≤ ∑ j, (K j * ‖z p‖ ^ A) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact pow_le_pow_left₀ (norm_nonneg _) (hz j) _
      _ = (∑ j, (K j) ^ 2) * (‖z p‖ ^ A) ^ 2 := by
        simp_rw [mul_pow]
        rw [Finset.sum_mul]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right (by dsimp only [Kall]; linarith)
        positivity
  simpa only [generatorLog, generatorVector, Function.comp_apply, T, A] using
    log_upper_of_square_bound Q (T z) z p hKall hsq

end
end SGPT.Foundations.Analysis.Pending.WeightedTruncatedGeneratorGrowth
