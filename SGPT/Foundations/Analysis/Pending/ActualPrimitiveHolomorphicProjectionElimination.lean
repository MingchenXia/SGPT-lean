import SGPT.Foundations.Analysis.Pending.ActualPrimitiveWeierstrassElimination
import SGPT.Foundations.Analysis.Pending.HolomorphicZeroSetNull

set_option autoImplicit false

/-! # Actual local projection nullity from origin-primitive germs

The natural regular last axis and original primitive germs produce
actual Weierstrass remainders, elimination into their original ideal,
and a genuine Haar-null projection.  No nearby primitivity is assumed.
-/

noncomputable section
open Set Filter Metric MeasureTheory Polynomial
open scoped Topology ENNReal
namespace SGPT.Foundations.Analysis.Pending.ActualPrimitiveHolomorphicProjectionElimination
open HolGerm OkaGermRelations HolomorphicGermWeierstrassPreparation
open ActualPrimitiveWeierstrassElimination

/-- The natural regular last axis and original primitive germs produce
an actual nonzero pulled-back base germ in the original germ ideal. -/
theorem exists_nonzero_ofFst_mem_span {n N : ℕ}
    (f : Fin N → EuclideanSpace ℂ (Fin n) × ℂ → ℂ)
    (hf : ∀ i, ∀ᶠ x in 𝓝 (0 : EuclideanSpace ℂ (Fin n) × ℂ),
      DifferentiableAt ℂ (f i) x) (k : Fin N)
    (haxis : ¬ ∀ᶠ t : ℂ in 𝓝 0, f k (0, t) = 0)
    (hprimitive : ∀ q : HolGerm (EuclideanSpace ℂ (Fin n) × ℂ),
      (∀ i, q ∣ HolGerm.mk (f i) (hf i)) → IsUnit q) :
    ∃ r : HolGerm (EuclideanSpace ℂ (Fin n)), r ≠ 0 ∧
      ofFst r ∈ Ideal.span (Set.range (fun i => HolGerm.mk (f i) (hf i))) := by
  classical
  have hline : AnalyticAt ℂ (fun t : ℂ => f k (0, t)) 0 := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    simpa only [Function.comp_def, ContinuousLinearMap.inr_apply] using
      eventually_differentiableAt_comp_clm
        (ContinuousLinearMap.inr ℂ (EuclideanSpace ℂ (Fin n)) ℂ) (hf k)
  obtain ⟨d, u, hu, hu0, hpow⟩ :=
    hline.exists_eventuallyEq_pow_smul_nonzero_iff.mpr haxis
  have hpow' : ∀ᶠ t : ℂ in 𝓝 0, f k (0, t) = t ^ d * u t := by
    simpa only [smul_eq_mul, sub_zero] using hpow
  obtain ⟨q, hq, hq0, a, ha, ha0, hprep⟩ :=
    exists_weierstrass_preparation (hf k) hu hu0 hpow'
  let A : ℕ → HolGerm (EuclideanSpace ℂ (Fin n)) := fun j => mk (a j) (ha j)
  let W : (HolGerm (EuclideanSpace ℂ (Fin n)))[X] :=
    X ^ d + ∑ j ∈ Finset.range d, C (A j) * X ^ j
  obtain ⟨hW, hd⟩ := AnalyticProjectionWeierstrass.monic_X_pow_add_sum d A
  have hW0 : ∀ j < W.natDegree, HolGerm.eval (W.coeff j) = 0 := by
    intro j hj
    rw [hd] at hj
    have hc : W.coeff j = A j := by
      simp [W, coeff_add, coeff_X_pow, Nat.ne_of_lt hj, hj]
    rw [hc, HolGerm.eval_mk]
    exact ha0 j hj
  have hPW : shiftEval 0 W = mk q hq * mk (f k) (hf k) := by
    have he : shiftEval 0 W = prodWeierstrassGerm d A := by
      simp only [W, shiftEval, map_zero, add_zero, coe_eval₂RingHom,
        eval₂_add, eval₂_X_pow, eval₂_finsetSum, eval₂_mul, eval₂_C,
        prodWeierstrassGerm]
    rw [he, prodWeierstrassGerm_eq_mk, ← mk_mul, mk_eq_mk_iff]
    exact hprep.symm
  choose c R hRdeg hdiv using fun i => exists_eq_mul_shiftEval_add hW hW0 (mk (f i) (hf i))
  let P : Fin (N + 1) → (HolGerm (EuclideanSpace ℂ (Fin n)))[X] := Fin.cases W R
  have hprimP : ∀ b : HolGerm (EuclideanSpace ℂ (Fin n) × ℂ),
      (∀ i, b ∣ shiftEval 0 (P i)) → IsUnit b := by
    intro b hb
    apply hprimitive b
    intro i
    rw [hdiv i]
    exact (dvd_mul_of_dvd_right (hb 0) (c i)).add (hb i.succ)
  obtain ⟨r, hr, hmem⟩ := exists_nonzero_constant_mem_span P 0 hW hW0 hprimP
  let J := Ideal.span (Set.range (fun i => mk (f i) (hf i)))
  have hWJ : shiftEval 0 W ∈ J := by
    rw [hPW]
    exact J.mul_mem_left _ (Ideal.subset_span ⟨k, rfl⟩)
  have hle : Ideal.map (shiftEval 0) (Ideal.span (Set.range P)) ≤ J := by
    rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change shiftEval 0 (P i) ∈ J
    refine Fin.cases hWJ (fun j => ?_) i
    have he : shiftEval 0 (R j) = mk (f j) (hf j) - c j * shiftEval 0 W := by
      rw [hdiv j]
      ring
    rw [show P j.succ = R j from rfl, he]
    exact J.sub_mem (Ideal.subset_span ⟨j, rfl⟩) (J.mul_mem_left _ hWJ)
  refine ⟨r, hr, ?_⟩
  have hm := hle (Ideal.mem_map_of_mem (shiftEval 0) hmem)
  simpa only [shiftEval, coe_eval₂RingHom, eval₂_C] using hm

/-- Original origin-primitive germs, with a natural regular last axis,
internally produce an actual small product whose common-zero projection
has outer Haar measure zero. -/
theorem exists_product_projection_common_zero_null {n N : ℕ}
    (f : Fin N → EuclideanSpace ℂ (Fin n) × ℂ → ℂ)
    (hf : ∀ i, ∀ᶠ x in 𝓝 (0 : EuclideanSpace ℂ (Fin n) × ℂ),
      DifferentiableAt ℂ (f i) x) (k : Fin N)
    (haxis : ¬ ∀ᶠ t : ℂ in 𝓝 0, f k (0, t) = 0)
    (hprimitive : ∀ q : HolGerm (EuclideanSpace ℂ (Fin n) × ℂ),
      (∀ i, q ∣ HolGerm.mk (f i) (hf i)) → IsUnit q) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ ε : ℝ, 0 < ε ∧
      volume (Prod.fst '' {x : EuclideanSpace ℂ (Fin n) × ℂ |
        x.1 ∈ ball 0 δ ∧ x.2 ∈ ball 0 ε ∧ ∀ i, f i x = 0}) = 0 := by
  classical
  obtain ⟨r, hr, hmem⟩ := exists_nonzero_ofFst_mem_span f hf k haxis hprimitive
  obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  obtain ⟨R, hR, rfl⟩ := HolGerm.exists_eq_mk r
  choose B hB hBeq using fun i => HolGerm.exists_eq_mk (b i)
  have hprod (i : Fin N) : ∀ᶠ x in 𝓝 (0 : EuclideanSpace ℂ (Fin n) × ℂ),
      DifferentiableAt ℂ (fun x => B i x * f i x) x :=
    eventually_differentiableAt_mul (hB i) (hf i)
  have hsum := HolGerm.mk_sum Finset.univ (fun i x => B i x * f i x) hprod
  have he : (fun x : EuclideanSpace ℂ (Fin n) × ℂ => R x.1) =ᶠ[𝓝 0]
      fun x => ∑ i, B i x * f i x := by
    apply (HolGerm.mk_eq_mk_iff
      (hf := eventually_differentiableAt_comp_clm
        (ContinuousLinearMap.fst ℂ (EuclideanSpace ℂ (Fin n)) ℂ) hR)
      (hg := eventually_differentiableAt_sum Finset.univ hprod)).mp
    change ofFst (mk R hR) = _
    rw [hsum, ← hb]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hBeq i]
    rfl
  obtain ⟨ρ, hρ, hρball⟩ := Metric.eventually_nhds_iff_ball.mp he
  obtain ⟨σ, hσ, hσball⟩ := Metric.eventually_nhds_iff_ball.mp hR
  let δ := min ρ σ
  have hδ : 0 < δ := lt_min hρ hσ
  have hdiff : DifferentiableOn ℂ R (ball 0 δ) := fun z hz =>
    (hσball z (ball_subset_ball (min_le_right _ _) hz)).differentiableWithinAt
  have hnot : ¬ ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℂ (Fin n)), R z = 0 := by
    intro hz
    apply hr
    rw [← HolGerm.mk_zero]
    exact HolGerm.mk_eq_mk_iff.mpr hz
  have hfreq : ∃ᶠ z in 𝓝 (0 : EuclideanSpace ℂ (Fin n)), R z ≠ 0 :=
    Filter.not_eventually.mp hnot
  obtain ⟨z, hzR, hzδ⟩ := (hfreq.and_eventually (ball_mem_nhds _ hδ)).exists
  have hnull := HolomorphicZeroSetNull.measure_ball_inter_preimage_zero_eq_zero
    volume hdiff hzδ hzR
  refine ⟨δ, hδ, ρ, hρ, measure_mono_null ?_ hnull⟩
  rintro _ ⟨x, ⟨hxδ, hxρ, hxzero⟩, rfl⟩
  refine ⟨hxδ, ?_⟩
  have hx : x ∈ ball (0 : EuclideanSpace ℂ (Fin n) × ℂ) ρ := by
    rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff]
    exact ⟨(mem_ball_zero_iff.mp hxδ).trans_le (min_le_left _ _),
      mem_ball_zero_iff.mp hxρ⟩
  have hz : R x.1 = 0 := (hρball x hx).trans (Finset.sum_eq_zero fun i _ => by
    rw [hxzero i, mul_zero])
  exact hz

end SGPT.Foundations.Analysis.Pending.ActualPrimitiveHolomorphicProjectionElimination
