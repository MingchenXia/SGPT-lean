import SGPT.GAGA.SerreHomogeneous
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Holomorphic functions on a ball agreeing with a homogeneous function on a cone


Let `C ⊆ ℂ^m` be a cone (`c • Z ∈ C` for `Z ∈ C`, `c ∈ ℂ`) and `F` a function which is
homogeneous of degree `k > 0` on `C` (`F (c • Z) = c^k F(Z)`), i.e. a section of `𝒪(k)` over the
projectivization of `C`.  If a holomorphic function `H` on a ball `B(0, R)` agrees with `F` on
`C ∩ B(0, R) ∖ {0}`, then the degree-`k` Taylor term of `H` at `0` is a homogeneous polynomial
`P` of degree `k` with `P = F` on all of `C` (`exists_isHomogeneous_eq_on_cone`).

Proof: for `W ∈ C` small, the one-variable function `t ↦ H(t W)` equals `t^k F(W)` near `0`, so
by uniqueness of one-variable power series the `k`-th coefficient of `H` along `W`, which is
`p_k(W, …, W)` for the Taylor series `p` of `H` at `0` (TN `hasFPowerSeriesOnBall_of_differentiableOn`),
is `F(W)`; homogeneity removes the smallness of `W`, and the diagonal of `p_k` is a homogeneous
polynomial (`SGPT.GAGA.exists_isHomogeneous_eval_eq_diag`).
-/

set_option autoImplicit false

open Filter Topology Metric
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

namespace SGPT.GAGA.H0

noncomputable section

variable {m : ℕ}

/-- The monomial `t ↦ b t^k` is represented by the power series with the single coefficient `b`
in degree `k`. -/
theorem hasFPowerSeriesOnBall_monomial (k : ℕ) (b : ℂ) :
    HasFPowerSeriesOnBall (fun t : ℂ => b * t ^ k)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => if n = k then b else 0)) 0 ⊤ where
  r_le := by
    rw [FormalMultilinearSeries.radius_eq_top_of_forall_image_add_eq_zero _ (k + 1) (fun j => ?_)]
    exact FormalMultilinearSeries.ofScalars_eq_zero_of_scalar_zero _ (by
      simp only [ite_eq_right_iff]; intro h; omega)
  r_pos := ENNReal.zero_lt_top
  hasSum := by
    intro y _
    rw [zero_add, FormalMultilinearSeries.ofScalars_apply_eq']
    have h := hasSum_single (f := fun n : ℕ => (if n = k then b else 0) • y ^ n) k
      (fun n hn => by simp [hn])
    simpa using h

/-- **Taylor extraction on a cone.** Let `H` be holomorphic on `B(0, R) ⊆ ℂ^m`, `C` a cone and
`F` homogeneous of degree `k > 0` on `C`. If `H = F` on `C ∩ B(0, R) ∖ {0}`, there is a homogeneous
polynomial `P` of degree `k` with `P = F` on `C`. -/
theorem exists_isHomogeneous_eq_on_cone {R : ℝ} (hR : 0 < R) {H F : ComplexModel m → ℂ}
    (hH : DifferentiableOn ℂ H (ball 0 R)) {C : Set (ComplexModel m)}
    (hC : ∀ (c : ℂ) (Z : ComplexModel m), Z ∈ C → c • Z ∈ C) {k : ℕ} (hk : 0 < k)
    (hF : ∀ (c : ℂ) (Z : ComplexModel m), Z ∈ C → F (c • Z) = c ^ k * F Z)
    (hHF : ∀ Z ∈ C, Z ∈ ball (0 : ComplexModel m) R → Z ≠ 0 → H Z = F Z) :
    ∃ P : MvPolynomial (Fin m) ℂ, P.IsHomogeneous k ∧
      ∀ Z ∈ C, MvPolynomial.eval (fun i => Z i) P = F Z := by
  set R' : ℝ := R / 2 with hR'
  have hR'0 : 0 < R' := by positivity
  have hR'R : R' < R := by rw [hR']; linarith
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ComplexModel m) R').exists_bound_of_continuousOn
    (hH.continuousOn.mono (closedBall_subset_ball hR'R))
  have hser := HolomorphicAnalytic.hasFPowerSeriesOnBall_of_differentiableOn hR'0
    (hH.mono (ball_subset_ball hR'R.le)) (fun w hw => hM w (ball_subset_closedBall hw))
  set p : FormalMultilinearSeries ℂ (ComplexModel m) ℂ :=
    fun n => (n.factorial : ℂ)⁻¹ • iteratedFDeriv ℂ n H 0 with hp
  set ρ : ℝ := R' / Real.exp 1 with hρ
  have hρ0 : 0 < ρ := div_pos hR'0 (Real.exp_pos 1)
  have hρR : ρ < R := by
    have : ρ ≤ R' := div_le_self hR'0.le (by
      have := Real.add_one_le_exp (1 : ℝ); linarith)
    linarith
  -- the coefficient identity for small `W`
  have hsmall : ∀ W ∈ C, W ≠ 0 → ‖W‖ < ρ → p k (fun _ => W) = F W := by
    intro W hWC hW0 hWρ
    let L : ℂ →L[ℂ] ComplexModel m := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) W
    have hL : ∀ t : ℂ, L t = t • W := fun t => rfl
    have hL0 : L 0 = 0 := by rw [hL, zero_smul]
    have h1 : HasFPowerSeriesAt (H ∘ L) (p.compContinuousLinearMap L) 0 := by
      have h := hser.hasFPowerSeriesAt
      rw [← hL0] at h
      exact h.compContinuousLinearMap
    have h2 : HasFPowerSeriesAt (fun t : ℂ => F W * t ^ k)
        (FormalMultilinearSeries.ofScalars ℂ (fun n => if n = k then F W else 0)) 0 :=
      (hasFPowerSeriesOnBall_monomial k (F W)).hasFPowerSeriesAt
    -- `H (t W) = F(W) t^k` for small `t`
    have hcontH : ContinuousAt (H ∘ L) 0 := by
      have hc : ContinuousAt H (L 0) := by
        rw [hL0]
        exact hH.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hR))
      exact hc.comp L.continuous.continuousAt
    have hnorm : ∀ t : ℂ, ‖t‖ < 1 → ‖t • W‖ < ρ := by
      intro t ht
      rw [norm_smul]
      calc ‖t‖ * ‖W‖ ≤ 1 * ‖W‖ := by gcongr
        _ < ρ := by rw [one_mul]; exact hWρ
    have hpunct : ∀ t : ℂ, ‖t‖ < 1 → t ≠ 0 → (H ∘ L) t = F W * t ^ k := by
      intro t ht ht0
      simp only [Function.comp_apply, hL]
      rw [hHF _ (hC t W hWC) (mem_ball_zero_iff.mpr ((hnorm t ht).trans hρR))
        (smul_ne_zero ht0 hW0), hF t W hWC, mul_comm]
    have hev : ∀ᶠ t in 𝓝 (0 : ℂ), (H ∘ L) t = F W * t ^ k := by
      have hball : ∀ᶠ t in 𝓝 (0 : ℂ), ‖t‖ < 1 := by
        have := isOpen_ball.mem_nhds (mem_ball_self (x := (0 : ℂ)) (one_pos : (0 : ℝ) < 1))
        filter_upwards [this] with t ht
        simpa using ht
      filter_upwards [hball] with t ht
      by_cases ht0 : t = 0
      · subst ht0
        -- continuity at `0`
        have hlim1 : Tendsto (H ∘ L) (𝓝[≠] (0 : ℂ)) (𝓝 ((H ∘ L) 0)) :=
          hcontH.tendsto.mono_left nhdsWithin_le_nhds
        have hcont2 : Continuous fun t : ℂ => F W * t ^ k := by fun_prop
        have hlim2 : Tendsto (fun t : ℂ => F W * t ^ k) (𝓝[≠] (0 : ℂ))
            (𝓝 (F W * (0 : ℂ) ^ k)) := (hcont2.tendsto 0).mono_left nhdsWithin_le_nhds
        have hev' : (fun t : ℂ => F W * t ^ k) =ᶠ[𝓝[≠] (0 : ℂ)] (H ∘ L) := by
          have hb : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖t‖ < 1 := hball.filter_mono nhdsWithin_le_nhds
          filter_upwards [hb, self_mem_nhdsWithin] with t ht1 ht2
          exact (hpunct t ht1 ht2).symm
        exact tendsto_nhds_unique hlim1 (hlim2.congr' hev')
      · exact hpunct t ht ht0
    have heq := h1.eq_formalMultilinearSeries_of_eventually h2 hev
    have hk' := congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ => q k (fun _ => (1 : ℂ))) heq
    simp only [FormalMultilinearSeries.compContinuousLinearMap_apply,
      FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul,
      mul_one, if_true] at hk'
    have hL1 : L 1 = W := by rw [hL, one_smul]
    simpa only [Function.comp_def, hL1] using hk'
  obtain ⟨P, hPh, hPeval⟩ := exists_isHomogeneous_eval_eq_diag (p k)
  refine ⟨P, hPh, fun Z hZ => ?_⟩
  rw [hPeval]
  by_cases hZ0 : Z = 0
  · subst hZ0
    have hF0 : F 0 = 0 := by
      have h := hF 0 0 hZ
      rw [zero_smul, zero_pow hk.ne', zero_mul] at h
      exact h
    rw [hF0]
    exact (p k).map_coord_zero (⟨0, hk⟩ : Fin k) rfl
  · have hnZ : 0 < ‖Z‖ := norm_pos_iff.mpr hZ0
    set lam : ℝ := ρ / (2 * ‖Z‖) with hlam
    have hlam0 : 0 < lam := by positivity
    have hlamZ : ‖(lam : ℂ) • Z‖ < ρ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0, hlam]
      field_simp
      linarith
    have hlamC : (lam : ℂ) • Z ∈ C := hC _ Z hZ
    have hlamne : (lam : ℂ) • Z ≠ 0 :=
      smul_ne_zero (Complex.ofReal_ne_zero.mpr hlam0.ne') hZ0
    have h := hsmall _ hlamC hlamne hlamZ
    rw [(p k).map_smul_univ (fun _ => (lam : ℂ)) (fun _ => Z), Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, hF _ Z hZ] at h
    exact mul_left_cancel₀ (pow_ne_zero k (Complex.ofReal_ne_zero.mpr hlam0.ne')) h

end

end SGPT.GAGA.H0
