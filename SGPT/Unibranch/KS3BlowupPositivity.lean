import SGPT.Unibranch.KS2LeviEstimate
import SGPT.Unibranch.KS3FibreLevi
import SGPT.Foundations.Analysis.Pending.UniformTubePositivity
import SGPT.Foundations.Analysis.Pending.BlowupWeightLevi

/-!
# Local positivity of `P^*ω + ddᶜ(ε log R + ‖H‖²)`

Lane KS3 (Kähler preservation under blowups, `def:unibranch:L212`).  In a chart of an ambient
space of the blowup: `P` (holomorphic, the projection to an ambient space of `X`), `v` a strictly
positive form near the image (a Kähler form of `X`), `H` holomorphic (equations of the blowup),
and `R > 0` smooth (the weight).  If `ddᶜ log R` is positive at `u₀` on the common kernel of
`dP` and `dH` (the fibre directions of the exceptional divisor), then
`P^*v + ddᶜ(ε log R + ‖H‖²)` is strictly positive near `u₀` for every small `ε > 0`
(`exists_isStrictlyPositive_near`): `P^*v + ddᶜ‖H‖²` is semipositive with exactly that kernel,
and `UniformTubePositivity` gives one neighbourhood and one bound.

`fibre_pos`: the hypothesis on `ddᶜ log R` holds for the blowup weight
`R = c₀ ‖ŵ‖² + Σ_x c_x ‖B_x ŵ‖²` in monomial coordinates (`ŵ = hatCoord`), when `c₀ > 0`,
`c_x ≥ 0` and `c`, `B` are constant along fibre lines (Fubini–Study).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Unibranch.KS3BlowupPositivity

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  BlowupWeightLevi

/-- **Local positivity.** -/
theorem exists_isStrictlyPositive_near {n N r : ℕ} {Ω : Set (ComplexModel n)} (hΩ : IsOpen Ω)
    {u₀ : ComplexModel n} (hu₀ : u₀ ∈ Ω) {P : ComplexModel n → ComplexModel N}
    (hP : ContDiffOn ℂ ∞ P Ω) {O : Set (ComplexModel N)} (_hO : IsOpen O) (hPO : MapsTo P Ω O)
    {v : AmbientForm N 2} (hv : ContDiffOn ℝ ∞ v O) (hvpos : ∀ x ∈ O, IsStrictlyPositive (v x))
    {H : ComplexModel n → ComplexModel r} (hH : ContDiffOn ℂ ∞ H Ω)
    {R : ComplexModel n → ℝ} (hR : ContDiffOn ℝ ∞ R Ω) (hRpos : ∀ u ∈ Ω, 0 < R u)
    (hfib : ∀ ξ : ComplexModel n, ξ ≠ 0 → fderiv ℝ P u₀ ξ = 0 → fderiv ℝ H u₀ ξ = 0 →
      0 < smoothDDC (fun u => Real.log (R u)) u₀ ![ξ, Complex.I • ξ]) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ U : Set (ComplexModel n), IsOpen U ∧ u₀ ∈ U ∧ U ⊆ Ω ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ u ∈ U,
        IsStrictlyPositive (pullbackForm P v u +
          smoothDDC (fun u => ε * Real.log (R u) + ‖H u‖ ^ 2) u) := by
  have hlogR : ContDiffOn ℝ ∞ (fun u => Real.log (R u)) Ω :=
    hR.log fun u hu => (hRpos u hu).ne'
  have hHn : ContDiffOn ℝ ∞ (fun u => ‖H u‖ ^ 2) Ω :=
    (contDiff_norm_sq ℝ).comp_contDiffOn (hH.restrict_scalars ℝ)
  have hPr := hP.restrict_scalars ℝ
  let a : ComplexModel n → ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ :=
    smoothDDC (fun u => Real.log (R u))
  let b : ComplexModel n → ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ :=
    fun u => pullbackForm P v u + smoothDDC (fun u => ‖H u‖ ^ 2) u
  have hacont : ContinuousOn a Ω :=
    (LogWeightFactorization.smoothDDC_contDiffOn hΩ hlogR).continuousOn
  have hbcont : ContinuousOn b Ω :=
    (SmoothRealForm.contDiffOn_compContinuousLinearMap (hv.comp hPr hPO)
      (hPr.fderiv_of_isOpen hΩ (by simp))).continuousOn.add
      (LogWeightFactorization.smoothDDC_contDiffOn hΩ hHn).continuousOn
  have hquadH : ∀ u ∈ Ω, ∀ ξ, smoothDDC (fun u => ‖H u‖ ^ 2) u ![ξ, Complex.I • ξ] =
      ‖fderiv ℝ H u ξ‖ ^ 2 / Real.pi := fun u hu ξ =>
    KS3FibreLevi.quad_smoothDDC_norm_sq hΩ hH hu ξ
  have hb : ∀ u ∈ Ω, ∀ ξ, 0 ≤ PositivityPerturbation.quad (b u) ξ := by
    intro u hu ξ
    change 0 ≤ (pullbackForm P v u + smoothDDC (fun u => ‖H u‖ ^ 2) u) ![ξ, Complex.I • ξ]
    rw [ContinuousAlternatingMap.add_apply, hquadH u hu ξ]
    have h1 := (KS2LeviEstimate.quad_pullbackForm_nonneg hΩ hP hPO hvpos hu ξ).1
    exact add_nonneg h1 (div_nonneg (sq_nonneg _) Real.pi_pos.le)
  have hpos : ∀ u ∈ ({u₀} : Set (ComplexModel n)), ∀ ξ : ComplexModel n, ξ ≠ 0 →
      PositivityPerturbation.quad (b u) ξ = 0 → 0 < PositivityPerturbation.quad (a u) ξ := by
    intro u hu ξ hξ hnull
    rw [mem_singleton_iff] at hu
    subst hu
    change (pullbackForm P v u + smoothDDC (fun u => ‖H u‖ ^ 2) u) ![ξ, Complex.I • ξ] = 0
      at hnull
    rw [ContinuousAlternatingMap.add_apply, hquadH u hu₀ ξ] at hnull
    have h1 := KS2LeviEstimate.quad_pullbackForm_nonneg hΩ hP hPO hvpos hu₀ ξ
    have h2 : 0 ≤ ‖fderiv ℝ H u ξ‖ ^ 2 / Real.pi := div_nonneg (sq_nonneg _) Real.pi_pos.le
    have hz1 : PositivityPerturbation.quad (pullbackForm P v u) ξ = 0 := by
      change pullbackForm P v u ![ξ, Complex.I • ξ] = 0
      have : (0 : ℝ) ≤ pullbackForm P v u ![ξ, Complex.I • ξ] := h1.1
      linarith
    have hz2 : ‖fderiv ℝ H u ξ‖ ^ 2 / Real.pi = 0 := by
      have : (0 : ℝ) ≤ pullbackForm P v u ![ξ, Complex.I • ξ] := h1.1
      linarith
    have hdP : fderiv ℝ P u ξ = 0 := h1.2 hz1
    have hdH : fderiv ℝ H u ξ = 0 := by
      rcases div_eq_zero_iff.mp hz2 with h | h
      · exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)
      · exact absurd h Real.pi_ne_zero
    exact hfib ξ hξ hdP hdH
  obtain ⟨B₀, hB₀, U, hU, hu₀U, hUΩ, hB⟩ :=
    UniformTubePositivity.exists_forall_isStrictlyPositive_add_smul_of_pos_on_null_familyOn
      hΩ hacont hbcont hb (isCompact_singleton (x := u₀)) (singleton_subset_iff.mpr hu₀) hpos
  refine ⟨B₀⁻¹, inv_pos.mpr hB₀, U, hU, hu₀U (mem_singleton u₀), hUΩ, ?_⟩
  intro ε hε hεB u hu
  have huΩ := hUΩ hu
  have hsplit : smoothDDC (fun u => ε * Real.log (R u) + ‖H u‖ ^ 2) u =
      ε • a u + smoothDDC (fun u => ‖H u‖ ^ 2) u := by
    rw [smoothDDC_add hΩ (contDiffOn_const.mul hlogR) hHn huΩ]
    congr 1
    have := smoothDDC_smul hΩ hlogR ε huΩ
    simpa only [smul_eq_mul] using this
  rw [hsplit]
  have hBε : B₀ ≤ ε⁻¹ := by
    rw [le_inv_comm₀ hB₀ hε]
    exact hεB
  have hpos' := hB ε⁻¹ hBε u hu
  intro ξ hξ
  have h := hpos' ξ hξ
  change 0 < (a u + ε⁻¹ • b u) ![ξ, Complex.I • ξ] at h
  change 0 < (pullbackForm P v u + (ε • a u + smoothDDC (fun u => ‖H u‖ ^ 2) u))
    ![ξ, Complex.I • ξ]
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul] at h ⊢
  have hb' : b u ![ξ, Complex.I • ξ] = pullbackForm P v u ![ξ, Complex.I • ξ] +
      smoothDDC (fun u => ‖H u‖ ^ 2) u ![ξ, Complex.I • ξ] := rfl
  rw [hb'] at h
  have : 0 < ε * (a u ![ξ, Complex.I • ξ] + ε⁻¹ * (pullbackForm P v u ![ξ, Complex.I • ξ] +
      smoothDDC (fun u => ‖H u‖ ^ 2) u ![ξ, Complex.I • ξ])) := mul_pos hε h
  rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul] at this
  linarith

/-- **Fubini–Study positivity of the blowup weight in fibre directions.** -/
theorem fibre_pos {n r : ℕ} {ι : Type} [Fintype ι] {rr : ι → ℕ} {j : Fin n}
    (emb : Fin r → Fin n) (hemb_j : ∃ j' : Fin r, emb j' = j)
    (c₀ : ComplexModel n → ℝ) (c : ι → ComplexModel n → ℝ)
    (B : (x : ι) → Fin (rr x) → Fin r → ComplexModel n → ℂ)
    {w₀ v : ComplexModel n}
    (hC2 : ContDiffAt ℝ 2 (fun w => Real.log (c₀ w * ∑ l, Complex.normSq (hatCoord j w (emb l)) +
      ∑ x, c x w * ∑ i, Complex.normSq (∑ l, B x i l w * hatCoord j w (emb l)))) w₀)
    (hc₀ : 0 < c₀ w₀) (hc : ∀ x, 0 ≤ c x w₀)
    (hc_line : ∀ t : ℂ, c₀ (w₀ + t • v) = c₀ w₀) (hcx_line : ∀ x (t : ℂ), c x (w₀ + t • v) = c x w₀)
    (hB_line : ∀ x i l (t : ℂ), B x i l (w₀ + t • v) = B x i l w₀)
    (hvj : v j = 0) (hv : ∃ l, v (emb l) ≠ 0) :
    0 < smoothDDC (fun w => Real.log (c₀ w * ∑ l, Complex.normSq (hatCoord j w (emb l)) +
      ∑ x, c x w * ∑ i, Complex.normSq (∑ l, B x i l w * hatCoord j w (emb l)))) w₀
      ![v, Complex.I • v] := by
  classical
  obtain ⟨j', hj'⟩ := hemb_j
  let κ := Fin r ⊕ (Σ x : ι, Fin (rr x))
  let X : EuclideanSpace ℂ κ := WithLp.toLp 2 fun s => match s with
    | Sum.inl l => (Real.sqrt (c₀ w₀) : ℂ) * hatCoord j w₀ (emb l)
    | Sum.inr ⟨x, i⟩ => (Real.sqrt (c x w₀) : ℂ) * ∑ l, B x i l w₀ * hatCoord j w₀ (emb l)
  let Y : EuclideanSpace ℂ κ := WithLp.toLp 2 fun s => match s with
    | Sum.inl l => (Real.sqrt (c₀ w₀) : ℂ) * v (emb l)
    | Sum.inr ⟨x, i⟩ => (Real.sqrt (c x w₀) : ℂ) * ∑ l, B x i l w₀ * v (emb l)
  have hhat : ∀ (t : ℂ) (l : Fin r),
      hatCoord j (w₀ + t • v) (emb l) = hatCoord j w₀ (emb l) + t * v (emb l) := fun t l =>
    hatCoord_line w₀ v hvj t (emb l)
  refine KS3FibreLevi.smoothDDC_log_pos_of_line (X := X) (Y := Y) hC2 (fun t => ?_) ?_ ?_
  · rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, Fintype.sum_sigma]
    simp only [X, Y, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hc_line, hcx_line, hB_line,
      hhat]
    congr 1
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      have e1 : (Real.sqrt (c₀ w₀) : ℂ) * hatCoord j w₀ (emb l) +
          t * ((Real.sqrt (c₀ w₀) : ℂ) * v (emb l)) =
          (Real.sqrt (c₀ w₀) : ℂ) * (hatCoord j w₀ (emb l) + t * v (emb l)) := by ring
      rw [e1, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        Real.sq_sqrt hc₀.le, Complex.normSq_eq_norm_sq]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hsum : ∑ l, B x i l w₀ * (hatCoord j w₀ (emb l) + t * v (emb l)) =
          ∑ l, B x i l w₀ * hatCoord j w₀ (emb l) + t * ∑ l, B x i l w₀ * v (emb l) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
      have e1 : (Real.sqrt (c x w₀) : ℂ) * ∑ l, B x i l w₀ * hatCoord j w₀ (emb l) +
          t * ((Real.sqrt (c x w₀) : ℂ) * ∑ l, B x i l w₀ * v (emb l)) =
          (Real.sqrt (c x w₀) : ℂ) * (∑ l, B x i l w₀ * hatCoord j w₀ (emb l) +
            t * ∑ l, B x i l w₀ * v (emb l)) := by ring
      rw [hsum, e1, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        Real.sq_sqrt (hc x), Complex.normSq_eq_norm_sq]
  · -- independence
    have hsq : (Real.sqrt (c₀ w₀) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hc₀).ne'
    intro t ht
    have h1 := congrArg (fun Z : EuclideanSpace ℂ κ => Z (Sum.inl j')) ht
    simp only [X, Y, PiLp.smul_apply, smul_eq_mul, hj', hvj, mul_zero] at h1
    have hhj : hatCoord j w₀ j = 1 := by simp [hatCoord]
    rw [hhj, mul_one] at h1
    have ht0 : t = 0 := by
      rcases mul_eq_zero.mp h1.symm with h | h
      · exact h
      · exact absurd h hsq
    obtain ⟨l, hl⟩ := hv
    have h2 := congrArg (fun Z : EuclideanSpace ℂ κ => Z (Sum.inl l)) ht
    simp only [X, Y, PiLp.smul_apply, smul_eq_mul, ht0, zero_mul] at h2
    rcases mul_eq_zero.mp h2 with h | h
    · exact hsq h
    · exact hl h
  · intro h0
    have h1 := congrArg (fun Z : EuclideanSpace ℂ κ => Z (Sum.inl j')) h0
    simp only [X, hj'] at h1
    have hhj : hatCoord j w₀ j = 1 := by simp [hatCoord]
    rw [hhj, mul_one] at h1
    have hsq : (Real.sqrt (c₀ w₀) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hc₀).ne'
    exact hsq h1

end SGPT.Unibranch.KS3BlowupPositivity
