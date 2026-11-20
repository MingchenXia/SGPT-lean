import SGPT.Envelopes.LapClass2MeanValue
import SGPT.Envelopes.LapClassTrace

/-!
# Kähler normal coordinates on balls of uniform radius

Lane LAP-CLASS2 (`claude-lap-class2`, node `lap-class2:normal-ball`).  For the variable-coefficient
second-order contact theorem we need Kähler normal coordinates `Φ_y = normalCoord y L c`
(lane TOS-C11, `SGPT.Analysis.KahlerNormal`) centred at every point `y` of a compact set `K`, on a
ball `B(0, r₀)` whose radius does not depend on `y`, with

* `|(h̃_y(ζ) - 1)_{jk}| ≤ C_H |ζ|²` for the coefficient matrix `h̃_y` of the pulled-back form
  (`exists_uniform_normal_data`), and
* `|(h̃_y(ζ)⁻¹ - 1)_{jk}| ≤ C_G |ζ|²` (`inv_one_add_sub_one_entry_le`).

The quadratic bound comes from Taylor's formula (`abs_sub_le_of_norm_iteratedFDeriv_two_le`) and a
bound for the second derivatives of the pulled-back coefficients on `K × B̄(0, r₀)` obtained, as in
TOS-C11's `kahlerNormal_uniform_deriv`, from their joint smoothness in the data `(y, L, c)` and in
`ζ` (`kahlerNormal_uniform_deriv_ball`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace SGPT.Envelopes.LapClass

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Analysis.KahlerNormal

variable {n : ℕ}

/-! ### Two generic estimates -/

/-- **Perturbation of the identity matrix**: if all entries of `E` are at most `ε` and `n ε ≤ 1/2`,
the entries of `(1 + E)⁻¹ - 1` are at most `2 n ε`. -/
theorem inv_one_add_sub_one_entry_le (E : Matrix (Fin n) (Fin n) ℂ) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hE : ∀ j k, ‖E j k‖ ≤ ε) (hsmall : (n : ℝ) * ε ≤ 1 / 2) (j k : Fin n) :
    ‖((1 + E)⁻¹ - 1) j k‖ ≤ 2 * n * ε := by
  let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have : Nonempty (Fin n) := ⟨j⟩
  have : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  set x : Matrix (Fin n) (Fin n) ℂ := -E with hxdef
  have hentry : ∀ (A : Matrix (Fin n) (Fin n) ℂ) (i l : Fin n), ‖A i l‖ ≤ ‖A‖ := by
    intro A i l
    have h : ‖A i l‖₊ ≤ ‖A‖₊ := by
      rw [Matrix.linfty_opNNNorm_def]
      have h1 : ‖A i l‖₊ ≤ ∑ l', ‖A i l'‖₊ :=
        Finset.single_le_sum (f := fun l => ‖A i l‖₊) (fun _ _ => by positivity) (Finset.mem_univ l)
      have h2 : ∑ l', ‖A i l'‖₊ ≤ Finset.univ.sup fun i => ∑ l', ‖A i l'‖₊ :=
        Finset.le_sup (f := fun i => ∑ l', ‖A i l'‖₊) (Finset.mem_univ i)
      exact h1.trans h2
    exact_mod_cast h
  have hx : ‖x‖ ≤ n * ε := by
    have h : ‖E‖₊ ≤ Real.toNNReal (n * ε) := by
      rw [Matrix.linfty_opNNNorm_def]
      refine Finset.sup_le fun i _ => ?_
      rw [← NNReal.coe_le_coe, NNReal.coe_sum, Real.coe_toNNReal _ (by positivity)]
      calc ∑ l, (‖E i l‖₊ : ℝ) = ∑ l, ‖E i l‖ := rfl
        _ ≤ ∑ _l : Fin n, ε := Finset.sum_le_sum fun l _ => hE i l
        _ = n * ε := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h' : (‖E‖₊ : ℝ) ≤ (Real.toNNReal (n * ε) : ℝ) := by exact_mod_cast h
    rw [Real.coe_toNNReal _ (by positivity), coe_nnnorm] at h'
    rw [hxdef, norm_neg]
    exact h'
  have hx1 : ‖x‖ < 1 := by linarith
  have h1 : (1 + E) = 1 - x := by simp [hxdef, sub_eq_add_neg]
  have hgeom : (∑' i : ℕ, x ^ i) * (1 - x) = 1 := geom_series_mul_neg x hx1
  have hinv : (1 - x)⁻¹ = ∑' i : ℕ, x ^ i := Matrix.inv_eq_left_inv hgeom
  have hdiff : (1 - x)⁻¹ - 1 = (∑' i : ℕ, x ^ i) * x := by
    rw [hinv]
    calc (∑' i : ℕ, x ^ i) - 1 = (∑' i : ℕ, x ^ i) - (∑' i : ℕ, x ^ i) * (1 - x) := by
          rw [hgeom]
      _ = (∑' i : ℕ, x ^ i) * x := by rw [mul_sub, mul_one]; abel
  have hnorm : ‖(1 - x)⁻¹ - 1‖ ≤ 2 * ‖x‖ := by
    rw [hdiff]
    refine (norm_mul_le _ _).trans ?_
    have h2 := tsum_geometric_le_of_norm_lt_one x hx1
    rw [norm_one] at h2
    have h3 : (1 - ‖x‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    exact mul_le_mul_of_nonneg_right (h2.trans (by linarith)) (norm_nonneg x)
  rw [h1]
  calc ‖((1 - x)⁻¹ - 1) j k‖ ≤ ‖(1 - x)⁻¹ - 1‖ := hentry _ j k
    _ ≤ 2 * ‖x‖ := hnorm
    _ ≤ 2 * n * ε := by linarith

/-- **Second-order Taylor bound**: if `f` is `C²` on `B(0, r)` with `Df(0) = 0` and
`‖D²f‖ ≤ C` there, then `|f(w) - f(0)| ≤ C ‖w‖²` on `B(0, r)`. -/
theorem abs_sub_le_of_norm_iteratedFDeriv_two_le {f : ComplexModel n → ℝ} {r C : ℝ}
    (hf : ContDiffOn ℝ 2 f (ball 0 r)) (hD0 : fderiv ℝ f 0 = 0)
    (hC : ∀ w ∈ ball (0 : ComplexModel n) r, ‖iteratedFDeriv ℝ 2 f w‖ ≤ C) {w : ComplexModel n}
    (hw : w ∈ ball (0 : ComplexModel n) r) : |f w - f 0| ≤ C * ‖w‖ ^ 2 := by
  have hr : 0 < r := by
    have := mem_ball.mp hw
    exact (dist_nonneg).trans_lt this
  have h0 : (0 : ComplexModel n) ∈ ball (0 : ComplexModel n) r := mem_ball_self hr
  have hd1 : ∀ x ∈ ball (0 : ComplexModel n) r, DifferentiableAt ℝ f x := fun x hx =>
    (hf.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by norm_num)
  have hg : ContDiffOn ℝ 1 (fderiv ℝ f) (ball 0 r) :=
    hf.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hd2 : ∀ x ∈ ball (0 : ComplexModel n) r, DifferentiableAt ℝ (fderiv ℝ f) x := fun x hx =>
    (hg.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by norm_num)
  have hD2 : ∀ x ∈ ball (0 : ComplexModel n) r, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C := fun x hx => by
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ), norm_iteratedFDeriv_fderiv]
    exact hC x hx
  have hD1 : ∀ x ∈ ball (0 : ComplexModel n) r, ‖fderiv ℝ f x‖ ≤ C * ‖x‖ := fun x hx => by
    have h := (convex_ball (0 : ComplexModel n) r).norm_image_sub_le_of_norm_fderiv_le hd2 hD2
      h0 hx
    rwa [hD0, sub_zero, sub_zero] at h
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 h0)
  have hsub : closedBall (0 : ComplexModel n) ‖w‖ ⊆ ball 0 r := closedBall_subset_ball (by
    simpa using hw)
  have h := (convex_closedBall (0 : ComplexModel n) ‖w‖).norm_image_sub_le_of_norm_fderiv_le
    (fun x hx => hd1 x (hsub hx)) (fun x hx => (hD1 x (hsub hx)).trans
      (mul_le_mul_of_nonneg_left (by simpa using hx) hC0)) (mem_closedBall_self (norm_nonneg w))
      (by simp : w ∈ closedBall (0 : ComplexModel n) ‖w‖)
  rw [sub_zero, Real.norm_eq_abs] at h
  calc |f w - f 0| ≤ C * ‖w‖ * ‖w‖ := h
    _ = C * ‖w‖ ^ 2 := by ring

/-! ### Uniform bounds on balls -/

/-- The compact set of normal data `(z₀, A, c)` with `z₀ ∈ K`, `‖A‖, ‖c‖ ≤ C0`. -/
abbrev normalDataSet (K : Set (ComplexModel n)) (C0 : ℝ) : Set (NormalData n) :=
  K ×ˢ ((closedBall (0 : ComplexModel n →L[ℝ] ComplexModel n) C0) ×ˢ
    (closedBall (0 : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n) C0))

theorem isCompact_normalDataSet {K : Set (ComplexModel n)} (hK : IsCompact K) (C0 : ℝ) :
    IsCompact (normalDataSet K C0) := by
  have : FiniteDimensional ℝ (ComplexModel n →L[ℝ] ComplexModel n) := inferInstance
  have : FiniteDimensional ℝ (ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n) :=
    inferInstance
  have : ProperSpace (ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n) :=
    FiniteDimensional.proper_real (ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n)
  exact hK.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))

/-- A radius `r₀ ≤ 1` such that the normal coordinate maps of data in `normalDataSet K C0` send
`B̄(0, r₀)` into `U`. -/
theorem exists_normal_radius {U K : Set (ComplexModel n)} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) {C0 : ℝ} (hC0 : 0 ≤ C0) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ ∀ x ∈ normalDataSet K C0, ∀ w ∈ closedBall (0 : ComplexModel n) r₀,
      normalPoint x w ∈ U := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  refine ⟨min 1 (δ / (C0 * (1 + C0) + 1)), lt_min one_pos (by positivity), min_le_left _ _,
    fun x hx w hw => hδU ?_⟩
  obtain ⟨hx1, hx2, hx3⟩ := hx
  replace hx2 : ‖x.2.1‖ ≤ C0 := (dist_zero_right x.2.1).symm.le.trans (mem_closedBall.mp hx2)
  replace hx3 : ‖x.2.2‖ ≤ C0 := (dist_zero_right x.2.2).symm.le.trans (mem_closedBall.mp hx3)
  rw [mem_closedBall, dist_zero_right] at hw
  have hr1 : ‖w‖ ≤ 1 := hw.trans (min_le_left _ _)
  have hr2 : ‖w‖ ≤ δ / (C0 * (1 + C0) + 1) := hw.trans (min_le_right _ _)
  refine Metric.mem_cthickening_of_dist_le _ x.1 _ _ hx1 ?_
  rw [normalPoint, dist_eq_norm, add_sub_cancel_left]
  have hcw : ‖x.2.2 w w‖ ≤ C0 * ‖w‖ * ‖w‖ :=
    ((x.2.2 w).le_opNorm w).trans (mul_le_mul_of_nonneg_right ((x.2.2.le_opNorm w).trans
      (mul_le_mul_of_nonneg_right hx3 (norm_nonneg _))) (norm_nonneg _))
  have hin : ‖w - (1 / 2 : ℝ) • x.2.2 w w‖ ≤ (1 + C0) * ‖w‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    nlinarith [norm_nonneg w, norm_nonneg (x.2.2 w w)]
  calc ‖x.2.1 (w - (1 / 2 : ℝ) • x.2.2 w w)‖ ≤ C0 * ((1 + C0) * ‖w‖) :=
        (x.2.1.le_opNorm _).trans (mul_le_mul hx2 hin (norm_nonneg _) hC0)
    _ ≤ (C0 * (1 + C0) + 1) * (δ / (C0 * (1 + C0) + 1)) := by
        have := mul_le_mul_of_nonneg_left hr2 (by positivity : 0 ≤ C0 * (1 + C0))
        nlinarith [norm_nonneg w]
    _ = δ := by field_simp

set_option maxHeartbeats 1600000 in
/-- **Uniform bound for the derivatives of the pulled-back coefficients on a ball.** -/
theorem exists_bound_iteratedFDeriv_normalCoeffFun {U K : Set (ComplexModel n)} (hU : IsOpen U)
    {a : ComplexModel n → CoordinateRealTwoForm n} (ha : ContDiffOn ℝ ∞ a U) (hK : IsCompact K)
    {C0 r₀ : ℝ} (hin : ∀ x ∈ normalDataSet K C0, ∀ w ∈ closedBall (0 : ComplexModel n) r₀,
      normalPoint x w ∈ U) (q : ℕ) (u v : ComplexModel n) :
    ∃ C : ℝ, ∀ x ∈ normalDataSet K C0, ∀ w ∈ closedBall (0 : ComplexModel n) r₀,
      ‖iteratedFDeriv ℝ q (fun w => normalCoeffFun a u v (x, w)) w‖ ≤ C := by
  have hO : IsOpen {y : NormalData n × ComplexModel n | normalPoint y.1 y.2 ∈ U} :=
    hU.preimage contDiff_normalPoint.continuous
  have hH := contDiffAt_iteratedFDeriv_param hO (contDiffOn_normalCoeffFun ha u v) q
  have hKp : IsCompact (normalDataSet K C0 ×ˢ closedBall (0 : ComplexModel n) r₀) :=
    (isCompact_normalDataSet hK C0).prod (isCompact_closedBall _ _)
  have hcont : ContinuousOn (fun y : NormalData n × ComplexModel n =>
      iteratedFDeriv ℝ q (fun w => normalCoeffFun a u v (y.1, w)) y.2)
      (normalDataSet K C0 ×ˢ closedBall (0 : ComplexModel n) r₀) := fun y hy =>
    (hH y (hin y.1 hy.1 y.2 hy.2)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hKp.exists_bound_of_continuousOn hcont
  exact ⟨C, fun x hx w hw => hC (x, w) ⟨hx, hw⟩⟩

/-- **Kähler normal coordinates on a ball of uniform radius.**  For a smooth field `a` of
strictly positive closed real `(1,1)`-forms on an open `U ⊆ ℂⁿ` and a compact `K ⊆ U` there are
`r₀ > 0` and constants such that every `z₀ ∈ K` is the centre of normal coordinates
`Φ = normalCoord z₀ L c` with `‖L‖ ≤ C0`, `‖L⁻¹ y‖ ≤ N0 ‖y‖`, `‖c(p, x)‖ ≤ C0 ‖p‖ ‖x‖`,
`Φ(B̄(0, r₀)) ⊆ U` and `|(h̃(w) - 1)_{jk}| ≤ C_H ‖w‖²` on `B(0, r₀)`, `h̃` the coefficient matrix of
`Φ^*a`; moreover `C0 r₀ ≤ 1/4` and `C0² r₀ N0 ≤ 1/4`. -/
theorem exists_uniform_normal_data {U : Set (ComplexModel n)} (hU : IsOpen U)
    {a : ComplexModel n → CoordinateRealTwoForm n} (ha : ContDiffOn ℝ ∞ a U)
    (h11 : ∀ z ∈ U, IsOneOne (a z)) (hpos : ∀ z ∈ U, IsStrictlyPositive (a z))
    (hcl : ∀ z ∈ U, extDeriv a z = 0) {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKU : K ⊆ U) :
    ∃ r₀ C0 N0 CH : ℝ, 0 < r₀ ∧ 0 ≤ C0 ∧ 0 < N0 ∧ 0 ≤ CH ∧ C0 * r₀ ≤ 1 / 4 ∧
      C0 * C0 * r₀ * N0 ≤ 1 / 4 ∧ ∀ z₀ ∈ K, ∃ (L : ComplexModel n ≃L[ℂ] ComplexModel n)
        (c : ComplexModel n →L[ℂ] ComplexModel n →L[ℂ] ComplexModel n),
        (∀ p u, c p u = c u p) ∧ ‖(L : ComplexModel n →L[ℂ] ComplexModel n)‖ ≤ C0 ∧
        (∀ y, ‖L.symm y‖ ≤ N0 * ‖y‖) ∧ (∀ p x, ‖c p x‖ ≤ C0 * ‖p‖ * ‖x‖) ∧
        (∀ w ∈ closedBall (0 : ComplexModel n) r₀,
          normalCoord z₀ (L : ComplexModel n →L[ℂ] ComplexModel n) c w ∈ U) ∧
        ∀ w ∈ ball (0 : ComplexModel n) r₀, ∀ j k,
          ‖(normalizedHermitianMatrix (pullbackField
            (normalCoord z₀ (L : ComplexModel n →L[ℂ] ComplexModel n) c) a w) - 1) j k‖ ≤
            CH * ‖w‖ ^ 2 := by
  classical
  obtain ⟨C0, hC0, hb⟩ := kahlerNormal_bound hU (ha.of_le (by simp)) hpos hK hKU
  obtain ⟨Ma, hMa⟩ := hK.exists_bound_of_continuousOn (ha.continuousOn.mono hKU)
  set N0 : ℝ := Real.sqrt (Real.pi * max Ma 0) + 1 with hN0
  have hN0pos : 0 < N0 := by positivity
  obtain ⟨r₁, hr₁, hr₁1, hin⟩ := exists_normal_radius hU hK hKU hC0
  set r₀ : ℝ := min r₁ (1 / (4 * (C0 + 1) * (C0 * N0 + 1))) with hr₀def
  have hr₀ : 0 < r₀ := lt_min hr₁ (by positivity)
  have hr₀₁ : r₀ ≤ r₁ := min_le_left _ _
  have hr₀₂ : r₀ ≤ 1 / (4 * (C0 + 1) * (C0 * N0 + 1)) := min_le_right _ _
  have hin₀ : ∀ x ∈ normalDataSet K C0, ∀ w ∈ closedBall (0 : ComplexModel n) r₀,
      normalPoint x w ∈ U := fun x hx w hw =>
    hin x hx w (closedBall_subset_closedBall hr₀₁ hw)
  -- the pairs of vectors giving the entries of the coefficient matrix
  set vec : Fin n → Fin n → Fin 2 → ComplexModel n × ComplexModel n := fun j k t =>
    if t = 0 then (coordinateVector j, Complex.I • coordinateVector k)
    else (coordinateVector j, coordinateVector k) with hvec
  choose C₂ hC₂ using fun (jkt : Fin n × Fin n × Fin 2) =>
    exists_bound_iteratedFDeriv_normalCoeffFun hU ha hK hin₀ 2
      (vec jkt.1 jkt.2.1 jkt.2.2).1 (vec jkt.1 jkt.2.1 jkt.2.2).2
  set Ct : ℝ := ∑ jkt, |C₂ jkt| with hCt
  have hCt0 : 0 ≤ Ct := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hC₂le : ∀ jkt, C₂ jkt ≤ Ct := fun jkt =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun jkt => |C₂ jkt|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ jkt))
  refine ⟨r₀, C0, N0, 2 * Real.pi * Ct, hr₀, hC0, hN0pos, by positivity, ?_, ?_, fun z₀ hz₀ => ?_⟩
  · calc C0 * r₀ ≤ C0 * (1 / (4 * (C0 + 1) * (C0 * N0 + 1))) :=
          mul_le_mul_of_nonneg_left hr₀₂ hC0
      _ ≤ 1 / 4 := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [mul_nonneg hC0 hN0pos.le]
  · calc C0 * C0 * r₀ * N0 = (C0 * C0 * N0) * r₀ := by ring
      _ ≤ (C0 * C0 * N0) * (1 / (4 * (C0 + 1) * (C0 * N0 + 1))) :=
          mul_le_mul_of_nonneg_left hr₀₂ (by positivity)
      _ ≤ 1 / 4 := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [mul_nonneg hC0 hN0pos.le, mul_nonneg (mul_nonneg hC0 hC0) hN0pos.le]
  have hz₀U := hKU hz₀
  obtain ⟨L, hL⟩ := exists_normalizing_linear (h11 z₀ hz₀U) (hpos z₀ hz₀U)
  set L' := (L : ComplexModel n →L[ℂ] ComplexModel n) with hL'def
  have ha0 : DifferentiableAt ℝ a z₀ :=
    (ha.contDiffAt (hU.mem_nhds hz₀U)).differentiableAt (by simp)
  have h11ev : ∀ᶠ z in 𝓝 z₀, IsOneOne (a z) :=
    Filter.mem_of_superset (hU.mem_nhds hz₀U) fun z hz => h11 z hz
  set β := normalizedDeriv a z₀ L'
  have hβ11 := normalizedDeriv_isOneOne ha0 h11ev L'
  set c := normalQuad β hβ11 with hcdef
  have hc : ∀ p u v, inner ℂ v (c p u) = (Real.pi : ℂ) * dHol β p u v := fun p u v =>
    inner_quadFun β p u v
  obtain ⟨hsymm, h0, hd⟩ := kahlerNormal_of_normalizing z₀ L' c ha0 h11ev (hcl z₀ hz₀U) hL hc
  obtain ⟨hAn, hcb⟩ := hb z₀ hz₀ L' hL
  obtain ⟨hcpx, hcn⟩ := hcb c hc
  -- the real normal data
  obtain ⟨cR, hcR⟩ : ∃ cR : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n,
      ∀ p x, cR p x = c p x :=
    ⟨ContinuousLinearMap.restrictScalarsL ℂ (ComplexModel n) (ComplexModel n) ℝ ℝ ∘L
      c.restrictScalars ℝ, fun p x => rfl⟩
  have hx : ((z₀, L'.restrictScalars ℝ, cR) : NormalData n) ∈ normalDataSet K C0 := by
    have h1 : ‖L'.restrictScalars ℝ‖ ≤ C0 := by
      refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun y => ?_
      exact (L'.le_opNorm y).trans (by gcongr)
    have h2 : ‖cR‖ ≤ C0 := by
      refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun p => ?_
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
      rw [hcR]
      exact hcpx p y
    refine ⟨hz₀, ?_, ?_⟩
    · rw [mem_closedBall]
      exact (dist_zero_right _).le.trans h1
    · rw [mem_closedBall]
      exact (dist_zero_right cR).le.trans h2
  have hfun : ∀ u v : ComplexModel n, (fun w => pullbackField (normalCoord z₀ L' c) a w ![u, v]) =
      fun w => normalCoeffFun a u v ((z₀, L'.restrictScalars ℝ, cR), w) := by
    intro u v
    funext w
    have hhalf : ((1 / 2 : ℂ)) • c w w = (1 / 2 : ℝ) • c w w := by
      rw [← Complex.coe_smul]; norm_num
    rw [pullbackField, fderiv_normalCoord z₀ L' c hsymm, compContinuousLinearMap_apply_two]
    simp only [normalCoeffFun, normalPoint, normalCoord, hcR,
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.comp_apply, _root_.sub_apply,
      ContinuousLinearMap.id_apply, hhalf]
  have hpt : ∀ w, normalCoord z₀ L' c w = normalPoint (z₀, L'.restrictScalars ℝ, cR) w := by
    intro w
    have hhalf : ((1 / 2 : ℂ)) • c w w = (1 / 2 : ℝ) • c w w := by
      rw [← Complex.coe_smul]; norm_num
    simp only [normalCoord, normalPoint, hcR, hhalf, ContinuousLinearMap.coe_restrictScalars']
  have hΦU : ∀ w ∈ closedBall (0 : ComplexModel n) r₀, normalCoord z₀ L' c w ∈ U := by
    intro w hw
    rw [hpt]
    exact hin₀ _ hx w hw
  -- the bound for `L⁻¹`
  have hLinv : ∀ y, ‖L.symm y‖ ≤ N0 * ‖y‖ := by
    intro y
    set x := L.symm y with hxdef
    have hy : L x = y := L.apply_symm_apply y
    have h1 : Real.pi⁻¹ * ‖x‖ ^ 2 ≤ max Ma 0 * ‖y‖ ^ 2 := by
      rw [← flatForm_apply_I_smul_self, ← hL, map_smul, hy]
      have h2 := twoForm_norm_apply_le (a z₀) y (Complex.I • y)
      have h3 := hMa z₀ hz₀
      rw [norm_smul, Complex.norm_I, one_mul] at h2
      calc a z₀ ![y, Complex.I • y] ≤ ‖a z₀‖ * ‖y‖ * ‖y‖ := (le_abs_self _).trans h2
        _ ≤ max Ma 0 * ‖y‖ ^ 2 := by
            rw [mul_assoc, ← sq]
            exact mul_le_mul_of_nonneg_right (h3.trans (le_max_left _ _)) (sq_nonneg _)
    have h4 : ‖x‖ ^ 2 ≤ (Real.pi * max Ma 0) * ‖y‖ ^ 2 := by
      have hπ := Real.pi_pos
      have := mul_le_mul_of_nonneg_left h1 hπ.le
      rw [← mul_assoc, mul_inv_cancel₀ hπ.ne', one_mul] at this
      linarith
    have h5 : ‖x‖ ≤ Real.sqrt (Real.pi * max Ma 0) * ‖y‖ := by
      rw [← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_sq (norm_nonneg y), ← Real.sqrt_mul
        (by positivity)]
      exact Real.sqrt_le_sqrt h4
    exact h5.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  refine ⟨L, c, hsymm, hAn, hLinv, hcpx, hΦU, fun w hw j k => ?_⟩
  -- the quadratic bound for the entries
  have hquad : ∀ jkt : Fin n × Fin n × Fin 2,
      |pullbackField (normalCoord z₀ L' c) a w
          ![(vec jkt.1 jkt.2.1 jkt.2.2).1, (vec jkt.1 jkt.2.1 jkt.2.2).2] -
        flatForm n ![(vec jkt.1 jkt.2.1 jkt.2.2).1, (vec jkt.1 jkt.2.1 jkt.2.2).2]| ≤
        Ct * ‖w‖ ^ 2 := by
    intro jkt
    set u := (vec jkt.1 jkt.2.1 jkt.2.2).1
    set v := (vec jkt.1 jkt.2.1 jkt.2.2).2
    set f := fun w => pullbackField (normalCoord z₀ L' c) a w ![u, v] with hfdef
    have hf0 : f 0 = flatForm n ![u, v] := by simp only [hfdef, h0]
    have hfD : fderiv ℝ f 0 = 0 := SGPT.Envelopes.LapClass.fderiv_apply_eq_zero hd u v
    have hfs : ContDiffOn ℝ 2 f (ball 0 r₀) := by
      rw [hfdef, hfun u v]
      have hmap : ContDiff ℝ ∞ (fun w : ComplexModel n =>
          (((z₀, L'.restrictScalars ℝ, cR) : NormalData n), w)) := by fun_prop
      refine ((contDiffOn_normalCoeffFun ha u v).comp hmap.contDiffOn fun w hw => ?_).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
      exact hin₀ _ hx w (ball_subset_closedBall hw)
    have hfC : ∀ w ∈ ball (0 : ComplexModel n) r₀, ‖iteratedFDeriv ℝ 2 f w‖ ≤ Ct := by
      intro w hw
      rw [hfdef, hfun u v]
      exact (hC₂ jkt _ hx w (ball_subset_closedBall hw)).trans (hC₂le jkt)
    have h := abs_sub_le_of_norm_iteratedFDeriv_two_le hfs hfD hfC hw
    rwa [hf0] at h
  have hq0 := hquad (j, k, 0)
  have hq1 := hquad (j, k, 1)
  simp only [hvec, if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0)] at hq0 hq1
  rw [Matrix.sub_apply, ← normalizedHermitianMatrix_flatForm n, normalizedHermitianMatrix_apply',
    normalizedHermitianMatrix_apply', ← mul_sub]
  simp only [hermitianEntry]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hsplit : ((pullbackField (normalCoord z₀ L' c) a w
        ![coordinateVector j, Complex.I • coordinateVector k] : ℂ) -
      Complex.I * (pullbackField (normalCoord z₀ L' c) a w
        ![coordinateVector j, coordinateVector k] : ℂ)) -
      ((flatForm n ![coordinateVector j, Complex.I • coordinateVector k] : ℂ) -
      Complex.I * (flatForm n ![coordinateVector j, coordinateVector k] : ℂ)) =
      (((pullbackField (normalCoord z₀ L' c) a w
        ![coordinateVector j, Complex.I • coordinateVector k] -
          flatForm n ![coordinateVector j, Complex.I • coordinateVector k] : ℝ) : ℂ) -
        Complex.I * ((pullbackField (normalCoord z₀ L' c) a w
          ![coordinateVector j, coordinateVector k] -
            flatForm n ![coordinateVector j, coordinateVector k] : ℝ) : ℂ)) := by
    push_cast; ring
  rw [hsplit]
  calc Real.pi * ‖((_ : ℝ) : ℂ) - Complex.I * ((_ : ℝ) : ℂ)‖
      ≤ Real.pi * (Ct * ‖w‖ ^ 2 + Ct * ‖w‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add ?_ ?_))
          Real.pi_pos.le
        · rw [Complex.norm_real, Real.norm_eq_abs]; exact hq0
        · rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]; exact hq1
    _ = 2 * Real.pi * Ct * ‖w‖ ^ 2 := by ring

end SGPT.Envelopes.LapClass
