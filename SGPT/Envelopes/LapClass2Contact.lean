import SGPT.Envelopes.LapClass2Transport
import SGPT.Envelopes.LapClass2Chart
import SGPT.Envelopes.C11RealRoofContact
import SGPT.Envelopes.LapClassKahlerClass

/-!
# Second-order contact for functions with bounded metric Laplacian

Lane LAP-CLASS2 (`claude-lap-class2`, nodes `lap-class2:contact-abstract`,
`lap-class2:contact-chart`, `lap-class2:contact-manifold`, `lap-class2:dntroof`).  Source:
`references/sgpt-d3f272c3/source/author/chapter_npp.tex`, `lma:DNTroof`, first assertion:

> Assume that `ω` is a Kähler form on `X` and let `f₁, f₂ ∈ C^{1,1̄}(X)`.  Then the functions `f₁`,
> `f₂` and `P_ω(min{f₁, f₂})` coincide up to second order at almost every point of the contact
> set `{P_ω(min{f₁, f₂}) = f₁ = f₂}`.

Here `C^{1,1̄}(X)` is the book's class of continuous functions with bounded `ω`-Laplacian
(`HasBoundedMetricLaplacian`, lane LAP-CLASS), in every dimension; C11-REAL proved the statement for
the smaller class of bounded complex Hessians, whose flat Laplacian is bounded in charts.  For
`n ≥ 2` a bounded `ω`-Laplacian is a bounded *variable-coefficient* operator `Re tr(H⁻¹ ∂∂̄)` in a
chart, and the flat mean-value inequalities are replaced by those of `LapClass2MeanValue` in
Kähler normal coordinates (`LapClass2Normal`, `LapClass2Transport`).  No Calderón–Zygmund theory,
no `W^{2,p}` estimate and no Stampacchia lemma are used.

* `ae_isLittleO_of_meanValue` — the density-point argument of C11-REAL with constants: if
  `g ≥ 0` has quadratic averages at its zeros and satisfies a sub-mean-value inequality with
  quadratic error, it vanishes to second order at almost every zero.
* `ae_isLittleO_of_kahler_pairing` — **chart version**: if `g ≥ 0` is continuous on an open
  `U ⊆ ℂⁿ` and `|∫ g V Re tr(H⁻¹ ∂∂̄φ)| ≤ M ∫ V |φ|` for test functions `φ` (`H` the coefficient
  matrix of a Kähler form, `V > 0` continuous), then `g(x + h) = o(|h|²)` at almost every zero.
* `HasBoundedMetricLaplacian.ae_isLittleO` — **manifold version**: a nonnegative function with
  bounded `ω`-Laplacian vanishes to second order at almost every zero, in every chart.
* `ae_coincideToSecondOrderAt_of_hasBoundedMetricLaplacian` — contact form.
* `roofEnvelope_coincideToSecondOrder_of_hasBoundedMetricLaplacian`,
  `sourceObstacleEnvelope_coincideToSecondOrder_of_hasBoundedMetricLaplacian` — **the first
  assertion of `lma:DNTroof` for the book's `C^{1,1̄}(X)`**, all dimensions.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric Asymptotics
open scoped Topology ContDiff ENNReal NNReal Matrix ComplexOrder

namespace SGPT.Envelopes.LapClass

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Analysis.KahlerNormal SGPT.Analysis.CZ

variable {n : ℕ}

/-! ### The density-point argument with constants -/

/-- **Second-order flatness from mean-value inequalities.**  Let `g ≥ 0` be continuous on
`B̄(c, 4ρ)`.  Assume (a) at every zero `y ∈ B̄(c, ρ)`, `∫_{B̄(y,t)} g ≤ C_a t² vol B̄(y,t)` for
`t < t₀`, and (c) at every `y ∈ B̄(c, 2ρ)`, `g(y) ≤ C₁ R^{-d} ∫_{B̄(y, L R)} g + C₂ R²` for
`R < t₀` (`t₀ ≤ ρ`).  Then `g(x + h) = o(‖h‖²)` at almost every zero `x ∈ B(c, ρ)`. -/
theorem ae_isLittleO_of_meanValue {g : ComplexModel n → ℝ} {c : ComplexModel n} {ρ t₀ Ca C₁ C₂ L : ℝ}
    (hρ : 0 < ρ) (ht₀ : 0 < t₀) (ht₀ρ : t₀ ≤ ρ) (hL : 0 < L)
    (hCa : 0 ≤ Ca) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hg : ContinuousOn g (closedBall c (4 * ρ))) (hg0 : ∀ z ∈ closedBall c (4 * ρ), 0 ≤ g z)
    (ha : ∀ y ∈ closedBall c ρ, g y = 0 → ∀ t : ℝ, 0 < t → t < t₀ →
      ∫ x in closedBall y t, g x ≤ Ca * t ^ 2 * volume.real (closedBall y t))
    (hc : ∀ y ∈ closedBall c (2 * ρ), ∀ R : ℝ, 0 < R → R < t₀ →
      g y ≤ C₁ * (R ^ Module.finrank ℝ (ComplexModel n))⁻¹ * (∫ x in closedBall y (L * R), g x) +
        C₂ * R ^ 2) :
    ∀ᵐ x ∂volume, x ∈ ball c ρ → g x = 0 →
      (fun h => g (x + h)) =o[𝓝 0] (fun h => ‖h‖ ^ 2) := by
  classical
  set d : ℕ := Module.finrank ℝ (ComplexModel n) with hd
  set vb : ℝ := volume.real (ball (0 : ComplexModel n) 1) with hvb
  have hvb0 : 0 ≤ vb := measureReal_nonneg
  set W : Set (ComplexModel n) := closedBall c (4 * ρ) with hWdef
  set S : Set (ComplexModel n) := closedBall c ρ ∩ g ⁻¹' {0} with hSdef
  have hcW : closedBall c ρ ⊆ W := closedBall_subset_closedBall (by linarith)
  have hSc : IsClosed S :=
    (hg.mono hcW).preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
  have hS : MeasurableSet S := hSc.measurableSet
  set G : ComplexModel n → ℝ≥0∞ := fun x => ENNReal.ofReal (W.piecewise g 0 x) with hGdef
  have hGm : Measurable G :=
    ENNReal.measurable_ofReal.comp (hg.measurable_piecewise continuousOn_const
      isClosed_closedBall.measurableSet)
  have hGeq : ∀ x ∈ W, G x = ENNReal.ofReal (g x) := fun x hx => by
    simp only [hGdef, piecewise_eq_of_mem _ _ _ hx]
  have hlint : ∀ {y : ComplexModel n} {r : ℝ}, closedBall y r ⊆ W →
      ∫⁻ x in closedBall y r, G x = ENNReal.ofReal (∫ x in closedBall y r, g x) := by
    intro y r hsub
    have hint : IntegrableOn g (closedBall y r) :=
      (hg.mono hsub).integrableOn_compact (isCompact_closedBall y r)
    rw [ofReal_integral_eq_lintegral_ofReal hint]
    · exact setLIntegral_congr_fun measurableSet_closedBall fun x hx => hGeq x (hsub hx)
    · filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
      exact hg0 x (hsub hx)
  have hdens := SGPT.Okounkov.TranscendentalWNReg.DensityPoint.ae_eventually_measure_closedBall_diff_le
    (μ := volume) hS
  rw [ae_restrict_iff' hS] at hdens
  filter_upwards [hdens] with z hz hzB hz0
  have hzS : z ∈ S := ⟨ball_subset_closedBall hzB, hz0⟩
  have hzc : dist z c ≤ ρ := ball_subset_closedBall hzB
  -- integral flatness at `z`
  have hsub : ∀ y ∈ S, ∀ s : ℝ, 0 < s → dist y z + s < t₀ →
      ∫⁻ x in closedBall y s, G x ≤ ENNReal.ofReal (Ca * s ^ 2) * volume (closedBall y s) := by
    intro y hy s hs hys
    have hst : s < t₀ := by linarith [dist_nonneg (x := y) (y := z)]
    have hyc : dist y c ≤ ρ := hy.1
    have hB : closedBall y s ⊆ W := by
      intro x hx
      rw [mem_closedBall] at hx ⊢
      linarith [dist_triangle x y c]
    rw [hlint hB, ← ENNReal.ofReal_toReal (measure_closedBall_lt_top (x := y) (r := s)).ne,
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (ha y hy.1 hy.2 s hs hst)
  have hflat := SGPT.Okounkov.TranscendentalWNReg.DensityPoint.eventually_setLIntegral_le_of_density
    (μ := volume) hGm hS hzS hCa ht₀ hsub (hz hzS)
  -- pointwise flatness
  rw [isLittleO_iff]
  intro ε hε
  set δ : ℝ := min (min 1 L⁻¹) (ε / (2 * (C₂ + 1))) with hδdef
  have hδ0 : 0 < δ := lt_min (lt_min one_pos (inv_pos.mpr hL)) (by positivity)
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hδL : L * δ ≤ 1 := by
    have : δ ≤ L⁻¹ := (min_le_left _ _).trans (min_le_right _ _)
    calc L * δ ≤ L * L⁻¹ := mul_le_mul_of_nonneg_left this hL.le
      _ = 1 := mul_inv_cancel₀ hL.ne'
  have hC₂δ : C₂ * δ ^ 2 ≤ ε / 2 := by
    have h1 : δ ≤ ε / (2 * (C₂ + 1)) := min_le_right _ _
    have h2 : δ ^ 2 ≤ δ := by nlinarith
    have h3 : C₂ * δ ≤ C₂ * (ε / (2 * (C₂ + 1))) := mul_le_mul_of_nonneg_left h1 hC₂
    have h4 : C₂ * (ε / (2 * (C₂ + 1))) ≤ ε / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc C₂ * δ ^ 2 ≤ C₂ * δ := mul_le_mul_of_nonneg_left h2 hC₂
      _ ≤ ε / 2 := h3.trans h4
  set K₁ : ℝ := C₁ * (4 * 2 ^ d * vb) * (δ ^ d)⁻¹ with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  set ε' : ℝ := ε / (2 * (K₁ + 1)) with hε'def
  have hε' : 0 < ε' := by positivity
  obtain ⟨r₀, hr₀, hr₀sub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hflat ε' hε')
  have hr₀pos : 0 < r₀ := hr₀
  filter_upwards [ball_mem_nhds (0 : ComplexModel n)
    (lt_min (half_pos hr₀pos) (lt_min hρ ht₀))] with h hh
  rw [mem_ball, dist_zero_right, lt_min_iff, lt_min_iff] at hh
  obtain ⟨hh1, hh2, hh3⟩ := hh
  set r : ℝ := ‖h‖ with hrdef
  have hyW : z + h ∈ W := by
    rw [hWdef, mem_closedBall]
    have : dist (z + h) z = r := by rw [dist_eq_norm, add_sub_cancel_left]
    linarith [dist_triangle (z + h) z c]
  have hwy0 : 0 ≤ g (z + h) := hg0 _ hyW
  rw [Real.norm_eq_abs, abs_of_nonneg hwy0, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rcases (norm_nonneg h).eq_or_lt with hr0 | hrpos
  · have h0 : h = 0 := norm_eq_zero.mp hr0.symm
    rw [h0, add_zero, hz0]
    positivity
  set y : ComplexModel n := z + h with hydef
  have hyz : dist y z = r := by rw [hydef, dist_eq_norm, add_sub_cancel_left]
  have hy2 : y ∈ closedBall c (2 * ρ) := by
    rw [mem_closedBall]; linarith [dist_triangle y z c]
  set R : ℝ := δ * r with hRdef
  have hR : 0 < R := mul_pos hδ0 hrpos
  have hRt : R < t₀ := by
    calc R ≤ 1 * r := mul_le_mul_of_nonneg_right hδ1 hrpos.le
      _ < t₀ := by linarith
  have hLR : L * R ≤ r := by
    calc L * R = (L * δ) * r := by ring
      _ ≤ 1 * r := mul_le_mul_of_nonneg_right hδL hrpos.le
      _ = r := one_mul r
  have hmean := hc y hy2 R hR hRt
  -- the ball `B̄(z, 2r)`
  have h2r : 2 * r ∈ Ioo 0 r₀ := ⟨by positivity, by linarith⟩
  have hfl := hr₀sub h2r
  have hzW : closedBall z (2 * r) ⊆ W := by
    intro x hx
    rw [mem_closedBall] at hx ⊢
    linarith [dist_triangle x z c]
  replace hfl : ∫⁻ x in closedBall z (2 * r), G x ≤
      ENNReal.ofReal (ε' * (2 * r) ^ 2) * volume (closedBall z (2 * r)) := hfl
  rw [hlint hzW, ← ENNReal.ofReal_toReal (measure_closedBall_lt_top (x := z) (r := 2 * r)).ne,
    ← ENNReal.ofReal_mul (by positivity)] at hfl
  have hfl' : ∫ x in closedBall z (2 * r), g x ≤ ε' * (2 * r) ^ 2 *
      volume.real (closedBall z (2 * r)) := by
    have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hfl
    simpa [measureReal_def] using this
  have hyzball : closedBall y (L * R) ⊆ closedBall z (2 * r) := by
    intro x hx
    rw [mem_closedBall] at hx ⊢
    linarith [dist_triangle x y z]
  have hmono : ∫ x in closedBall y (L * R), g x ≤ ∫ x in closedBall z (2 * r), g x := by
    refine setIntegral_mono_set ((hg.mono hzW).integrableOn_compact
      (isCompact_closedBall z _)) ?_ (Eventually.of_forall hyzball)
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    exact hg0 x (hzW hx)
  have hvol : volume.real (closedBall z (2 * r)) = (2 * r) ^ d * vb :=
    SGPT.Analysis.CZ.volume_real_closedBall_eq z (by positivity)
  have hfirst : C₁ * (R ^ d)⁻¹ * ∫ x in closedBall y (L * R), g x ≤ ε / 2 * r ^ 2 := by
    have h1 : C₁ * (R ^ d)⁻¹ * ∫ x in closedBall y (L * R), g x ≤
        C₁ * (R ^ d)⁻¹ * (ε' * (2 * r) ^ 2 * ((2 * r) ^ d * vb)) := by
      rw [← hvol]
      exact mul_le_mul_of_nonneg_left (hmono.trans hfl') (by positivity)
    have h2 : C₁ * (R ^ d)⁻¹ * (ε' * (2 * r) ^ 2 * ((2 * r) ^ d * vb)) = ε' * K₁ * r ^ 2 := by
      have hrne : r ≠ 0 := hrpos.ne'
      have hδne : δ ≠ 0 := hδ0.ne'
      rw [hRdef, hK₁, mul_pow, mul_pow, mul_pow]
      field_simp
      ring
    have h3 : ε' * K₁ ≤ ε / 2 := by
      rw [hε'def, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc C₁ * (R ^ d)⁻¹ * ∫ x in closedBall y (L * R), g x ≤ ε' * K₁ * r ^ 2 := h1.trans h2.le
      _ ≤ ε / 2 * r ^ 2 := mul_le_mul_of_nonneg_right h3 (sq_nonneg r)
  have hsecond : C₂ * R ^ 2 ≤ ε / 2 * r ^ 2 := by
    rw [hRdef, mul_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hC₂δ (sq_nonneg r)
  have : g y ≤ ε * r ^ 2 := by linarith
  simpa [hydef] using this

/-! ### The coefficient matrix in normal coordinates -/

namespace NormalBall

open HolomorphicMixedDensity

variable (B : NormalBall n)

theorem continuous_jacobianMatrix : Continuous fun w => jacobianMatrix B.Φ w := by
  refine continuous_pi fun p => continuous_pi fun j => ?_
  have hfun : (fun w => jacobianMatrix B.Φ w p j) = fun w =>
      (EuclideanSpace.proj p : ComplexModel n →L[ℂ] ℂ)
        ((B.L : ComplexModel n →L[ℂ] ComplexModel n)
          (coordinateVector j - (B.c.flip (coordinateVector j)) w)) := by
    funext w
    rw [jacobianMatrix, Matrix.of_apply, fderiv_normalCoord_apply B.z₀ _ B.symm, normalLinear_apply]
    rfl
  rw [hfun]
  exact (EuclideanSpace.proj p : ComplexModel n →L[ℂ] ℂ).continuous.comp
    ((B.L : ComplexModel n →L[ℂ] ComplexModel n).continuous.comp
      (continuous_const.sub (B.c.flip (coordinateVector j)).continuous))

theorem normalizedHermitianMatrix_pullback (a : ComplexModel n → CoordinateRealTwoForm n)
    {w : ComplexModel n} (h11 : IsOneOne (a (B.Φ w))) :
    normalizedHermitianMatrix (pullbackField B.Φ a w) =
      (jacobianMatrix B.Φ w)ᵀ * normalizedHermitianMatrix (a (B.Φ w)) *
        (jacobianMatrix B.Φ w).map (starRingEnd ℂ) := by
  rw [pullbackField_eq_compLinearMap B.z₀ _ B.symm, normalizedHermitianMatrix_compLinearMap h11,
    standardMatrix_normalLinear B.z₀ _ B.symm]

end NormalBall

/-- The coefficient matrix of a continuous field of two-forms is continuous. -/
theorem continuousOn_normalizedHermitianMatrix {U : Set (ComplexModel n)}
    {a : ComplexModel n → CoordinateRealTwoForm n} (ha : ContinuousOn a U) :
    ContinuousOn (fun z => normalizedHermitianMatrix (a z)) U := by
  have hev : ∀ v : Fin 2 → ComplexModel n, ContinuousOn (fun z => a z v) U := fun v =>
    (ContinuousAlternatingMap.apply ℝ (ComplexModel n) ℝ v).continuous.comp_continuousOn ha
  refine continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k => ?_
  simp only [normalizedHermitianMatrix]
  exact continuousOn_const.mul ((Complex.continuous_ofReal.comp_continuousOn (hev _)).sub
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (hev _))))

/-! ### The contact theorem in a chart -/

set_option maxHeartbeats 1600000 in
/-- **Local form of the variable-coefficient contact theorem.** -/
theorem ae_isLittleO_of_kahler_pairing_ball (hn : 0 < n) {U : Set (ComplexModel n)}
    (hU : IsOpen U) {a : ComplexModel n → CoordinateRealTwoForm n} (ha : ContDiffOn ℝ ∞ a U)
    (h11 : ∀ z ∈ U, IsOneOne (a z)) (hpos : ∀ z ∈ U, IsStrictlyPositive (a z))
    (hcl : ∀ z ∈ U, extDeriv a z = 0) {V g : ComplexModel n → ℝ} (hV : ContinuousOn V U)
    (hV0 : ∀ z ∈ U, 0 < V z) (hg : ContinuousOn g U) (hg0 : ∀ z ∈ U, 0 ≤ g z) {M : ℝ}
    (hM : 0 ≤ M)
    (hP : ∀ φ : ComplexModel n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      |∫ z, g z * (V z * ((normalizedHermitianMatrix (a z))⁻¹ * complexHessian φ z).trace.re)| ≤
        M * ∫ z, V z * |φ z|)
    {c : ComplexModel n} {ρ : ℝ} (hρ : 0 < ρ) (hcU : closedBall c (8 * ρ) ⊆ U) :
    ∀ᵐ x ∂volume, x ∈ ball c ρ → g x = 0 →
      (fun h => g (x + h)) =o[𝓝 0] (fun h => ‖h‖ ^ 2) := by
  classical
  set d : ℕ := Module.finrank ℝ (ComplexModel n) with hd
  set K : Set (ComplexModel n) := closedBall c (2 * ρ) with hKdef
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKU : K ⊆ U := (closedBall_subset_closedBall (by linarith)).trans hcU
  obtain ⟨r₀, C0, N0, CH, hr₀, hC0, hN0, hCH, hsm, hsm', hdata⟩ :=
    exists_uniform_normal_data hU ha h11 hpos hcl hK hKU
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  set K' : Set (ComplexModel n) := cthickening δ K with hK'def
  have hK' : IsCompact K' := hK.cthickening
  -- bounds on `K'`
  obtain ⟨Bg, hBg⟩ := hK'.exists_bound_of_continuousOn (hg.mono hδU)
  have hK'ne : K'.Nonempty := ⟨c, self_subset_cthickening _ (mem_closedBall_self (by linarith))⟩
  obtain ⟨zm, hzm, hzmin⟩ := hK'.exists_isMinOn hK'ne (hV.mono hδU)
  obtain ⟨Vp, hVp⟩ := hK'.exists_bound_of_continuousOn (hV.mono hδU)
  set Vm : ℝ := V zm with hVm
  have hVm0 : 0 < Vm := hV0 zm (hδU hzm)
  have hgB : ∀ z ∈ K', g z ≤ max Bg 0 := fun z hz => by
    have := hBg z hz
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  have hVle : ∀ z ∈ K', V z ≤ max Vp 0 := fun z hz => by
    have := hVp z hz
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  have hVge : ∀ z ∈ K', Vm ≤ V z := fun z hz => hzmin hz
  -- the radius
  set r₁ : ℝ := min (min (r₀ / 2) (min 1 ρ)) (min (δ / (5 / 4 * C0 + 1)) (1 / (2 * n * CH + 1)))
    with hr₁def
  have hr₁ : 0 < r₁ := lt_min (lt_min (by positivity) (lt_min one_pos hρ))
    (lt_min (by positivity) (by positivity))
  have hr₁r₀ : r₁ < r₀ := (min_le_left _ _).trans_lt ((min_le_left _ _).trans_lt (by linarith))
  have hr₁1 : r₁ ≤ 1 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr₁ρ : r₁ ≤ ρ := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr₁δ : 5 / 4 * C0 * r₁ ≤ δ := by
    have h1 : r₁ ≤ δ / (5 / 4 * C0 + 1) := (min_le_right _ _).trans (min_le_left _ _)
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 5 / 4 * C0 + 1)
    rw [mul_div_cancel₀ _ (by positivity)] at h2
    nlinarith
  have hr₁CH : (n : ℝ) * CH * r₁ ≤ 1 / 2 := by
    have h1 : r₁ ≤ 1 / (2 * n * CH + 1) := (min_le_right _ _).trans (min_le_right _ _)
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * n * CH + 1)
    rw [mul_one_div_cancel (by positivity)] at h2
    nlinarith
  -- constants
  set m : ℝ := 3 / (4 * N0) with hmdef
  have hm : 0 < m := by positivity
  set jm : ℝ := m ^ d with hjm
  set jp : ℝ := (5 / 4 * C0) ^ d with hjp
  have hjm0 : 0 < jm := by positivity
  set sm : ℝ := jm * Vm with hsmdef
  set sp : ℝ := jp * max Vp 0 with hspdef
  have hsm0 : 0 < sm := by positivity
  have hsp0 : 0 ≤ sp := by positivity
  obtain ⟨C₃, hC₃, hmean⟩ := abs_integral_scaledKernel_sub_le hn (M := M) (B := max Bg 0)
    (sp := sp) (CG := 2 * n * CH) hM (le_max_right _ _) hsp0
  set L : ℝ := 5 / 4 * C0 + 1 with hLdef
  have hL : 0 < L := by positivity
  set vol₁ : ℝ := unitBallVol n with hvol₁
  have hvol₁0 : 0 < vol₁ := unitBallVol_pos
  -- the normal ball at each centre and its mean-value estimate
  have hcenter : ∀ y ∈ K, ∃ B : NormalBall n, B.z₀ = y ∧ B.r₀ = r₁ ∧ B.C0 = C0 ∧ B.N0 = N0 ∧
      (∀ ζ ∈ ball (0 : ComplexModel n) r₁, B.Φ ζ ∈ K') ∧
      ∀ R : ℝ, 0 < R → R < r₁ →
        |(∫ ζ, g (B.Φ ζ) * (|LinearMap.det (fderiv ℝ B.Φ ζ : ComplexModel n →ₗ[ℝ] ComplexModel n)| *
            V (B.Φ ζ)) * scaledKernel n R ζ) -
          g y * (|LinearMap.det (fderiv ℝ B.Φ 0 : ComplexModel n →ₗ[ℝ] ComplexModel n)| * V y)| ≤
          C₃ * R ^ 2 := by
    intro y hy
    obtain ⟨L₀, c₀, hsymm, hLn, hLinv, hcn, hΦU, hH⟩ := hdata y hy
    let B : NormalBall n :=
      { z₀ := y, L := L₀, c := c₀, r₀ := r₁, C0 := C0, N0 := N0, symm := hsymm, r₀_pos := hr₁
        C0_nonneg := hC0, N0_pos := hN0, norm_L := hLn, norm_Linv := hLinv, norm_c := hcn
        small := (mul_le_mul_of_nonneg_left hr₁r₀.le hC0).trans hsm
        small' := by
          have := mul_le_mul_of_nonneg_left hr₁r₀.le (mul_nonneg hC0 hC0)
          nlinarith [mul_le_mul_of_nonneg_right this hN0.le] }
    have hΦ0 : B.Φ 0 = y := normalCoord_zero _ _ _
    have hball : ∀ ζ ∈ ball (0 : ComplexModel n) r₁, ζ ∈ ball (0 : ComplexModel n) r₀ :=
      fun ζ hζ => ball_subset_ball hr₁r₀.le hζ
    have hΦK' : ∀ ζ ∈ ball (0 : ComplexModel n) r₁, B.Φ ζ ∈ K' := by
      intro ζ hζ
      refine Metric.mem_cthickening_of_dist_le _ y _ _ hy ?_
      rw [dist_eq_norm]
      have h1 := B.norm_Φ_sub_le hζ
      rw [mem_ball, dist_zero_right] at hζ
      calc ‖B.Φ ζ - y‖ ≤ 5 / 4 * C0 * ‖ζ‖ := h1
        _ ≤ 5 / 4 * C0 * r₁ := mul_le_mul_of_nonneg_left hζ.le (by positivity)
        _ ≤ δ := hr₁δ
    have hΦU' : ∀ ζ ∈ ball (0 : ComplexModel n) r₁, B.Φ ζ ∈ U := fun ζ hζ => hδU (hΦK' ζ hζ)
    refine ⟨B, rfl, rfl, rfl, rfl, hΦK', fun R hR hRr => ?_⟩
    -- the data of the mean-value estimate
    set w : ComplexModel n → ℝ := fun ζ => g (B.Φ ζ) with hwdef
    set sf : ComplexModel n → ℝ := fun ζ =>
      |LinearMap.det (fderiv ℝ B.Φ ζ : ComplexModel n →ₗ[ℝ] ComplexModel n)| * V (B.Φ ζ) with hsfdef
    set hq : ComplexModel n → Matrix (Fin n) (Fin n) ℂ := fun ζ =>
      normalizedHermitianMatrix (pullbackField B.Φ a ζ) with hqdef
    set G : ComplexModel n → Matrix (Fin n) (Fin n) ℂ := fun ζ => (hq ζ)⁻¹ with hGdef
    have hΦc : Continuous B.Φ := B.contDiff_Φ.continuous
    have hmaps : MapsTo B.Φ (ball 0 r₁) U := fun ζ hζ => hΦU' ζ hζ
    have hwc : ContinuousOn w (ball 0 r₁) := hg.comp hΦc.continuousOn hmaps
    have hsc : ContinuousOn sf (ball 0 r₁) :=
      B.continuous_abs_det_fderiv.continuousOn.mul (hV.comp hΦc.continuousOn hmaps)
    -- the coefficient matrix and its inverse
    have hqeq : ∀ ζ ∈ ball (0 : ComplexModel n) r₁, hq ζ =
        (HolomorphicMixedDensity.jacobianMatrix B.Φ ζ)ᵀ * normalizedHermitianMatrix (a (B.Φ ζ)) *
          (HolomorphicMixedDensity.jacobianMatrix B.Φ ζ).map (starRingEnd ℂ) := fun ζ hζ =>
      B.normalizedHermitianMatrix_pullback a (h11 _ (hΦU' ζ hζ))
    have hqpd : ∀ ζ ∈ ball (0 : ComplexModel n) r₁, (hq ζ).PosDef := fun ζ hζ => by
      rw [hqeq ζ hζ]
      exact posDef_transpose_mul_mul_conj
        (ConcentrationMassComparison.normalizedHermitianMatrix_posDef (h11 _ (hΦU' ζ hζ))
          (hpos _ (hΦU' ζ hζ))) (B.isUnit_det_jacobian hζ)
    have hJc := B.continuous_jacobianMatrix
    have hHc : ContinuousOn (fun z => normalizedHermitianMatrix (a z)) U :=
      continuousOn_normalizedHermitianMatrix ha.continuousOn
    have hqc : ContinuousOn hq (ball 0 r₁) := by
      refine ContinuousOn.congr ?_ hqeq
      exact ((hJc.matrix_transpose.continuousOn.mul (hHc.comp hΦc.continuousOn hmaps)).mul
        (hJc.matrix_map Complex.continuous_conj).continuousOn)
    have hGc : ContinuousOn G (ball 0 r₁) := by
      have hdet : ContinuousOn (fun ζ => (hq ζ).det) (ball 0 r₁) :=
        (continuous_id.matrix_det).comp_continuousOn hqc
      have hne : ∀ ζ ∈ ball (0 : ComplexModel n) r₁, (hq ζ).det ≠ 0 := fun ζ hζ =>
        (hqpd ζ hζ).det_pos.ne'
      refine ContinuousOn.congr ((hdet.inv₀ hne).smul
        ((continuous_id.matrix_adjugate).comp_continuousOn hqc)) fun ζ _ => ?_
      simp only [hGdef, Matrix.inv_def, Ring.inverse_eq_inv]
      rfl
    -- the bounds
    have hw0 : ∀ ζ ∈ ball (0 : ComplexModel n) r₁, 0 ≤ w ζ := fun ζ hζ => hg0 _ (hΦU' ζ hζ)
    have hwB : ∀ ζ ∈ ball (0 : ComplexModel n) r₁, w ζ ≤ max Bg 0 := fun ζ hζ =>
      hgB _ (hΦK' ζ hζ)
    have hs0 : ∀ ζ ∈ ball (0 : ComplexModel n) r₁, 0 ≤ sf ζ := fun ζ hζ =>
      mul_nonneg (abs_nonneg _) (hV0 _ (hΦU' ζ hζ)).le
    have hsp : ∀ ζ ∈ ball (0 : ComplexModel n) r₁, sf ζ ≤ sp := fun ζ hζ =>
      mul_le_mul (B.abs_det_fderiv_le hζ) (hVle _ (hΦK' ζ hζ)) (hV0 _ (hΦU' ζ hζ)).le
        (by positivity)
    have hG : ∀ ζ ∈ ball (0 : ComplexModel n) r₁, ∀ j k,
        ‖(G ζ - 1) j k‖ ≤ 2 * n * CH * ‖ζ‖ ^ 2 := by
      intro ζ hζ j k
      have hζ1 : ‖ζ‖ ≤ 1 := by
        have := mem_ball.mp hζ; rw [dist_zero_right] at this; linarith
      have hsmall : (n : ℝ) * (CH * ‖ζ‖ ^ 2) ≤ 1 / 2 := by
        have h1 : ‖ζ‖ ^ 2 ≤ r₁ := by
          have := mem_ball.mp hζ; rw [dist_zero_right] at this
          nlinarith [norm_nonneg ζ]
        calc (n : ℝ) * (CH * ‖ζ‖ ^ 2) ≤ n * (CH * r₁) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hCH) (by positivity)
          _ = n * CH * r₁ := by ring
          _ ≤ 1 / 2 := hr₁CH
      have h := inv_one_add_sub_one_entry_le (hq ζ - 1) (by positivity) (hH ζ (hball ζ hζ))
        hsmall j k
      rw [add_sub_cancel] at h
      calc ‖(G ζ - 1) j k‖ = ‖((hq ζ)⁻¹ - 1) j k‖ := rfl
        _ ≤ 2 * n * (CH * ‖ζ‖ ^ 2) := h
        _ = 2 * n * CH * ‖ζ‖ ^ 2 := by ring
    -- the transported pairing
    have hP' : ∀ ψ : ComplexModel n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ ball 0 r₁ →
        |∫ ζ, w ζ * sf ζ * (G ζ * complexHessian ψ ζ).trace.re| ≤ M * ∫ ζ, sf ζ * |ψ ζ| := by
      intro ψ hψ hψc hψt
      have hφt : tsupport (B.pushTest ψ) ⊆ U :=
        (B.tsupport_pushTest_subset hψc).trans fun z ⟨ζ, hζ, hζz⟩ => hζz ▸ hΦU' ζ (hψt hζ)
      have h1 := hP (B.pushTest ψ) (B.contDiff_pushTest hψ hψc hψt)
        (B.hasCompactSupport_pushTest hψc) hφt
      rw [B.integral_pushTest_eq a (fun ζ hζ => h11 _ (hΦU' ζ hζ)) hψ hψc hψt g V,
        B.integral_abs_pushTest_eq hψt V] at h1
      convert h1 using 2
      refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
      simp only [hwdef, hsfdef, hGdef, hqdef]
      ring
    have := hmean hwc hsc hGc hw0 hwB hs0 hsp hG hP' R hR hRr
    simpa only [hwdef, hsfdef, hΦ0] using this
  -- common facts about the normal balls
  have hderivOn : ∀ (B : NormalBall n) (S : Set (ComplexModel n)), ∀ x ∈ S,
      HasFDerivWithinAt B.Φ (fderiv ℝ B.Φ x) S x := fun B S x _ =>
    ((B.contDiff_Φ.differentiable (by simp)) x).hasFDerivAt.hasFDerivWithinAt
  set vb : ℝ := volume.real (ball (0 : ComplexModel n) 1) with hvbdef
  have hvb0 : 0 < vb := by
    rw [hvbdef, measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  have hLr₁ : L * r₁ ≤ δ := by
    have h1 : r₁ ≤ δ / (5 / 4 * C0 + 1) := (min_le_right _ _).trans (min_le_left _ _)
    have h2 := mul_le_mul_of_nonneg_left h1 hL.le
    rwa [hLdef, mul_div_cancel₀ _ (by positivity)] at h2
  set t₀ : ℝ := min (m * r₁ / 2) r₁ with ht₀def
  have ht₀ : 0 < t₀ := lt_min (by positivity) hr₁
  have ht₀ρ : t₀ ≤ ρ := (min_le_right _ _).trans hr₁ρ
  have ht₀r : t₀ ≤ r₁ := min_le_right _ _
  set Ca : ℝ := jp * vol₁ * C₃ * (2 / m) ^ (d + 2) / (sm * vb) with hCadef
  set C₁ : ℝ := sp * 2 ^ d / (vol₁ * jm * sm) with hC₁def
  set C₂ : ℝ := C₃ / sm with hC₂def
  have hcompact_img : ∀ (B : NormalBall n) {ρ' : ℝ}, B.r₀ = r₁ → ρ' < r₁ →
      (∀ ζ ∈ ball (0 : ComplexModel n) r₁, B.Φ ζ ∈ K') →
      IsCompact (B.Φ '' closedBall 0 ρ') ∧ B.Φ '' closedBall 0 ρ' ⊆ K' := by
    intro B ρ' _ hρ' hK'B
    exact ⟨(isCompact_closedBall _ _).image B.contDiff_Φ.continuous,
      fun z ⟨ζ, hζ, hζz⟩ => hζz ▸ hK'B ζ (closedBall_subset_ball hρ' hζ)⟩
  -- (a): quadratic averages at the zeros
  have ha : ∀ y ∈ closedBall c ρ, g y = 0 → ∀ t : ℝ, 0 < t → t < t₀ →
      ∫ x in closedBall y t, g x ≤ Ca * t ^ 2 * volume.real (closedBall y t) := by
    intro y hy hy0 t ht htt
    have hyK : y ∈ K := closedBall_subset_closedBall (by linarith) hy
    obtain ⟨B, hBz, hBr, hBC, hBN, hΦK', hB⟩ := hcenter y hyK
    set ρζ : ℝ := t / m with hρζdef
    have hρζ : 0 < ρζ := by positivity
    have hρζr : ρζ < r₁ / 2 := by
      rw [hρζdef, div_lt_iff₀ hm]
      have := htt.trans_le (min_le_left _ _)
      linarith
    set R : ℝ := 2 * ρζ with hRdef
    have hR : 0 < R := by positivity
    have hRr : R < r₁ := by linarith
    have hρζR : ρζ = R / 2 := by rw [hRdef]; ring
    have hsubB : closedBall (0 : ComplexModel n) ρζ ⊆ ball 0 r₁ :=
      closedBall_subset_ball (by linarith)
    have hsubB' : closedBall (0 : ComplexModel n) ρζ ⊆ ball 0 B.r₀ := hBr ▸ hsubB
    obtain ⟨himgc, himgK'⟩ := hcompact_img B hBr (by linarith : ρζ < r₁) hΦK'
    -- the inclusion
    have hincl : closedBall y t ⊆ B.Φ '' closedBall 0 ρζ := by
      have h := B.closedBall_subset_image hρζ.le (by rw [hBr]; linarith)
      rw [hBz, hBN] at h
      have ht' : 3 / (4 * N0) * ρζ = t := by
        rw [hρζdef, hmdef]; field_simp
      rwa [ht'] at h
    -- integrability
    have hgimg : IntegrableOn g (B.Φ '' closedBall 0 ρζ) :=
      (hg.mono (himgK'.trans hδU)).integrableOn_compact himgc
    have hgΦc : ContinuousOn (fun ζ => g (B.Φ ζ)) (ball 0 r₁) :=
      hg.comp B.contDiff_Φ.continuous.continuousOn fun ζ hζ => hδU (hΦK' ζ hζ)
    have hdetc := B.continuous_abs_det_fderiv
    have hsfc : ContinuousOn (fun ζ => |LinearMap.det (fderiv ℝ B.Φ ζ :
        ComplexModel n →ₗ[ℝ] ComplexModel n)| * V (B.Φ ζ)) (ball 0 r₁) :=
      hdetc.continuousOn.mul (hV.comp B.contDiff_Φ.continuous.continuousOn
        fun ζ hζ => hδU (hΦK' ζ hζ))
    -- step 1: the ball lies in the image
    have h1 : ∫ x in closedBall y t, g x ≤ ∫ x in B.Φ '' closedBall 0 ρζ, g x :=
      setIntegral_mono_set hgimg
        (by filter_upwards [ae_restrict_mem (himgc.isClosed.measurableSet)] with x hx
            exact hg0 x (hδU (himgK' hx)))
        (Eventually.of_forall hincl)
    -- step 2: change of variables
    have h2 : ∫ x in B.Φ '' closedBall 0 ρζ, g x =
        ∫ ζ in closedBall 0 ρζ, |LinearMap.det (fderiv ℝ B.Φ ζ :
          ComplexModel n →ₗ[ℝ] ComplexModel n)| * g (B.Φ ζ) := by
      rw [integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_closedBall
        (hderivOn B _) (B.injOn.mono hsubB') g]
      rfl
    have h3 : ∫ ζ in closedBall 0 ρζ, |LinearMap.det (fderiv ℝ B.Φ ζ :
          ComplexModel n →ₗ[ℝ] ComplexModel n)| * g (B.Φ ζ) ≤
        ∫ ζ in closedBall 0 ρζ, jp * g (B.Φ ζ) := by
      refine setIntegral_mono_on ((hdetc.continuousOn.mul (hgΦc.mono hsubB)).integrableOn_compact
        (isCompact_closedBall _ _)) ((continuousOn_const.mul (hgΦc.mono hsubB)).integrableOn_compact
        (isCompact_closedBall _ _)) measurableSet_closedBall fun ζ hζ => ?_
      have hdet := B.abs_det_fderiv_le (hsubB' hζ)
      rw [hBC] at hdet
      exact mul_le_mul_of_nonneg_right hdet (hg0 _ (hδU (hΦK' ζ (hsubB hζ))))
    -- step 3: the kernel dominates the ball average
    have hkint : Integrable fun ζ => g (B.Φ ζ) * (|LinearMap.det (fderiv ℝ B.Φ ζ :
        ComplexModel n →ₗ[ℝ] ComplexModel n)| * V (B.Φ ζ)) * scaledKernel n R ζ :=
      integrable_of_continuousOn_ball ((hgΦc.mul hsfc).mul
        (continuous_scaledKernel R).continuousOn) hRr fun ζ hζ => by
          rw [scaledKernel_eq_zero_of_lt R hR hζ, mul_zero]
    have hkpos : ∀ ζ, 0 ≤ g (B.Φ ζ) * (|LinearMap.det (fderiv ℝ B.Φ ζ :
        ComplexModel n →ₗ[ℝ] ComplexModel n)| * V (B.Φ ζ)) * scaledKernel n R ζ := by
      intro ζ
      by_cases hζ : ‖ζ‖ ≤ R
      · have hζb : ζ ∈ ball (0 : ComplexModel n) r₁ := by
          rw [mem_ball, dist_zero_right]; linarith
        exact mul_nonneg (mul_nonneg (hg0 _ (hδU (hΦK' ζ hζb))) (mul_nonneg (abs_nonneg _)
          (hV0 _ (hδU (hΦK' ζ hζb))).le)) (scaledKernel_nonneg R hR ζ)
      · rw [scaledKernel_eq_zero_of_lt R hR (lt_of_not_ge hζ), mul_zero]
    have h4 : ∫ ζ in closedBall 0 ρζ, g (B.Φ ζ) ≤ R ^ d * vol₁ / sm *
        ∫ ζ, g (B.Φ ζ) * (|LinearMap.det (fderiv ℝ B.Φ ζ :
          ComplexModel n →ₗ[ℝ] ComplexModel n)| * V (B.Φ ζ)) * scaledKernel n R ζ := by
      rw [← integral_const_mul]
      refine (setIntegral_mono_on ((hgΦc.mono hsubB).integrableOn_compact
        (isCompact_closedBall _ _)) (hkint.const_mul _).integrableOn measurableSet_closedBall
        fun ζ hζ => ?_).trans (setIntegral_le_integral (hkint.const_mul _)
          (Eventually.of_forall fun ζ => mul_nonneg (by positivity) (hkpos ζ)))
      have hζb := hsubB hζ
      have hg0' := hg0 _ (hδU (hΦK' ζ hζb))
      have hdet := B.le_abs_det_fderiv (hsubB' hζ)
      rw [hBN] at hdet
      have hVz := hVge _ (hΦK' ζ hζb)
      have hk := le_scaledKernel (n := n) R hR (ζ := ζ) (by
        rw [← hρζR]; simpa using hζ)
      have hs : sm ≤ |LinearMap.det (fderiv ℝ B.Φ ζ : ComplexModel n →ₗ[ℝ] ComplexModel n)| *
          V (B.Φ ζ) := mul_le_mul hdet hVz hVm0.le (abs_nonneg _)
      have hprod : 1 ≤ R ^ d * vol₁ / sm * ((|LinearMap.det (fderiv ℝ B.Φ ζ :
          ComplexModel n →ₗ[ℝ] ComplexModel n)| * V (B.Φ ζ)) * scaledKernel n R ζ) := by
        have hRd : 0 < R ^ d := by positivity
        have hu := (unitBallVol_pos (n := n)).ne'
        calc (1 : ℝ) = R ^ d * vol₁ / sm * (sm * ((R ^ d)⁻¹ * (unitBallVol n)⁻¹)) := by
              rw [hvol₁]; field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul hs hk
              (mul_nonneg (by positivity) (inv_nonneg.mpr unitBallVol_pos.le))
              (hsm0.le.trans hs)) (div_nonneg (mul_nonneg hRd.le hvol₁0.le) hsm0.le)
      calc g (B.Φ ζ) = g (B.Φ ζ) * 1 := (mul_one _).symm
        _ ≤ g (B.Φ ζ) * (R ^ d * vol₁ / sm * ((|LinearMap.det (fderiv ℝ B.Φ ζ :
            ComplexModel n →ₗ[ℝ] ComplexModel n)| * V (B.Φ ζ)) * scaledKernel n R ζ)) :=
            mul_le_mul_of_nonneg_left hprod hg0'
        _ = _ := by ring
    -- step 4: the mean-value estimate at a zero
    have h5 := hB R hR hRr
    rw [hy0, zero_mul, sub_zero] at h5
    have h5' := (le_abs_self _).trans h5
    -- conclusion
    have hvolt : volume.real (closedBall y t) = t ^ d * vb :=
      SGPT.Analysis.CZ.volume_real_closedBall_eq y ht.le
    have hRval : R = 2 / m * t := by rw [hRdef, hρζdef]; ring
    have hA : ∫ x in closedBall y t, g x ≤ jp * ∫ ζ in closedBall 0 ρζ, g (B.Φ ζ) := by
      rw [← integral_const_mul]
      exact h1.trans (h2.le.trans h3)
    have hnn : 0 ≤ R ^ d * vol₁ / sm := div_nonneg (mul_nonneg (by positivity) hvol₁0.le) hsm0.le
    have hB' : ∫ ζ in closedBall 0 ρζ, g (B.Φ ζ) ≤ R ^ d * vol₁ / sm * (C₃ * R ^ 2) :=
      h4.trans (mul_le_mul_of_nonneg_left h5' hnn)
    have hjp0 : 0 ≤ jp := by rw [hjp]; positivity
    calc ∫ x in closedBall y t, g x ≤ jp * (R ^ d * vol₁ / sm * (C₃ * R ^ 2)) :=
          hA.trans (mul_le_mul_of_nonneg_left hB' hjp0)
      _ = Ca * t ^ 2 * volume.real (closedBall y t) := by
          have hmne : m ≠ 0 := hm.ne'
          have hsmne : sm ≠ 0 := hsm0.ne'
          have hvbne : vb ≠ 0 := hvb0.ne'
          rw [hvolt, hRval, hCadef, mul_pow, mul_pow, pow_add]
          field_simp
  -- (c): the sub-mean-value inequality
  have hc : ∀ y ∈ closedBall c (2 * ρ), ∀ R : ℝ, 0 < R → R < t₀ →
      g y ≤ C₁ * (R ^ d)⁻¹ * (∫ x in closedBall y (L * R), g x) + C₂ * R ^ 2 := by
    intro y hyK R hR hRt
    obtain ⟨B, hBz, hBr, hBC, hBN, hΦK', hB⟩ := hcenter y hyK
    have hRr : R < r₁ := hRt.trans_le ht₀r
    have hsubB : closedBall (0 : ComplexModel n) R ⊆ ball 0 r₁ := closedBall_subset_ball hRr
    have hsubB' : closedBall (0 : ComplexModel n) R ⊆ ball 0 B.r₀ := hBr ▸ hsubB
    have h0b : (0 : ComplexModel n) ∈ ball (0 : ComplexModel n) r₁ := mem_ball_self hr₁
    have hgΦc : ContinuousOn (fun ζ => g (B.Φ ζ)) (ball 0 r₁) :=
      hg.comp B.contDiff_Φ.continuous.continuousOn fun ζ hζ => hδU (hΦK' ζ hζ)
    have hdetc := B.continuous_abs_det_fderiv
    have hyLR : closedBall y (L * R) ⊆ K' := fun x hx =>
      Metric.mem_cthickening_of_dist_le _ y _ _ hyK ((mem_closedBall.mp hx).trans
        ((mul_le_mul_of_nonneg_left hRr.le hL.le).trans hLr₁))
    -- the value at the centre
    have hs0 : sm ≤ |LinearMap.det (fderiv ℝ B.Φ 0 : ComplexModel n →ₗ[ℝ] ComplexModel n)| * V y := by
      have hdet := B.le_abs_det_fderiv (hBr ▸ h0b)
      rw [hBN] at hdet
      have hyK' : y ∈ K' := self_subset_cthickening _ hyK
      exact mul_le_mul hdet (hVge y hyK') hVm0.le (abs_nonneg _)
    have h1 := (abs_le.mp (hB R hR hRr)).1
    -- the kernel average is bounded by the ball average
    have h2 : ∫ ζ, g (B.Φ ζ) * (|LinearMap.det (fderiv ℝ B.Φ ζ :
          ComplexModel n →ₗ[ℝ] ComplexModel n)| * V (B.Φ ζ)) * scaledKernel n R ζ ≤
        sp * ((R ^ d)⁻¹ * (2 ^ d / vol₁)) * ∫ ζ in closedBall 0 R, g (B.Φ ζ) := by
      rw [← integral_const_mul, ← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := closedBall (0 : ComplexModel n) R) fun ζ hζ => by
          rw [scaledKernel_eq_zero_of_lt R hR (by simpa using hζ), mul_zero]]
      refine setIntegral_mono_on ?_ ((continuousOn_const.mul (hgΦc.mono hsubB)).integrableOn_compact
        (isCompact_closedBall _ _)) measurableSet_closedBall fun ζ hζ => ?_
      · exact ((hgΦc.mono hsubB).mul ((hdetc.continuousOn.mul (hV.comp
          B.contDiff_Φ.continuous.continuousOn fun ζ hζ => hδU (hΦK' ζ hζ))).mono hsubB) |>.mul
          (continuous_scaledKernel R).continuousOn).integrableOn_compact (isCompact_closedBall _ _)
      · have hζb := hsubB hζ
        have hg0' := hg0 _ (hδU (hΦK' ζ hζb))
        have hdet := B.abs_det_fderiv_le (hsubB' hζ)
        rw [hBC] at hdet
        have hVz := hVle _ (hΦK' ζ hζb)
        have hk := scaledKernel_le (n := n) R hR ζ
        have hsfle : |LinearMap.det (fderiv ℝ B.Φ ζ : ComplexModel n →ₗ[ℝ] ComplexModel n)| *
            V (B.Φ ζ) ≤ sp := mul_le_mul hdet hVz (hV0 _ (hδU (hΦK' ζ hζb))).le (by positivity)
        have hsf0 : 0 ≤ |LinearMap.det (fderiv ℝ B.Φ ζ : ComplexModel n →ₗ[ℝ] ComplexModel n)| *
            V (B.Φ ζ) := mul_nonneg (abs_nonneg _) (hV0 _ (hδU (hΦK' ζ hζb))).le
        calc g (B.Φ ζ) * (|LinearMap.det (fderiv ℝ B.Φ ζ : ComplexModel n →ₗ[ℝ] ComplexModel n)| *
              V (B.Φ ζ)) * scaledKernel n R ζ
            ≤ g (B.Φ ζ) * sp * ((R ^ d)⁻¹ * (2 ^ d / vol₁)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hsfle hg0') hk (scaledKernel_nonneg R hR ζ)
                (mul_nonneg hg0' hsp0)
          _ = sp * ((R ^ d)⁻¹ * (2 ^ d / vol₁)) * g (B.Φ ζ) := by ring
    -- back to a ball of `ℂⁿ`
    have hcompact := hcompact_img B hBr hRr hΦK'
    have h3 : jm * ∫ ζ in closedBall 0 R, g (B.Φ ζ) ≤ ∫ x in closedBall y (L * R), g x := by
      rw [← integral_const_mul]
      calc ∫ ζ in closedBall 0 R, jm * g (B.Φ ζ)
          ≤ ∫ ζ in closedBall 0 R, |LinearMap.det (fderiv ℝ B.Φ ζ :
              ComplexModel n →ₗ[ℝ] ComplexModel n)| * g (B.Φ ζ) := by
            refine setIntegral_mono_on ((continuousOn_const.mul (hgΦc.mono hsubB)).integrableOn_compact
              (isCompact_closedBall _ _)) ((hdetc.continuousOn.mul
              (hgΦc.mono hsubB)).integrableOn_compact (isCompact_closedBall _ _))
              measurableSet_closedBall fun ζ hζ => ?_
            have hdet := B.le_abs_det_fderiv (hsubB' hζ)
            rw [hBN] at hdet
            exact mul_le_mul_of_nonneg_right hdet (hg0 _ (hδU (hΦK' ζ (hsubB hζ))))
        _ = ∫ x in B.Φ '' closedBall 0 R, g x := by
            rw [integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_closedBall
              (hderivOn B _) (B.injOn.mono hsubB') g]
            rfl
        _ ≤ ∫ x in closedBall y (L * R), g x := by
            refine setIntegral_mono_set ((hg.mono (hyLR.trans hδU)).integrableOn_compact
              (isCompact_closedBall _ _)) ?_ (Eventually.of_forall ?_)
            · filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
              exact hg0 x (hδU (hyLR hx))
            · rintro _ ⟨ζ, hζ, rfl⟩
              show B.Φ ζ ∈ closedBall y (L * R)
              rw [mem_closedBall, dist_eq_norm, ← hBz]
              have := B.norm_Φ_sub_le (hsubB' hζ)
              rw [hBC] at this
              have hζR : ‖ζ‖ ≤ R := by simpa using hζ
              calc ‖B.Φ ζ - B.z₀‖ ≤ 5 / 4 * C0 * ‖ζ‖ := this
                _ ≤ L * R := by rw [hLdef]; nlinarith [norm_nonneg ζ]
    -- conclusion
    have hgy0 : 0 ≤ g y := hg0 y (hδU (self_subset_cthickening _ hyK))
    have hI0 : 0 ≤ ∫ ζ in closedBall 0 R, g (B.Φ ζ) :=
      setIntegral_nonneg measurableSet_closedBall fun ζ hζ => hg0 _ (hδU (hΦK' ζ (hsubB hζ)))
    have hmain : g y * sm ≤ sp * ((R ^ d)⁻¹ * (2 ^ d / vol₁)) * (∫ x in closedBall y (L * R), g x) / jm
        + C₃ * R ^ 2 := by
      have e1 : g y * sm ≤ g y * (|LinearMap.det (fderiv ℝ B.Φ 0 :
          ComplexModel n →ₗ[ℝ] ComplexModel n)| * V y) := mul_le_mul_of_nonneg_left hs0 hgy0
      have e2 : sp * ((R ^ d)⁻¹ * (2 ^ d / vol₁)) * ∫ ζ in closedBall 0 R, g (B.Φ ζ) ≤
          sp * ((R ^ d)⁻¹ * (2 ^ d / vol₁)) * (∫ x in closedBall y (L * R), g x) / jm := by
        rw [le_div_iff₀ hjm0, mul_assoc]
        exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hsp0 (mul_nonneg (by positivity)
          (div_nonneg (by positivity) hvol₁0.le)))
      linarith
    rw [hC₁def, hC₂def]
    have hsmne : sm ≠ 0 := hsm0.ne'
    have hjmne : jm ≠ 0 := hjm0.ne'
    have hvne : vol₁ ≠ 0 := hvol₁0.ne'
    have hsm' : g y = g y * sm / sm := by field_simp
    rw [hsm', div_le_iff₀ hsm0]
    calc g y * sm ≤ _ := hmain
      _ = (sp * 2 ^ d / (vol₁ * jm * sm) * (R ^ d)⁻¹ * (∫ x in closedBall y (L * R), g x) +
          C₃ / sm * R ^ 2) * sm := by field_simp
  have hC₁0 : 0 ≤ C₁ := div_nonneg (mul_nonneg hsp0 (by positivity))
    (mul_nonneg (mul_nonneg hvol₁0.le hjm0.le) hsm0.le)
  have hC₂0 : 0 ≤ C₂ := div_nonneg hC₃ hsm0.le
  have hCa0 : 0 ≤ Ca := div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by rw [hjp]; positivity)
    hvol₁0.le) hC₃) (by positivity)) (mul_nonneg hsm0.le hvb0.le)
  have h4U : closedBall c (4 * ρ) ⊆ U := (closedBall_subset_closedBall (by linarith)).trans hcU
  exact ae_isLittleO_of_meanValue hρ ht₀ ht₀ρ hL hCa0 hC₁0 hC₂0 (hg.mono h4U)
    (fun z hz => hg0 z (h4U hz)) ha hc

/-- **The variable-coefficient contact theorem in a chart.**  Let `a` be a smooth field of closed
strictly positive real `(1,1)`-forms on an open `U ⊆ ℂⁿ` (a Kähler form in a chart), `H` its
coefficient matrix, `V > 0` continuous, and let `g ≥ 0` be continuous on `U` with
`|∫ g V Re tr(H⁻¹ ∂∂̄φ)| ≤ M ∫ V |φ|` for all smooth `φ` with compact support in `U` (a bounded
metric Laplacian).  Then `g(x + h) = o(‖h‖²)` at almost every point `x ∈ U` with `g(x) = 0`. -/
theorem ae_isLittleO_of_kahler_pairing {U : Set (ComplexModel n)} (hU : IsOpen U)
    {a : ComplexModel n → CoordinateRealTwoForm n} (ha : ContDiffOn ℝ ∞ a U)
    (h11 : ∀ z ∈ U, IsOneOne (a z)) (hpos : ∀ z ∈ U, IsStrictlyPositive (a z))
    (hcl : ∀ z ∈ U, extDeriv a z = 0) {V g : ComplexModel n → ℝ} (hV : ContinuousOn V U)
    (hV0 : ∀ z ∈ U, 0 < V z) (hg : ContinuousOn g U) (hg0 : ∀ z ∈ U, 0 ≤ g z) {M : ℝ}
    (hM : 0 ≤ M)
    (hP : ∀ φ : ComplexModel n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      |∫ z, g z * (V z * ((normalizedHermitianMatrix (a z))⁻¹ * complexHessian φ z).trace.re)| ≤
        M * ∫ z, V z * |φ z|) :
    ∀ᵐ x ∂volume, x ∈ U → g x = 0 → (fun h => g (x + h)) =o[𝓝 0] (fun h => ‖h‖ ^ 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine Eventually.of_forall fun x _ hx0 => ?_
    have hconst : (fun h : ComplexModel 0 => g (x + h)) = fun _ => 0 := by
      funext h
      rw [Subsingleton.elim h 0, add_zero, hx0]
    rw [hconst]
    exact isLittleO_zero _ _
  have hrad : ∀ x : U, ∃ ρ : ℝ, 0 < ρ ∧ closedBall (x : ComplexModel n) (8 * ρ) ⊆ U := by
    intro x
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x x.2
    exact ⟨ε / 16, by positivity, (closedBall_subset_ball (by linarith)).trans hεU⟩
  choose ρ hρ hρU using hrad
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : U => ball (x : ComplexModel n) (ρ x)) fun x => isOpen_ball
  have hloc : ∀ x ∈ T, ∀ᵐ y ∂volume, y ∈ ball (x : ComplexModel n) (ρ x) → g y = 0 →
      (fun h => g (y + h)) =o[𝓝 0] (fun h => ‖h‖ ^ 2) := fun x _ =>
    ae_isLittleO_of_kahler_pairing_ball hn hU ha h11 hpos hcl hV hV0 hg hg0 hM hP (hρ x) (hρU x)
  have hall := (ae_ball_iff hTc).mpr hloc
  filter_upwards [hall] with y hy hyU hy0
  have hmem : y ∈ ⋃ x : U, ball (x : ComplexModel n) (ρ x) :=
    mem_iUnion.mpr ⟨⟨y, hyU⟩, mem_ball_self (hρ _)⟩
  rw [← hTU] at hmem
  obtain ⟨x, hxT, hyx⟩ := mem_iUnion₂.mp hmem
  exact hy x hxT hyx hy0

/-! ### On the manifold -/

section Manifold

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

/-- The class `C^{1,1̄}_ω(X)` is a vector space: differences. -/
theorem HasBoundedMetricLaplacian.sub (w : KahlerBackground N Y) {f v : Y → ℝ}
    (hf : HasBoundedMetricLaplacian w f) (hv : HasBoundedMetricLaplacian w v) :
    HasBoundedMetricLaplacian w (fun x => f x - v x) := by
  obtain ⟨hfc, Mf, hfLE, hfGE⟩ := hf
  obtain ⟨hvc, Mv, hvLE, hvGE⟩ := hv
  have hsplit : ∀ χ : Y → ℝ, ChartSmooth (n := N) χ →
      ∫ y, (f y - v y) * KahlerLaplacianChart.laplacian w.form.val χ y ∂(IntegrationCurrent.kahlerVolume w) =
        (∫ y, f y * KahlerLaplacianChart.laplacian w.form.val χ y ∂(IntegrationCurrent.kahlerVolume w)) -
          ∫ y, v y * KahlerLaplacianChart.laplacian w.form.val χ y ∂(IntegrationCurrent.kahlerVolume w) := by
    intro χ hχ
    have hL := continuous_laplacian_of_chartSmooth w.isKahler.1 hχ
    refine Eq.trans ?_ (integral_sub (integral_continuous (hfc.mul hL) _)
      (integral_continuous (hvc.mul hL) _))
    exact integral_congr_ae (Eventually.of_forall fun y => by simp only; ring)
  refine ⟨hfc.sub hvc, Mf + Mv, fun χ hχ hχ0 => ?_, fun χ hχ hχ0 => ?_⟩
  · rw [hsplit χ hχ]
    have h1 := hfLE χ hχ hχ0
    have h2 := hvGE χ hχ hχ0
    linarith
  · rw [hsplit χ hχ]
    have h1 := hfGE χ hχ hχ0
    have h2 := hvLE χ hχ hχ0
    linarith

/-- **Second-order flatness for the book's `C^{1,1̄}(X)`.**  If `u ≥ 0` has bounded `ω`-Laplacian
on a compact complex manifold with a Kähler form `ω`, then in every holomorphic chart
`u(x + h) = o(‖h‖²)` at almost every point `x` of the chart target with `u(x) = 0`. -/
theorem HasBoundedMetricLaplacian.ae_isLittleO (w : KahlerBackground N Y) {u : Y → ℝ}
    (hu : HasBoundedMetricLaplacian w u) (hu0 : ∀ x, 0 ≤ u x) (e : ComplexChart N Y) :
    ∀ᵐ z ∂volume, z ∈ e.val.target → u (e.val.symm z) = 0 →
      (fun h => u (e.val.symm (z + h))) =o[𝓝 0] (fun h => ‖h‖ ^ 2) := by
  rcases N with _ | m
  · refine Eventually.of_forall fun z _ hz0 => ?_
    have hconst : (fun h : ComplexModel 0 => u (e.val.symm (z + h))) = fun _ => 0 := by
      funext h
      rw [Subsingleton.elim h 0, add_zero, hz0]
    rw [hconst]
    exact isLittleO_zero _ _
  obtain ⟨M, hM0, hM⟩ := hu.abs_integral_chartLaplacian_le w
  exact ae_isLittleO_of_kahler_pairing e.val.open_target (w.form.val.smooth e)
    (fun z hz => (w.isKahler.1 e z hz).1) (fun z hz => (w.isKahler.1 e z hz).2)
    (fun z hz => w.isKahler.2 e z hz) (ClosedTopCurrents.continuousOn_volDensity w e)
    (fun z hz => ClosedTopCurrents.volDensity_pos w e hz)
    (hu.1.comp_continuousOn e.val.continuousOn_symm) (fun z _ => hu0 _) hM0
    fun φ hφ hφc hφt => hM e φ hφ hφc hφt

/-- **Second-order contact for the book's `C^{1,1̄}(X)`**: if `v ≤ f` both have bounded
`ω`-Laplacian, then in every chart `f` and `v` coincide up to second order at almost every point of
the contact set `{v = f}`. -/
theorem ae_coincideToSecondOrderAt_of_hasBoundedMetricLaplacian (w : KahlerBackground N Y)
    {v f : Y → ℝ} (hv : HasBoundedMetricLaplacian w v) (hf : HasBoundedMetricLaplacian w f)
    (hle : ∀ x, v x ≤ f x) (e : ComplexChart N Y) :
    ∀ᵐ z ∂volume, z ∈ e.val.target → v (e.val.symm z) = f (e.val.symm z) →
      CoincideToSecondOrderAt (fun z => f (e.val.symm z)) (fun z => v (e.val.symm z)) z := by
  have h := (hf.sub w hv).ae_isLittleO w (fun x => sub_nonneg.mpr (hle x)) e
  filter_upwards [h] with z hz hzt hze
  refine ⟨hze.symm, ?_⟩
  exact hz hzt (by simp [hze])

end Manifold

/-! ### `lma:DNTroof`, first assertion, for the book's `C^{1,1̄}(X)` -/

section Roof

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]

open SGPT.Envelopes.DNTReg SGPT.Okounkov.TranscendentalWNReg

/-- **Source `lma:DNTroof`, first assertion** (all dimensions, the book's class).  Let `ω` be a
Kähler form on a compact connected complex manifold `X` and `f₁, f₂ ∈ C^{1,1̄}(X)` (bounded
`ω`-Laplacian).  Then in every holomorphic chart the functions `f₁`, `f₂` and
`P = P_ω(min{f₁, f₂})` (`DNT.roofEnvelope`) pairwise coincide up to second order at almost every
point of the contact set `{P = f₁ = f₂}`. -/
theorem roofEnvelope_coincideToSecondOrder_of_hasBoundedMetricLaplacian (A : KahlerBackground N Y)
    {f₁ f₂ : Y → ℝ} (h₁ : HasBoundedMetricLaplacian A f₁) (h₂ : HasBoundedMetricLaplacian A f₂)
    (e : ComplexChart N Y) :
    ∀ᵐ z ∂volume, z ∈ e.val.target →
      DNT.roofEnvelope A f₁ f₂ (e.val.symm z) = (f₁ (e.val.symm z) : EReal) →
      DNT.roofEnvelope A f₁ f₂ (e.val.symm z) = (f₂ (e.val.symm z) : EReal) →
      CoincideToSecondOrderAt (fun z => f₁ (e.val.symm z))
          (fun z => (DNT.roofEnvelope A f₁ f₂ (e.val.symm z)).toReal) z ∧
        CoincideToSecondOrderAt (fun z => f₂ (e.val.symm z))
          (fun z => (DNT.roofEnvelope A f₁ f₂ (e.val.symm z)).toReal) z ∧
        CoincideToSecondOrderAt (fun z => f₁ (e.val.symm z)) (fun z => f₂ (e.val.symm z)) z := by
  obtain ⟨hreal, hP⟩ := envelope_min_hasBoundedMetricLaplacian_gen A A h₁ h₂
  set P : Y → ℝ := envelopeReal A.form (fun y => min (f₁ y) (f₂ y)) with hPdef
  have hroof : ∀ x, DNT.roofEnvelope A f₁ f₂ x = (P x : EReal) := hreal
  obtain ⟨-, hle₁, hle₂⟩ := DNT.roofEnvelope_genuine A h₁.1 h₂.1
  have hP₁ : ∀ x, P x ≤ f₁ x := fun x => by
    have := hle₁ x; rw [hroof] at this; exact EReal.coe_le_coe_iff.mp this
  have hP₂ : ∀ x, P x ≤ f₂ x := fun x => by
    have := hle₂ x; rw [hroof] at this; exact EReal.coe_le_coe_iff.mp this
  have hfun : (fun z => (DNT.roofEnvelope A f₁ f₂ (e.val.symm z)).toReal) =
      fun z => P (e.val.symm z) := by
    funext z; rw [hroof, EReal.toReal_coe]
  rw [hfun]
  filter_upwards [ae_coincideToSecondOrderAt_of_hasBoundedMetricLaplacian A hP h₁ hP₁ e,
    ae_coincideToSecondOrderAt_of_hasBoundedMetricLaplacian A hP h₂ hP₂ e]
    with z hz₁ hz₂ hzt he₁ he₂
  rw [hroof] at he₁ he₂
  have c₁ := hz₁ hzt (EReal.coe_eq_coe_iff.mp he₁)
  have c₂ := hz₂ hzt (EReal.coe_eq_coe_iff.mp he₂)
  exact ⟨c₁, c₂, c₁.trans c₂.symm⟩

open SGPT.PSH.VariableComplexAtlas in
/-- **Source `lma:DNTroof`, first assertion, with the source envelope**
`P = sourceRelativeEnvelope ω ⊤ (min{f₁, f₂})` of `def:Pthetaf` (all dimensions, the book's
class `C^{1,1̄}(X)` of functions with bounded `ω`-Laplacian). -/
theorem sourceObstacleEnvelope_coincideToSecondOrder_of_hasBoundedMetricLaplacian
    (θ : AtlasClosedRealOneOneForm (ofFixedModel N Y))
    (hK : (atlasClosedFormToNative θ).val.IsKahler) {f₁ f₂ : Y → ℝ}
    (h₁ : HasBoundedMetricLaplacian ⟨atlasClosedFormToNative θ, hK⟩ f₁)
    (h₂ : HasBoundedMetricLaplacian ⟨atlasClosedFormToNative θ, hK⟩ f₂)
    (e : ComplexChart N Y) :
    ∀ᵐ z ∂volume, z ∈ e.val.target →
      sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal))
          (e.val.symm z) = (f₁ (e.val.symm z) : EReal) →
      sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal))
          (e.val.symm z) = (f₂ (e.val.symm z) : EReal) →
      CoincideToSecondOrderAt (fun z => f₁ (e.val.symm z))
          (fun z => (sourceRelativeEnvelope θ (fun _ => ⊤)
            (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal)) (e.val.symm z)).toReal) z ∧
        CoincideToSecondOrderAt (fun z => f₂ (e.val.symm z))
          (fun z => (sourceRelativeEnvelope θ (fun _ => ⊤)
            (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal)) (e.val.symm z)).toReal) z ∧
        CoincideToSecondOrderAt (fun z => f₁ (e.val.symm z)) (fun z => f₂ (e.val.symm z)) z := by
  have hsrc : ∀ x, sourceRelativeEnvelope θ (fun _ => ⊤)
      (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal)) x =
        DNT.roofEnvelope ⟨atlasClosedFormToNative θ, hK⟩ f₁ f₂ x := by
    intro x
    rw [sourceObstacleEnvelope_eq_native]
    rfl
  simp only [hsrc]
  exact roofEnvelope_coincideToSecondOrder_of_hasBoundedMetricLaplacian _ h₁ h₂ e

end Roof

end SGPT.Envelopes.LapClass
