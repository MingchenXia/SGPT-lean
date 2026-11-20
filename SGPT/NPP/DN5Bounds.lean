import SGPT.NPP.DN5Regularity
import SGPT.NPP.DN5Transfer

/-!
# Uniform bounds for the smoothing at radii bounded away from zero

Lane DN5, `thm:DNT23_C11bar` (`chapter_npp.tex`), via FPT `lem:chern-joint-smoothing`
(`chapters/inputs/q10-big-envelope-regularity.tex`).  The `psh` field of
`SGPT.NPP.DN2.IsJointSmoothing` is required at all radii `t < r₀`, `r₀` fixed before `θ` and `u`,
while the local estimates (FPT Steps 2–6) hold below a radius depending on the size of the
domains of local potentials of `θ`.  For radii in a compact interval `[r_L, r₀] ⊂ (0, r₁)` the
smoothing `Ψ_g` (`g` integrable) is smooth, hence all its derivatives are bounded on
`Y × [r_L, r₀]` by compactness (via a finite cover by chart balls), and the clauses follow with
constants depending on `g` (absorbed in `C` and `K`).  This file proves the bounds:

* `exists_uniform_bound_of_local` — local bounds on a cover give a global bound.
* `exists_bound_logRadius` — `Ψ_g(x, eˢ)` and its first two `s`-derivatives are bounded for
  `eˢ ∈ [r_L, r₀]`.
* `exists_bound_theta` — `|θ(v, Jv)| ≤ B ω(v, Jv)` in every chart.
* `exists_bound_leviForm_jointFun` — in every chart, the joint Levi form of
  `(z, w) ↦ Ψ_g(e⁻¹ z, |w|)` is bounded by `B(|v|²_ω + |η|²)` for `|w| ∈ [r_L, r₀]`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace SGPT.NPP.DN5

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending IntegrationCurrent
open SGPT.NPP.DN2

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-! ### Generic compactness tools -/

/-- **Local bounds on an open cover give a uniform bound** on a compact space. -/
theorem exists_uniform_bound_of_local [CompactSpace Y] {P : Y → ℝ → Prop}
    (hmono : ∀ y B B', B ≤ B' → P y B → P y B')
    (hloc : ∀ x : Y, ∃ V : Set Y, IsOpen V ∧ x ∈ V ∧ ∃ B, ∀ y ∈ V, P y B) :
    ∃ B, ∀ y, P y B := by
  classical
  choose V hV hxV B hB using hloc
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover V hV
    (fun x _ => mem_iUnion.mpr ⟨x, hxV x⟩)
  refine ⟨∑ x ∈ s, |B x|, fun y => ?_⟩
  obtain ⟨x, hx⟩ := mem_iUnion.mp (hs (mem_univ y))
  obtain ⟨hxs, hy⟩ := mem_iUnion.mp hx
  refine hmono y (B x) _ ?_ (hB x y hy)
  calc B x ≤ |B x| := le_abs_self _
    _ ≤ ∑ x ∈ s, |B x| := Finset.single_le_sum (f := fun x => |B x|) (fun _ _ => abs_nonneg _) hxs

/-- A smooth function has bounded `k`-th derivative on a compact subset of its open domain. -/
theorem exists_bound_iteratedFDeriv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {S Q : Set E} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S) (hQ : IsCompact Q) (hQS : Q ⊆ S) (k : ℕ) :
    ∃ B, ∀ p ∈ Q, ‖iteratedFDeriv ℝ k f p‖ ≤ B := by
  have hc : ContinuousOn (iteratedFDeriv ℝ k f) Q := fun p hp =>
    ((hf.contDiffAt (hS.mem_nhds (hQS hp))).continuousAt_iteratedFDeriv
      (WithTop.coe_le_coe.mpr le_top)).continuousWithinAt
  obtain ⟨B, hB⟩ := hQ.exists_bound_of_continuousOn hc
  exact ⟨B, hB⟩

theorem abs_realHessian_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ)
    (p h : E) : |realHessian f p h h| ≤ ‖iteratedFDeriv ℝ 2 f p‖ * ‖h‖ ^ 2 := by
  have H := (iteratedFDeriv ℝ 2 f p).le_opNorm ![h, h]
  rw [Fin.prod_univ_two] at H
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at H
  rw [realHessian, ← Real.norm_eq_abs, sq]
  calc _ ≤ _ := H
    _ = _ := by ring

theorem abs_leviForm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : E → ℝ)
    (p h : E) : |leviForm f p h| ≤ ‖iteratedFDeriv ℝ 2 f p‖ * ‖h‖ ^ 2 := by
  have h1 := abs_realHessian_le f p h
  have h2 := abs_realHessian_le f p (Complex.I • h)
  rw [norm_smul, Complex.norm_I, one_mul] at h2
  have hn : 0 ≤ ‖iteratedFDeriv ℝ 2 f p‖ * ‖h‖ ^ 2 := by positivity
  rw [leviForm, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  calc |realHessian f p h h + realHessian f p (Complex.I • h) (Complex.I • h)| / 4
      ≤ (|realHessian f p h h| + |realHessian f p (Complex.I • h) (Complex.I • h)|) / 4 := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

theorem norm_prod_sq_le {E : Type*} [NormedAddCommGroup E] (v : E) (η : ℂ) :
    ‖(v, η)‖ ^ 2 ≤ ‖v‖ ^ 2 + ‖η‖ ^ 2 := by
  rw [Prod.norm_mk]
  rcases le_total ‖v‖ ‖η‖ with h | h
  · rw [max_eq_right h]; nlinarith [norm_nonneg v]
  · rw [max_eq_left h]; nlinarith [norm_nonneg η]

/-! ### Chart balls -/

theorem exists_closedBall_subset_target (e : ComplexChart N Y) {z : ComplexModel N}
    (hz : z ∈ e.val.target) : ∃ b > 0, closedBall z b ⊆ e.val.target := by
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp e.val.open_target z hz
  exact ⟨r / 2, by linarith, (closedBall_subset_ball (by linarith)).trans hrsub⟩

theorem chartNormSq_nonneg (wY : KahlerBackground N Y) (e : ComplexChart N Y)
    {z : ComplexModel N} (hz : z ∈ e.val.target) (v : ComplexModel N) :
    0 ≤ chartNormSq wY e z v :=
  wY.isSemipositive e z hz v

/-- `m ‖v‖² ≤ |v|²_ω` on a compact part of a chart. -/
theorem exists_pos_le_chartNormSq (wY : KahlerBackground N Y) (e : ComplexChart N Y)
    {Q : Set (ComplexModel N)} (hQ : IsCompact Q) (hQt : Q ⊆ e.val.target) :
    ∃ m > 0, ∀ z ∈ Q, ∀ v, m * ‖v‖ ^ 2 ≤ chartNormSq wY e z v := by
  obtain ⟨m, hm, h⟩ := SGPT.Analysis.KahlerNormal.exists_pos_le_apply_I_smul
    (wY.form.val.smooth e).continuousOn (fun z hz => (wY.isKahler.1 e z hz).2) hQ hQt
  exact ⟨m, hm, h⟩

/-- **`|θ(v, Jv)| ≤ B ω(v, Jv)` in every chart.** -/
theorem exists_bound_theta [CompactSpace Y] (wY : KahlerBackground N Y)
    (θ : SmoothRealForm N Y 2) :
    ∃ B, ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target → ∀ v,
      |θ.coeff e z ![v, Complex.I • v]| ≤ B * chartNormSq wY e z v := by
  suffices key : ∃ B, ∀ y : Y, ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      e.val.symm z = y → ∀ v, |θ.coeff e z ![v, Complex.I • v]| ≤ B * chartNormSq wY e z v by
    obtain ⟨B, hB⟩ := key
    exact ⟨B, fun e z hz v => hB (e.val.symm z) e z hz rfl v⟩
  refine exists_uniform_bound_of_local
    (fun y B B' hBB' h e z hz hzy v => (h e z hz hzy v).trans
      (mul_le_mul_of_nonneg_right hBB' (chartNormSq_nonneg wY e hz v))) fun x => ?_
  set e₀ := complexChartAt (n := N) x
  have hx : x ∈ e₀.val.source := mem_complexChartAt_source x
  obtain ⟨b, hb, hbt⟩ := exists_closedBall_subset_target e₀ (e₀.val.map_source hx)
  obtain ⟨m, hm, hmQ⟩ := exists_pos_le_chartNormSq wY e₀ (isCompact_closedBall _ b) hbt
  have hc : ContinuousOn (θ.coeff e₀) (closedBall (e₀.val x) b) := (θ.smooth e₀).continuousOn.mono hbt
  obtain ⟨Bθ, hBθ⟩ := (isCompact_closedBall (e₀.val x) b).exists_bound_of_continuousOn hc
  refine ⟨e₀.val.source ∩ e₀.val ⁻¹' ball (e₀.val x) b,
    e₀.val.isOpen_inter_preimage isOpen_ball, ⟨hx, mem_ball_self hb⟩, Bθ / m, ?_⟩
  rintro y ⟨hy, hyb⟩ e z hz rfl v
  have hzs : z ∈ (chartTransition e e₀).source := mem_transition_source_iff.mpr ⟨hz, hy⟩
  have hτ : chartTransition e e₀ z ∈ closedBall (e₀.val x) b := ball_subset_closedBall hyb
  rw [coeff_apply_I_transition θ hzs v, chartNormSq_transition wY hzs v]
  set a := chartTransitionDerivative e e₀ z v
  have h1 : |θ.coeff e₀ (chartTransition e e₀ z) ![a, Complex.I • a]| ≤ Bθ * ‖a‖ ^ 2 := by
    have H := (θ.coeff e₀ (chartTransition e e₀ z)).le_opNorm ![a, Complex.I • a]
    rw [Fin.prod_univ_two] at H
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, norm_smul,
      Complex.norm_I, one_mul] at H
    rw [← Real.norm_eq_abs]
    calc _ ≤ _ := H
      _ ≤ Bθ * (‖a‖ * ‖a‖) := mul_le_mul_of_nonneg_right (hBθ _ hτ) (by positivity)
      _ = Bθ * ‖a‖ ^ 2 := by ring
  have h2 := hmQ _ hτ a
  have hBθ0 : 0 ≤ Bθ := (norm_nonneg _).trans (hBθ _ hτ)
  calc _ ≤ Bθ * ‖a‖ ^ 2 := h1
    _ = Bθ / m * (m * ‖a‖ ^ 2) := by field_simp
    _ ≤ Bθ / m * chartNormSq wY e₀ (chartTransition e e₀ z) a :=
      mul_le_mul_of_nonneg_left h2 (div_nonneg hBθ0 hm.le)

/-! ### Bounds for the smoothing -/

variable [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

section Smoothing

variable {wY : KahlerBackground N Y} {A : FibreAtlas N Y} {r₁ : ℝ} {g : Y → ℝ}

/-- The smoothing in log radius, in a chart: `G(z, s) = Ψ_g(e⁻¹ z, eˢ)` is smooth for
`s < log r₁`. -/
theorem contDiffOn_logRadius (hr : IsUniformRadius wY A r₁) (hg : Integrable g (kahlerVolume wY))
    (e : ComplexChart N Y) :
    ContDiffOn ℝ ∞ (fun q : ComplexModel N × ℝ => smoothing wY A g (e.val.symm q.1) (Real.exp q.2))
      (e.val.target ×ˢ Iio (Real.log r₁)) := by
  have h := smoothing_contDiffOn hr hg e
  refine h.comp (contDiffOn_fst.prodMk (Real.contDiff_exp.comp_contDiffOn contDiffOn_snd)) ?_
  intro q hq
  refine ⟨hq.1, Real.exp_pos _, ?_⟩
  have := hq.2
  rw [mem_Iio] at this
  calc Real.exp q.2 < Real.exp (Real.log r₁) := Real.exp_lt_exp.mpr this
    _ = r₁ := Real.exp_log hr.1

/-- The joint function `(z, w) ↦ Ψ_g(e⁻¹ z, |w|)` is smooth for `0 < |w| < r₁`. -/
theorem contDiffOn_jointFun (hr : IsUniformRadius wY A r₁) (hg : Integrable g (kahlerVolume wY))
    (e : ComplexChart N Y) :
    ContDiffOn ℝ ∞ (jointFun (smoothing wY A g) e)
      (e.val.target ×ˢ {w : ℂ | w ≠ 0 ∧ ‖w‖ < r₁}) := by
  have h := smoothing_contDiffOn hr hg e
  have hn : ContDiffOn ℝ ∞ (fun q : ComplexModel N × ℂ => ‖q.2‖)
      (e.val.target ×ˢ {w : ℂ | w ≠ 0 ∧ ‖w‖ < r₁}) := fun q hq =>
    ((contDiffAt_norm ℝ hq.2.1).comp q contDiffAt_snd).contDiffWithinAt
  exact h.comp (contDiffOn_fst.prodMk hn) fun q hq => ⟨hq.1, norm_pos_iff.mpr hq.2.1, hq.2.2⟩

theorem isOpen_annulusDomain (e : ComplexChart N Y) (r₁ : ℝ) :
    IsOpen (e.val.target ×ˢ {w : ℂ | w ≠ 0 ∧ ‖w‖ < r₁}) :=
  e.val.open_target.prod ((isOpen_ne).inter (isOpen_lt continuous_norm continuous_const))

/-- The slice derivatives of a smooth function of `(z, s)`. -/
theorem deriv_slice_eq {G : ComplexModel N × ℝ → ℝ} {S : Set (ComplexModel N × ℝ)} (hS : IsOpen S)
    (hG : ContDiffOn ℝ ∞ G S) {z : ComplexModel N} {s : ℝ} (hs : (z, s) ∈ S) :
    deriv (fun s' => G (z, s')) s = fderiv ℝ G (z, s) (0, 1) ∧
      deriv (deriv (fun s' => G (z, s'))) s = fderiv ℝ (fderiv ℝ G) (z, s) (0, 1) (0, 1) := by
  have hsl : ∀ s', (z, s') ∈ S → HasDerivAt (fun s'' => G (z, s'')) (fderiv ℝ G (z, s') (0, 1)) s' := by
    intro s' hs'
    have hd : DifferentiableAt ℝ G (z, s') :=
      (hG.contDiffAt (hS.mem_nhds hs')).differentiableAt (by simp)
    have h2 : HasDerivAt (fun s'' : ℝ => (z, s'')) ((0 : ComplexModel N), (1 : ℝ)) s' :=
      (hasDerivAt_const s' z).prodMk (hasDerivAt_id s')
    exact hd.hasFDerivAt.comp_hasDerivAt s' h2
  have hev : ∀ᶠ s' in 𝓝 s, (z, s') ∈ S :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hS.mem_nhds hs)
  have hderiv : deriv (fun s' => G (z, s')) =ᶠ[𝓝 s] fun s' => fderiv ℝ G (z, s') (0, 1) := by
    filter_upwards [hev] with s' hs'
    exact (hsl s' hs').deriv
  refine ⟨(hsl s hs).deriv, ?_⟩
  rw [hderiv.deriv_eq]
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ G) S := hG.fderiv_of_isOpen hS (by simp)
  have hDd : DifferentiableAt ℝ (fderiv ℝ G) (z, s) :=
    (hD.contDiffAt (hS.mem_nhds hs)).differentiableAt (by simp)
  have h2 : HasDerivAt (fun s'' : ℝ => (z, s'')) ((0 : ComplexModel N), (1 : ℝ)) s :=
    (hasDerivAt_const s z).prodMk (hasDerivAt_id s)
  have h3 := (hDd.hasFDerivAt.comp_hasDerivAt s h2).clm_apply (hasDerivAt_const s ((0 : ComplexModel N), (1 : ℝ)))
  have h4 : HasDerivAt (fun s' => fderiv ℝ G (z, s') (0, 1))
      (fderiv ℝ (fderiv ℝ G) (z, s) (0, 1) (0, 1)) s := by
    have := h3
    rw [map_zero, add_zero] at this
    exact this
  exact h4.deriv

/-- **Bounds in log radius**: `Ψ_g(x, eˢ)` and its first two `s`-derivatives are bounded,
uniformly in `x`, for `eˢ ∈ [r_L, r₀]`, `0 < r_L ≤ r₀ < r₁`. -/
theorem exists_bound_logRadius (hr : IsUniformRadius wY A r₁) (hg : Integrable g (kahlerVolume wY))
    {rL r₀ : ℝ} (hrL : 0 < rL) (hLr : rL ≤ r₀) (hr₀ : r₀ < r₁) :
    ∃ B, ∀ (x : Y) (s : ℝ), rL ≤ Real.exp s → Real.exp s ≤ r₀ →
      |smoothing wY A g x (Real.exp s)| ≤ B ∧
      |deriv (fun s => smoothing wY A g x (Real.exp s)) s| ≤ B ∧
      |deriv (deriv (fun s => smoothing wY A g x (Real.exp s))) s| ≤ B := by
  have hr₀pos : 0 < r₀ := hrL.trans_le hLr
  refine exists_uniform_bound_of_local
    (fun y B B' hBB' h s h1 h2 => ⟨(h s h1 h2).1.trans hBB', (h s h1 h2).2.1.trans hBB',
      (h s h1 h2).2.2.trans hBB'⟩) fun x => ?_
  set e₀ := complexChartAt (n := N) x
  have hx : x ∈ e₀.val.source := mem_complexChartAt_source x
  obtain ⟨b, hb, hbt⟩ := exists_closedBall_subset_target e₀ (e₀.val.map_source hx)
  set G := fun q : ComplexModel N × ℝ => smoothing wY A g (e₀.val.symm q.1) (Real.exp q.2)
  set S := e₀.val.target ×ˢ Iio (Real.log r₁)
  have hS : IsOpen S := e₀.val.open_target.prod isOpen_Iio
  have hG : ContDiffOn ℝ ∞ G S := contDiffOn_logRadius hr hg e₀
  set Q := closedBall (e₀.val x) b ×ˢ Icc (Real.log rL) (Real.log r₀)
  have hQ : IsCompact Q := (isCompact_closedBall _ _).prod isCompact_Icc
  have hlog : Real.log r₀ < Real.log r₁ := Real.log_lt_log hr₀pos hr₀
  have hQS : Q ⊆ S := fun q hq => ⟨hbt hq.1, lt_of_le_of_lt hq.2.2 hlog⟩
  have hD1 : ContDiffOn ℝ ∞ (fderiv ℝ G) S := hG.fderiv_of_isOpen hS (by simp)
  have hD2 : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ G)) S := hD1.fderiv_of_isOpen hS (by simp)
  obtain ⟨B0, hB0⟩ := hQ.exists_bound_of_continuousOn (hG.continuousOn.mono hQS)
  obtain ⟨B1, hB1⟩ := hQ.exists_bound_of_continuousOn (hD1.continuousOn.mono hQS)
  obtain ⟨B2, hB2⟩ := exists_bound_iteratedFDeriv hS hG hQ hQS 2
  refine ⟨e₀.val.source ∩ e₀.val ⁻¹' ball (e₀.val x) b,
    e₀.val.isOpen_inter_preimage isOpen_ball, ⟨hx, mem_ball_self hb⟩, max B0 (max B1 B2), ?_⟩
  rintro y ⟨hy, hyb⟩ s hs1 hs2
  have hq : (e₀.val y, s) ∈ Q :=
    ⟨ball_subset_closedBall hyb, (Real.log_le_iff_le_exp hrL).mpr hs1,
      (Real.le_log_iff_exp_le hr₀pos).mpr hs2⟩
  have hfun : (fun s => smoothing wY A g y (Real.exp s)) = fun s' => G (e₀.val y, s') := by
    funext s'
    simp only [G, e₀.val.left_inv hy]
  have hnorm : ‖((0 : ComplexModel N), (1 : ℝ))‖ = 1 := by simp [Prod.norm_mk]
  obtain ⟨hd1, hd2⟩ := deriv_slice_eq hS hG (hQS hq)
  refine ⟨?_, ?_, ?_⟩
  · have h := hB0 _ hq
    rw [Real.norm_eq_abs] at h
    have : smoothing wY A g y (Real.exp s) = G (e₀.val y, s) := by
      simp only [G, e₀.val.left_inv hy]
    rw [this]
    exact h.trans (le_max_left _ _)
  · rw [hfun, hd1]
    calc |fderiv ℝ G (e₀.val y, s) (0, 1)| ≤ ‖fderiv ℝ G (e₀.val y, s)‖ * ‖((0 : ComplexModel N), (1 : ℝ))‖ := by
          rw [← Real.norm_eq_abs]; exact (fderiv ℝ G _).le_opNorm _
      _ ≤ B1 := by rw [hnorm, mul_one]; exact hB1 _ hq
      _ ≤ _ := (le_max_left _ _).trans (le_max_right _ _)
  · rw [hfun, hd2]
    rw [← realHessian_eq_fderiv]
    calc |realHessian G (e₀.val y, s) (0, 1) (0, 1)|
        ≤ ‖iteratedFDeriv ℝ 2 G (e₀.val y, s)‖ * ‖((0 : ComplexModel N), (1 : ℝ))‖ ^ 2 :=
          abs_realHessian_le G _ _
      _ ≤ B2 := by rw [hnorm, one_pow, mul_one]; exact hB2 _ hq
      _ ≤ _ := (le_max_right _ _).trans (le_max_right _ _)

theorem contDiffAt_jointFun (hr : IsUniformRadius wY A r₁) (hg : Integrable g (kahlerVolume wY))
    {e : ComplexChart N Y} {z : ComplexModel N} (hz : z ∈ e.val.target) {w : ℂ} (hw : 0 < ‖w‖)
    (hw₁ : ‖w‖ < r₁) : ContDiffAt ℝ ∞ (jointFun (smoothing wY A g) e) (z, w) :=
  (contDiffOn_jointFun hr hg e).contDiffAt
    ((isOpen_annulusDomain e r₁).mem_nhds ⟨hz, norm_pos_iff.mp hw, hw₁⟩)

/-- **Intrinsic bound of the joint Levi form** of `(z, w) ↦ Ψ_g(e⁻¹ z, |w|)` for
`|w| ∈ [r_L, r₀]`, in every chart. -/
theorem exists_bound_leviForm_jointFun (hr : IsUniformRadius wY A r₁)
    (hg : Integrable g (kahlerVolume wY)) {rL r₀ : ℝ} (hrL : 0 < rL) (hr₀ : r₀ < r₁) :
    ∃ B, ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target → ∀ w : ℂ,
      rL ≤ ‖w‖ → ‖w‖ ≤ r₀ → ∀ (v : ComplexModel N) (η : ℂ),
        |leviForm (jointFun (smoothing wY A g) e) (z, w) (v, η)| ≤
          B * (chartNormSq wY e z v + ‖η‖ ^ 2) := by
  suffices key : ∃ B, ∀ y : Y, ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      e.val.symm z = y → ∀ w : ℂ, rL ≤ ‖w‖ → ‖w‖ ≤ r₀ → ∀ (v : ComplexModel N) (η : ℂ),
        |leviForm (jointFun (smoothing wY A g) e) (z, w) (v, η)| ≤
          B * (chartNormSq wY e z v + ‖η‖ ^ 2) by
    obtain ⟨B, hB⟩ := key
    exact ⟨B, fun e z hz w h1 h2 v η => hB (e.val.symm z) e z hz rfl w h1 h2 v η⟩
  refine exists_uniform_bound_of_local
    (fun y B B' hBB' h e z hz hzy w h1 h2 v η => (h e z hz hzy w h1 h2 v η).trans
      (mul_le_mul_of_nonneg_right hBB'
        (add_nonneg (chartNormSq_nonneg wY e hz v) (sq_nonneg _)))) fun x => ?_
  set e₀ := complexChartAt (n := N) x
  have hx : x ∈ e₀.val.source := mem_complexChartAt_source x
  obtain ⟨b, hb, hbt⟩ := exists_closedBall_subset_target e₀ (e₀.val.map_source hx)
  set S := e₀.val.target ×ˢ {w : ℂ | w ≠ 0 ∧ ‖w‖ < r₁}
  set Q := closedBall (e₀.val x) b ×ˢ (closedBall (0 : ℂ) r₀ ∩ {w : ℂ | rL ≤ ‖w‖})
  have hQ : IsCompact Q := (isCompact_closedBall _ _).prod
    ((isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm))
  have hQS : Q ⊆ S := by
    intro q hq
    refine ⟨hbt hq.1, ?_, ?_⟩
    · intro h0
      have h3 : rL ≤ ‖q.2‖ := hq.2.2
      rw [h0, norm_zero] at h3
      linarith
    · have := hq.2.1
      rw [mem_closedBall, dist_zero_right] at this
      exact this.trans_lt hr₀
  obtain ⟨BH, hBH⟩ := exists_bound_iteratedFDeriv (isOpen_annulusDomain e₀ r₁)
    (contDiffOn_jointFun hr hg e₀) hQ hQS 2
  obtain ⟨m, hm, hmQ⟩ := exists_pos_le_chartNormSq wY e₀ (isCompact_closedBall _ b) hbt
  refine ⟨e₀.val.source ∩ e₀.val ⁻¹' ball (e₀.val x) b,
    e₀.val.isOpen_inter_preimage isOpen_ball, ⟨hx, mem_ball_self hb⟩,
    max BH 0 * (m⁻¹ + 1), ?_⟩
  rintro y ⟨hy, hyb⟩ e z hz rfl w hw1 hw2 v η
  have hzs : z ∈ (chartTransition e e₀).source := mem_transition_source_iff.mpr ⟨hz, hy⟩
  have hτb : chartTransition e e₀ z ∈ closedBall (e₀.val x) b := ball_subset_closedBall hyb
  have hw0 : 0 < ‖w‖ := hrL.trans_le hw1
  have hJ : ContDiffAt ℝ 2 (jointFun (smoothing wY A g) e₀) (chartTransition e e₀ z, w) :=
    (contDiffAt_jointFun hr hg (hbt hτb) hw0 (hw2.trans_lt hr₀)).of_le (by norm_cast)
  obtain ⟨-, hlevi⟩ := leviForm_jointFun_transition (smoothing wY A g) hzs hJ v η
  rw [hlevi, chartNormSq_transition wY hzs v]
  set a := chartTransitionDerivative e e₀ z v
  have hqQ : (chartTransition e e₀ z, w) ∈ Q :=
    ⟨hτb, by rw [mem_closedBall, dist_zero_right]; exact hw2, hw1⟩
  have h1 := abs_leviForm_le (jointFun (smoothing wY A g) e₀) (chartTransition e e₀ z, w) (a, η)
  have h2 := norm_prod_sq_le a η
  have h3 := hmQ _ hτb a
  have hBH' : ‖iteratedFDeriv ℝ 2 (jointFun (smoothing wY A g) e₀) (chartTransition e e₀ z, w)‖
      ≤ max BH 0 := (hBH _ hqQ).trans (le_max_left _ _)
  have hN := chartNormSq_nonneg wY e₀ (hbt hτb) a
  have ha2 : ‖a‖ ^ 2 ≤ m⁻¹ * chartNormSq wY e₀ (chartTransition e e₀ z) a := by
    rw [inv_mul_eq_div, le_div_iff₀ hm]
    linarith
  have hM : 0 ≤ max BH 0 := le_max_right _ _
  calc _ ≤ ‖iteratedFDeriv ℝ 2 (jointFun (smoothing wY A g) e₀) (chartTransition e e₀ z, w)‖ *
        ‖(a, η)‖ ^ 2 := h1
    _ ≤ max BH 0 * (‖a‖ ^ 2 + ‖η‖ ^ 2) := mul_le_mul hBH' h2 (sq_nonneg _) hM
    _ ≤ max BH 0 * (m⁻¹ * chartNormSq wY e₀ (chartTransition e e₀ z) a + ‖η‖ ^ 2) := by gcongr
    _ ≤ max BH 0 * (m⁻¹ + 1) * (chartNormSq wY e₀ (chartTransition e e₀ z) a + ‖η‖ ^ 2) := by
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ hM
        have hm' : 0 ≤ m⁻¹ := inv_nonneg.mpr hm.le
        nlinarith [sq_nonneg ‖η‖]

end Smoothing

end SGPT.NPP.DN5
