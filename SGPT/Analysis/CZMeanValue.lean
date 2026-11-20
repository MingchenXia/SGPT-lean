import SGPT.Okounkov.TranscendentalWNRegC11bar
import SGPT.Foundations.Analysis.Pending.RadialLeviPreimage

/-!
# Mean-value inequalities for functions with a one-sided bounded Laplacian

Lane C11-REAL (`claude-c11-real`, nodes `c11r:levi-trace-calculus` and `c11r:mean-value`).  This
is the potential-theoretic input that replaces Calderón–Zygmund theory (`W^{2,p}` estimates,
a.e. second-order differentiability and Stampacchia's lemma) in the second-order contact argument
of the book's `lma:DNTroof` (`references/sgpt-d3f272c3/source/author/chapter_npp.tex`).

On `ℂⁿ = ComplexModel n` the **coordinate Levi trace** `∑_j ∂_j∂̄_j φ` (TN's
`coordinateLeviTrace`, `∂_j∂̄_j φ = leviForm φ · e_j`) is a quarter of the flat Laplacian of
`ℝ²ⁿ`.  A function `w`, continuous on an open set `U`, has distributional Levi trace `≥ -M`
(`LeviTraceGE`) if `∫ w ∑_j ∂_j∂̄_j φ ≥ -M ∫ φ` for every nonnegative test function `φ` supported
in `U`; similarly `LeviTraceLE`.  `HasLocallyBoundedLeviTraceOn` is the two-sided local version
(a locally bounded distributional Laplacian).

* `coordinateLeviTrace_comp_sub`, `coordinateLeviTrace_norm_sub_sq` — translation invariance and
  `∑_j ∂_j∂̄_j ‖z - y‖² = n`.
* `le_kernelAverage_add` — **sub-mean value inequality with quadratic error**: if `w` has Levi
  trace `≥ -M` (`M ≥ 0`) on `U ⊇ B̄(y, R)`, then `w(y) ≤ ∫ w(z) κ_R(z - y) dz + (M/n) R²`, where
  `κ_R` is TN's explicit smooth radial probability kernel supported in `B̄(0, R)`.
* `kernelAverage_sub_le` — the super-mean value inequality for Levi trace `≤ M`.
* `kernelAverage_le_setIntegral_div`, `setIntegral_div_le_kernelAverage` — comparison of kernel
  averages of a nonnegative function with its integrals over the balls `B̄(y, R)`, `B̄(y, R/2)`.

## Proof of the mean-value inequality

TN's radial Poisson potential `Φ = Φ_{0,b}` (`explicitRadialPoissonPotential R hR 0 b`) is smooth,
nonnegative, supported in `B̄(0, R)`, and `4 ∑_j ∂_j∂̄_j Φ = κ_R - κ_{R/(b+1)}`.  Testing the
hypothesis against `Φ(· - y)` and integrating `‖z - y‖²` by parts against it
(`∫ Φ = (1/4n) ∫ ‖z‖² (κ_R - κ_{R/(b+1)}) ≤ R²/(4n)`) gives
`∫ w κ_{R/(b+1)}(· - y) ≤ ∫ w κ_R(· - y) + (M/n) R²`; as `b → ∞` the left side tends to `w(y)`
by continuity.  This is the classical argument "mollifications of a subharmonic function increase
with the radius", with the explicit error term needed for a one-sided bound `Δw ≥ -4M`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace SGPT.Analysis.CZ

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HolomorphicPullback
open SGPT.Foundations.Analysis.Pending.RadialLeviPreimage
open SGPT.Okounkov.TranscendentalWNReg

variable {n : ℕ}

/-! ### Distributional bounds for the Levi trace -/

/-- `w` has distributional coordinate Levi trace `∑_j ∂_j∂̄_j w = Δw/4` at least `-M` on `U`. -/
def LeviTraceGE (w : ComplexModel n → ℝ) (U : Set (ComplexModel n)) (M : ℝ) : Prop :=
  ∀ φ : ComplexModel n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    (∀ z, 0 ≤ φ z) → -(M * ∫ z, φ z) ≤ ∫ z, w z * coordinateLeviTrace φ z

/-- `w` has distributional coordinate Levi trace `∑_j ∂_j∂̄_j w = Δw/4` at most `M` on `U`. -/
def LeviTraceLE (w : ComplexModel n → ℝ) (U : Set (ComplexModel n)) (M : ℝ) : Prop :=
  ∀ φ : ComplexModel n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    (∀ z, 0 ≤ φ z) → ∫ z, w z * coordinateLeviTrace φ z ≤ M * ∫ z, φ z

/-- **Locally bounded distributional Laplacian** on `U`: for every compact `K ⊆ U` there is `M`
with `|∫ w ∑_j ∂_j∂̄_j φ| ≤ M ∫ |φ|` for every smooth `φ` supported in `K`. -/
def HasLocallyBoundedLeviTraceOn (w : ComplexModel n → ℝ) (U : Set (ComplexModel n)) : Prop :=
  ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ U → ∃ M : ℝ,
    ∀ φ : ComplexModel n → ℝ, ContDiff ℝ ∞ φ → tsupport φ ⊆ K →
      |∫ z, w z * coordinateLeviTrace φ z| ≤ M * ∫ z, |φ z|

theorem LeviTraceGE.mono {w : ComplexModel n → ℝ} {U V : Set (ComplexModel n)} {M : ℝ}
    (h : LeviTraceGE w U M) (hVU : V ⊆ U) : LeviTraceGE w V M :=
  fun φ hφ hφc hφV hφ0 => h φ hφ hφc (hφV.trans hVU) hφ0

theorem LeviTraceLE.mono {w : ComplexModel n → ℝ} {U V : Set (ComplexModel n)} {M : ℝ}
    (h : LeviTraceLE w U M) (hVU : V ⊆ U) : LeviTraceLE w V M :=
  fun φ hφ hφc hφV hφ0 => h φ hφ hφc (hφV.trans hVU) hφ0

/-- A Levi trace bounded above by `M` is a Levi trace of `-w` bounded below by `-M`. -/
theorem LeviTraceLE.neg {w : ComplexModel n → ℝ} {U : Set (ComplexModel n)} {M : ℝ}
    (h : LeviTraceLE w U M) : LeviTraceGE (fun z => -w z) U M := by
  intro φ hφ hφc hφU hφ0
  have h1 := h φ hφ hφc hφU hφ0
  have h2 : ∫ z, -w z * coordinateLeviTrace φ z = -∫ z, w z * coordinateLeviTrace φ z := by
    rw [← integral_neg]
    congr 1
    funext z
    ring
  rw [h2]
  linarith

/-- On a compact set inside `U`, a locally bounded Levi trace gives two-sided bounds on the open
interior pieces. -/
theorem HasLocallyBoundedLeviTraceOn.exists_ge_le {w : ComplexModel n → ℝ}
    {U : Set (ComplexModel n)} (h : HasLocallyBoundedLeviTraceOn w U) {K V : Set (ComplexModel n)}
    (hK : IsCompact K) (hKU : K ⊆ U) (hVK : V ⊆ K) :
    ∃ M : ℝ, 0 ≤ M ∧ LeviTraceGE w V M ∧ LeviTraceLE w V M := by
  obtain ⟨M, hM⟩ := h K hK hKU
  refine ⟨max M 0, le_max_right _ _, fun φ hφ _ hφV hφ0 => ?_, fun φ hφ _ hφV hφ0 => ?_⟩
  · have h1 := hM φ hφ (hφV.trans hVK)
    have habs : ∫ z, |φ z| = ∫ z, φ z := by
      congr 1
      funext z
      exact abs_of_nonneg (hφ0 z)
    have hint : 0 ≤ ∫ z, φ z := integral_nonneg hφ0
    rw [habs] at h1
    have h2 : M * ∫ z, φ z ≤ max M 0 * ∫ z, φ z :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hint
    have h3 := (abs_le.mp (h1.trans h2)).1
    linarith
  · have h1 := hM φ hφ (hφV.trans hVK)
    have habs : ∫ z, |φ z| = ∫ z, φ z := by
      congr 1
      funext z
      exact abs_of_nonneg (hφ0 z)
    have hint : 0 ≤ ∫ z, φ z := integral_nonneg hφ0
    rw [habs] at h1
    have h2 : M * ∫ z, φ z ≤ max M 0 * ∫ z, φ z :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hint
    exact (abs_le.mp (h1.trans h2)).2

/-! ### Calculus of the coordinate Levi trace -/

/-- Translation invariance of the real Hessian. -/
theorem realHessian_comp_sub {u : ComplexModel n → ℝ} (hu : ContDiff ℝ 2 u)
    (y z a b : ComplexModel n) :
    realHessian (fun x => u (x - y)) z a b = realHessian u (z - y) a b := by
  have h := realHessian_comp_affine hu (ContinuousLinearMap.id ℝ (ComplexModel n)) (-y) z a b
  simpa [sub_eq_neg_add] using h

/-- Translation invariance of the Levi form. -/
theorem leviForm_comp_sub {u : ComplexModel n → ℝ} (hu : ContDiff ℝ 2 u)
    (y z v : ComplexModel n) :
    leviForm (fun x => u (x - y)) z v = leviForm u (z - y) v := by
  simp only [leviForm, realHessian_comp_sub hu]

/-- Translation invariance of the coordinate Levi trace. -/
theorem coordinateLeviTrace_comp_sub {u : ComplexModel n → ℝ} (hu : ContDiff ℝ 2 u)
    (y z : ComplexModel n) :
    coordinateLeviTrace (fun x => u (x - y)) z = coordinateLeviTrace u (z - y) := by
  simp only [coordinateLeviTrace, leviForm_comp_sub hu]

/-- The Levi form of `‖· - y‖²` is `‖v‖²`. -/
theorem leviForm_norm_sub_sq (y z v : ComplexModel n) :
    leviForm (fun x => ‖x - y‖ ^ 2) z v = ‖v‖ ^ 2 := by
  have hq : ContDiff ℝ 2 (fun x : ComplexModel n => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  rw [leviForm_comp_sub hq, leviForm, realHessian_norm_sq, realHessian_norm_sq,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_smul, Complex.norm_I, one_mul]
  ring

/-- `∑_j ∂_j∂̄_j ‖z - y‖² = n`. -/
theorem coordinateLeviTrace_norm_sub_sq (y z : ComplexModel n) :
    coordinateLeviTrace (fun x => ‖x - y‖ ^ 2) z = n := by
  simp only [coordinateLeviTrace, leviForm_norm_sub_sq, norm_coordinateVector, one_pow,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- The coordinate Levi trace of a `C²` function is continuous. -/
theorem continuous_coordinateLeviTrace {φ : ComplexModel n → ℝ} (hφ : ContDiff ℝ 2 φ) :
    Continuous (coordinateLeviTrace φ) := by
  unfold coordinateLeviTrace leviForm
  refine continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_realHessian hφ _ _).add (continuous_realHessian hφ _ _)).div_const _

/-- The coordinate Levi trace of a compactly supported `C²` function has compact support. -/
theorem tsupport_coordinateLeviTrace_subset {φ : ComplexModel n → ℝ} :
    tsupport (coordinateLeviTrace φ) ⊆ tsupport φ := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport φ)
  by_contra hxs
  apply hx
  have h0 : iteratedFDeriv ℝ 2 φ x = 0 := by
    by_contra hne
    exact hxs (support_iteratedFDeriv_subset (𝕜 := ℝ) (n := 2) (f := φ) hne)
  simp [coordinateLeviTrace, leviForm, realHessian, h0]

/-- **Integration by parts against `‖· - y‖²`**: `∫ ‖z - y‖² ∑_j ∂_j∂̄_j φ = n ∫ φ`. -/
theorem integral_norm_sub_sq_mul_coordinateLeviTrace {φ : ComplexModel n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (y : ComplexModel n) :
    ∫ z, ‖z - y‖ ^ 2 * coordinateLeviTrace φ z = n * ∫ z, φ z := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hq : ContDiffOn ℝ ∞ (fun x : ComplexModel n => ‖x - y‖ ^ 2) univ :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).contDiffOn
  have hint : ∀ j : Fin n, Integrable (fun z => ‖z - y‖ ^ 2 * leviForm φ z (coordinateVector j)) := by
    intro j
    have hc : Continuous (fun z => leviForm φ z (coordinateVector j)) :=
      ((continuous_realHessian hφ2 _ _).add (continuous_realHessian hφ2 _ _)).div_const _
    have hcs : HasCompactSupport (fun z => leviForm φ z (coordinateVector j)) := by
      refine hφc.mono' fun x hx => ?_
      by_contra hxs
      apply hx
      have h0 : iteratedFDeriv ℝ 2 φ x = 0 := by
        by_contra hne
        exact hxs (support_iteratedFDeriv_subset (𝕜 := ℝ) (n := 2) (f := φ) hne)
      simp [leviForm, realHessian, h0]
    exact integrable_mul_of_continuousOn isOpen_univ hq.continuousOn hc hcs (subset_univ _)
  calc ∫ z, ‖z - y‖ ^ 2 * coordinateLeviTrace φ z
      = ∑ j : Fin n, ∫ z, ‖z - y‖ ^ 2 * leviForm φ z (coordinateVector j) := by
        rw [← integral_finsetSum _ fun j _ => hint j]
        congr 1
        funext z
        rw [coordinateLeviTrace, Finset.mul_sum]
    _ = ∑ j : Fin n, ∫ z, φ z := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_mul_leviForm_eq isOpen_univ hq hφ hφc (subset_univ _)]
        congr 1
        funext z
        rw [leviForm_norm_sub_sq, norm_coordinateVector, one_pow, one_mul]
    _ = n * ∫ z, φ z := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### The explicit kernels -/

/-- A function vanishing outside `B̄(0, r)`, translated by `y`, has topological support in
`B̄(y, r)`. -/
theorem tsupport_comp_sub_subset {f : ComplexModel n → ℝ} {r : ℝ}
    (hf : ∀ x, r < ‖x‖ → f x = 0) (y : ComplexModel n) :
    tsupport (fun z => f (z - y)) ⊆ closedBall y r := by
  refine closure_minimal (fun z hz => ?_) isClosed_closedBall
  rw [mem_closedBall, dist_eq_norm]
  by_contra h
  exact hz (hf _ (lt_of_not_ge h))

theorem explicitRadialKernel_eq_zero_of_lt (R : ℝ) (hR : 0 < R) (j : ℕ) {x : ComplexModel n}
    (hx : R / ((j : ℝ) + 1) < ‖x‖) : explicitRadialKernel R hR j x = 0 := by
  have hx' : x ∉ tsupport (explicitRadialKernel (n := n) R hR j) := by
    rw [explicitRadialKernel_tsupport, mem_closedBall, dist_zero_right]
    exact not_le.mpr hx
  exact image_eq_zero_of_notMem_tsupport hx'

theorem explicitRadialKernel_continuous (R : ℝ) (hR : 0 < R) (j : ℕ) :
    Continuous (explicitRadialKernel (n := n) R hR j) :=
  (explicitRadialKernel_contDiff R hR j).continuous

/-- The translated kernel `κ_j(· - y)` is supported in `B̄(y, R/(j+1))`. -/
theorem tsupport_explicitRadialKernel_sub_subset (R : ℝ) (hR : 0 < R) (j : ℕ)
    (y : ComplexModel n) :
    tsupport (fun z => explicitRadialKernel R hR j (z - y)) ⊆ closedBall y (R / ((j : ℝ) + 1)) :=
  tsupport_comp_sub_subset (fun _ hx => explicitRadialKernel_eq_zero_of_lt R hR j hx) y

theorem hasCompactSupport_explicitRadialKernel_sub (R : ℝ) (hR : 0 < R) (j : ℕ)
    (y : ComplexModel n) :
    HasCompactSupport (fun z => explicitRadialKernel (n := n) R hR j (z - y)) :=
  (isCompact_closedBall y _).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_explicitRadialKernel_sub_subset R hR j y)

theorem integral_explicitRadialKernel_sub (R : ℝ) (hR : 0 < R) (j : ℕ) (y : ComplexModel n) :
    ∫ z, explicitRadialKernel (n := n) R hR j (z - y) = 1 := by
  rw [integral_sub_right_eq_self (fun z => explicitRadialKernel (n := n) R hR j z) y]
  exact explicitRadialKernel_integral_one R hR j

/-- `w · κ_j(· - y)` is integrable when `w` is continuous on an open `U ⊇ B̄(y, R/(j+1))`. -/
theorem integrable_mul_explicitRadialKernel_sub {w : ComplexModel n → ℝ}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (hw : ContinuousOn w U) (R : ℝ) (hR : 0 < R)
    (j : ℕ) {y : ComplexModel n} (hyU : closedBall y (R / ((j : ℝ) + 1)) ⊆ U) :
    Integrable (fun z => w z * explicitRadialKernel R hR j (z - y)) :=
  integrable_mul_of_continuousOn hU hw
    ((explicitRadialKernel_continuous R hR j).comp (continuous_id.sub continuous_const))
    (hasCompactSupport_explicitRadialKernel_sub R hR j y)
    ((tsupport_explicitRadialKernel_sub_subset R hR j y).trans hyU)

theorem div_zero_succ (R : ℝ) : R / (((0 : ℕ) : ℝ) + 1) = R := by
  simp

theorem div_succ_le (R : ℝ) (hR : 0 < R) (j : ℕ) : R / ((j : ℝ) + 1) ≤ R := by
  rw [div_le_iff₀ (by positivity)]
  nlinarith [Nat.cast_nonneg (α := ℝ) j]

/-- **Approximate identity, one-sided**: for `w` continuous at `y ∈ U`, eventually
`w(y) ≤ ∫ w κ_b(· - y) + ε`. -/
theorem eventually_le_integral_mul_explicitRadialKernel {w : ComplexModel n → ℝ}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (hw : ContinuousOn w U) {y : ComplexModel n}
    (hy : y ∈ U) (R : ℝ) (hR : 0 < R) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ b : ℕ in atTop, w y ≤ (∫ z, w z * explicitRadialKernel R hR b (z - y)) + ε := by
  obtain ⟨δ₁, hδ₁, hδ₁U⟩ := Metric.isOpen_iff.mp hU y hy
  obtain ⟨δ₂, hδ₂, hδ₂w⟩ := Metric.continuousAt_iff.mp (hw.continuousAt (hU.mem_nhds hy)) ε hε
  set δ := min δ₁ δ₂ with hδ
  have hδ0 : 0 < δ := lt_min hδ₁ hδ₂
  have htend : Tendsto (fun b : ℕ => R / ((b : ℝ) + 1)) atTop (𝓝 0) := by
    have h : Tendsto (fun b : ℕ => ((b : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        tendsto_inv_atTop_zero.comp
          ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul h : Tendsto (fun b : ℕ => R * ((b : ℝ) + 1)⁻¹) atTop (𝓝 (R * 0)))
  filter_upwards [htend.eventually (gt_mem_nhds (half_pos hδ0))] with b hb
  have hball : closedBall y (R / ((b : ℝ) + 1)) ⊆ ball y δ :=
    closedBall_subset_ball (hb.trans (half_lt_self hδ0))
  have hballU : closedBall y (R / ((b : ℝ) + 1)) ⊆ U :=
    hball.trans ((ball_subset_ball (min_le_left _ _)).trans hδ₁U)
  have hint := integrable_mul_explicitRadialKernel_sub hU hw R hR b hballU
  have hκint : Integrable (fun z => explicitRadialKernel (n := n) R hR b (z - y)) :=
    ((explicitRadialKernel_continuous R hR b).comp (continuous_id.sub continuous_const))
      |>.integrable_of_hasCompactSupport (hasCompactSupport_explicitRadialKernel_sub R hR b y)
  have hkey : ∀ z, (w y - ε) * explicitRadialKernel R hR b (z - y) ≤
      w z * explicitRadialKernel R hR b (z - y) := by
    intro z
    by_cases hz : z ∈ ball y δ
    · have hzw : dist (w z) (w y) < ε := hδ₂w (lt_of_lt_of_le (mem_ball.mp hz) (min_le_right _ _))
      rw [Real.dist_eq] at hzw
      exact mul_le_mul_of_nonneg_right (by linarith [(abs_lt.mp hzw).1])
        (explicitRadialKernel_nonneg R hR b _)
    · have hz' : z ∉ tsupport (fun z => explicitRadialKernel (n := n) R hR b (z - y)) :=
        fun h => hz (hball (tsupport_explicitRadialKernel_sub_subset R hR b y h))
      have h0 : explicitRadialKernel R hR b (z - y) = 0 :=
        image_eq_zero_of_notMem_tsupport (f := fun z => explicitRadialKernel (n := n) R hR b (z - y)) hz'
      simp [h0]
  have h1 := integral_mono (hκint.const_mul (w y - ε)) hint hkey
  rw [integral_const_mul, integral_explicitRadialKernel_sub, mul_one] at h1
  linarith

/-! ### The mean-value inequalities -/

/-- **Sub-mean value inequality with quadratic error.**  If `w` is continuous on the open set
`U ⊇ B̄(y, R)` and its distributional coordinate Levi trace is at least `-M` (`M ≥ 0`), then
`w(y) ≤ ∫ w(z) κ_R(z - y) dz + (M / n) R²`. -/
theorem le_kernelAverage_add (hn : 0 < n) {w : ComplexModel n → ℝ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hw : ContinuousOn w U) {M : ℝ} (hM0 : 0 ≤ M) (hM : LeviTraceGE w U M)
    {y : ComplexModel n} {R : ℝ} (hR : 0 < R) (hyU : closedBall y R ⊆ U) :
    w y ≤ (∫ z, w z * explicitRadialKernel R hR 0 (z - y)) + M / n * R ^ 2 := by
  have hy : y ∈ U := hyU (mem_closedBall_self hR.le)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hyU0 : closedBall y (R / (((0 : ℕ) : ℝ) + 1)) ⊆ U := by rwa [div_zero_succ]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨b, hb⟩ := (eventually_le_integral_mul_explicitRadialKernel hU hw hy R hR hε).exists
  suffices hmain : ∫ z, w z * explicitRadialKernel R hR b (z - y) ≤
      (∫ z, w z * explicitRadialKernel R hR 0 (z - y)) + M / n * R ^ 2 by linarith
  -- the translated Poisson potential
  set Φ : ComplexModel n → ℝ := explicitRadialPoissonPotential R hR 0 b with hΦdef
  set φ : ComplexModel n → ℝ := fun z => Φ (z - y) with hφdef
  have hΦs : ContDiff ℝ ∞ Φ := explicitRadialPoissonPotential_contDiff hn R hR 0 b
  have hΦ2 : ContDiff ℝ 2 Φ := hΦs.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hφs : ContDiff ℝ ∞ φ := hΦs.comp (contDiff_id.sub contDiff_const)
  have hφsupp : tsupport φ ⊆ closedBall y R := by
    refine tsupport_comp_sub_subset (fun x hx => ?_) y
    exact explicitRadialPoissonPotential_eq_zero_of_outer hn R hR (Nat.zero_le b)
      (by rw [div_zero_succ]; exact hx.le)
  have hφc : HasCompactSupport φ :=
    (isCompact_closedBall y R).of_isClosed_subset (isClosed_tsupport _) hφsupp
  have hφ0 : ∀ z, 0 ≤ φ z := fun z =>
    explicitRadialPoissonPotential_nonneg hn R hR (Nat.zero_le b) _
  have hLT : ∀ z, coordinateLeviTrace φ z =
      (explicitRadialKernel R hR 0 (z - y) - explicitRadialKernel R hR b (z - y)) / 4 := by
    intro z
    rw [hφdef, coordinateLeviTrace_comp_sub hΦ2,
      ← four_mul_coordinateLeviTrace_explicitRadialPoissonPotential_eq_kernel_sub hn R hR 0 b]
    ring
  -- integrability
  have hb_le : R / ((b : ℝ) + 1) ≤ R := div_succ_le R hR b
  have hwb := integrable_mul_explicitRadialKernel_sub hU hw R hR b
    ((closedBall_subset_closedBall hb_le).trans hyU)
  have hw0 := integrable_mul_explicitRadialKernel_sub hU hw R hR 0 hyU0
  have hq : ContinuousOn (fun z : ComplexModel n => ‖z - y‖ ^ 2) univ :=
    (continuous_norm.comp (continuous_id.sub continuous_const)).pow 2 |>.continuousOn
  have hqb := integrable_mul_explicitRadialKernel_sub (y := y) isOpen_univ hq R hR b
    (subset_univ _)
  have hq0 := integrable_mul_explicitRadialKernel_sub (y := y) isOpen_univ hq R hR 0
    (subset_univ _)
  -- the hypothesis tested against `φ`
  have h1 := hM φ hφs hφc (hφsupp.trans hyU) hφ0
  have hwLT : ∫ z, w z * coordinateLeviTrace φ z =
      ((∫ z, w z * explicitRadialKernel R hR 0 (z - y)) -
        ∫ z, w z * explicitRadialKernel R hR b (z - y)) / 4 := by
    rw [← integral_sub hw0 hwb, ← integral_div]
    congr 1
    funext z
    rw [hLT]
    ring
  -- the mass of `φ`
  have h2 := integral_norm_sub_sq_mul_coordinateLeviTrace hφs hφc y
  have hqLT : ∫ z, ‖z - y‖ ^ 2 * coordinateLeviTrace φ z =
      ((∫ z, ‖z - y‖ ^ 2 * explicitRadialKernel R hR 0 (z - y)) -
        ∫ z, ‖z - y‖ ^ 2 * explicitRadialKernel R hR b (z - y)) / 4 := by
    rw [← integral_sub hq0 hqb, ← integral_div]
    congr 1
    funext z
    rw [hLT]
    ring
  have hq0le : ∫ z, ‖z - y‖ ^ 2 * explicitRadialKernel R hR 0 (z - y) ≤ R ^ 2 := by
    have hκ : Integrable (fun z => explicitRadialKernel (n := n) R hR 0 (z - y)) :=
      ((explicitRadialKernel_continuous R hR 0).comp (continuous_id.sub continuous_const))
        |>.integrable_of_hasCompactSupport (hasCompactSupport_explicitRadialKernel_sub R hR 0 y)
    have hle : ∀ z, ‖z - y‖ ^ 2 * explicitRadialKernel R hR 0 (z - y) ≤
        R ^ 2 * explicitRadialKernel R hR 0 (z - y) := by
      intro z
      by_cases hz : ‖z - y‖ ≤ R
      · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hz 2)
          (explicitRadialKernel_nonneg R hR 0 _)
      · have h0 : explicitRadialKernel (n := n) R hR 0 (z - y) = 0 :=
          explicitRadialKernel_eq_zero_of_lt R hR 0 (by rw [div_zero_succ]; exact lt_of_not_ge hz)
        simp [h0]
    have h := integral_mono hq0 (hκ.const_mul (R ^ 2)) hle
    rwa [integral_const_mul, integral_explicitRadialKernel_sub, mul_one] at h
  have hqb0 : 0 ≤ ∫ z, ‖z - y‖ ^ 2 * explicitRadialKernel R hR b (z - y) :=
    integral_nonneg fun z => mul_nonneg (sq_nonneg _) (explicitRadialKernel_nonneg R hR b _)
  have hmass : (n : ℝ) * ∫ z, φ z ≤ R ^ 2 / 4 := by
    rw [← h2, hqLT]
    linarith
  have hφint0 : 0 ≤ ∫ z, φ z := integral_nonneg hφ0
  have hMmass : M * ∫ z, φ z ≤ M / n * R ^ 2 / 4 := by
    have : M * ((n : ℝ) * ∫ z, φ z) ≤ M * (R ^ 2 / 4) := mul_le_mul_of_nonneg_left hmass hM0
    rw [div_mul_eq_mul_div, div_div, le_div_iff₀ (by positivity)]
    nlinarith
  rw [hwLT] at h1
  linarith

/-- **Super-mean value inequality with quadratic error.**  If `w` is continuous on the open set
`U ⊇ B̄(y, R)` and its distributional coordinate Levi trace is at most `M` (`M ≥ 0`), then
`∫ w(z) κ_R(z - y) dz - (M / n) R² ≤ w(y)`. -/
theorem kernelAverage_sub_le (hn : 0 < n) {w : ComplexModel n → ℝ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hw : ContinuousOn w U) {M : ℝ} (hM0 : 0 ≤ M) (hM : LeviTraceLE w U M)
    {y : ComplexModel n} {R : ℝ} (hR : 0 < R) (hyU : closedBall y R ⊆ U) :
    (∫ z, w z * explicitRadialKernel R hR 0 (z - y)) - M / n * R ^ 2 ≤ w y := by
  have h := le_kernelAverage_add hn hU (fun z hz => (hw z hz).neg) hM0 hM.neg hR hyU
  simp only [Pi.neg_apply] at h
  have hneg : ∫ z, -w z * explicitRadialKernel R hR 0 (z - y) =
      -∫ z, w z * explicitRadialKernel R hR 0 (z - y) := by
    rw [← integral_neg]
    congr 1
    funext z
    ring
  rw [hneg] at h
  linarith

/-! ### Kernel averages and ball integrals -/

/-- The raw profile of `κ_R` equals `1` on `B̄(0, R/2)`. -/
theorem explicitRadialRaw_eq_one (R : ℝ) (hR : 0 < R) {x : ComplexModel n}
    (hx : ‖x‖ ≤ R / 2) : explicitRadialRaw R hR 0 x = 1 := by
  unfold explicitRadialRaw
  apply (ContDiffBumpBase.ofInnerProductSpace (ComplexModel n)).eq_one 2 (by norm_num)
  rw [norm_smul, Real.norm_eq_abs, abs_inv]
  have hrIn : (shrinkingBump (E := ComplexModel n) R hR 0).rIn = R / 2 := by
    simp [shrinkingBump]
  rw [hrIn, abs_of_pos (by positivity : (0 : ℝ) < R / 2), inv_mul_le_iff₀ (by positivity),
    mul_one]
  exact hx

theorem integrable_explicitRadialRaw (R : ℝ) (hR : 0 < R) :
    Integrable (explicitRadialRaw (n := n) R hR 0) :=
  explicitRadialRaw_integrable R hR 0

/-- `vol B̄(0, R/2) ≤ ∫ raw ≤ vol B(0, R)`. -/
theorem volume_closedBall_half_le_integral_raw (R : ℝ) (hR : 0 < R) :
    volume.real (closedBall (0 : ComplexModel n) (R / 2)) ≤
      ∫ x : ComplexModel n, explicitRadialRaw R hR 0 x := by
  rw [← integral_indicator_one measurableSet_closedBall]
  have hfin : volume (closedBall (0 : ComplexModel n) (R / 2)) ≠ ⊤ :=
    measure_closedBall_lt_top.ne
  refine integral_mono ((integrable_indicator_iff measurableSet_closedBall).mpr
    (integrableOn_const hfin)) (integrable_explicitRadialRaw R hR) fun x => ?_
  · by_cases hx : x ∈ closedBall (0 : ComplexModel n) (R / 2)
    · rw [indicator_of_mem hx, Pi.one_apply,
        explicitRadialRaw_eq_one R hR (by simpa [mem_closedBall, dist_zero_right] using hx)]
    · rw [indicator_of_notMem hx]
      exact explicitRadialRaw_nonneg R hR 0 x

theorem integral_raw_le_volume_ball (R : ℝ) (hR : 0 < R) :
    ∫ x : ComplexModel n, explicitRadialRaw R hR 0 x ≤
      volume.real (ball (0 : ComplexModel n) R) := by
  have hball : MeasurableSet (ball (0 : ComplexModel n) R) := measurableSet_ball
  rw [← integral_indicator_one hball]
  have hfin : volume (ball (0 : ComplexModel n) R) ≠ ⊤ := measure_ball_lt_top.ne
  refine integral_mono (integrable_explicitRadialRaw R hR)
    ((integrable_indicator_iff hball).mpr (integrableOn_const hfin)) fun x => ?_
  by_cases hx : x ∈ ball (0 : ComplexModel n) R
  · rw [indicator_of_mem hx, Pi.one_apply]
    exact explicitRadialRaw_le_one R hR 0 x
  · rw [indicator_of_notMem hx]
    have hsupp : x ∉ Function.support (explicitRadialRaw (n := n) R hR 0) := by
      rw [explicitRadialRaw_support]
      simpa using hx
    exact (Function.notMem_support.mp hsupp).le

theorem explicitRadialKernel_eq_div (R : ℝ) (hR : 0 < R) (x : ComplexModel n) :
    explicitRadialKernel R hR 0 x =
      explicitRadialRaw R hR 0 x / ∫ y : ComplexModel n, explicitRadialRaw R hR 0 y := rfl

theorem volume_real_closedBall_pos (x : ComplexModel n) {r : ℝ} (hr : 0 < r) :
    0 < volume.real (closedBall x r) := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos (measure_closedBall_pos volume x hr).ne' measure_closedBall_lt_top.ne

/-- `κ_R ≤ 1 / vol B̄(0, R/2)` everywhere. -/
theorem explicitRadialKernel_le_inv (R : ℝ) (hR : 0 < R) (x : ComplexModel n) :
    explicitRadialKernel R hR 0 x ≤ 1 / volume.real (closedBall (0 : ComplexModel n) (R / 2)) := by
  rw [explicitRadialKernel_eq_div]
  have hV := volume_real_closedBall_pos (0 : ComplexModel n) (half_pos hR)
  have hI := volume_closedBall_half_le_integral_raw (n := n) R hR
  calc explicitRadialRaw R hR 0 x / ∫ y : ComplexModel n, explicitRadialRaw R hR 0 y
      ≤ 1 / ∫ y : ComplexModel n, explicitRadialRaw R hR 0 y :=
        div_le_div_of_nonneg_right (explicitRadialRaw_le_one R hR 0 x) (hV.le.trans hI)
    _ ≤ 1 / volume.real (closedBall (0 : ComplexModel n) (R / 2)) :=
        one_div_le_one_div_of_le hV hI

/-- `κ_R ≥ 1 / vol B(0, R)` on `B̄(0, R/2)`. -/
theorem inv_le_explicitRadialKernel (R : ℝ) (hR : 0 < R) {x : ComplexModel n}
    (hx : ‖x‖ ≤ R / 2) :
    1 / volume.real (ball (0 : ComplexModel n) R) ≤ explicitRadialKernel R hR 0 x := by
  rw [explicitRadialKernel_eq_div, explicitRadialRaw_eq_one R hR hx]
  have hV := volume_real_closedBall_pos (0 : ComplexModel n) (half_pos hR)
  have hI := volume_closedBall_half_le_integral_raw (n := n) R hR
  exact one_div_le_one_div_of_le (hV.trans_le hI) (integral_raw_le_volume_ball R hR)

/-- **Kernel average below a ball integral**: for `w ≥ 0` continuous on `U ⊇ B̄(y, R)`,
`∫ w κ_R(· - y) ≤ (∫_{B̄(y, R)} w) / vol B̄(0, R/2)`. -/
theorem kernelAverage_le_setIntegral_div {w : ComplexModel n → ℝ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hw : ContinuousOn w U) {y : ComplexModel n} {R : ℝ} (hR : 0 < R)
    (hyU : closedBall y R ⊆ U) (hw0 : ∀ z ∈ closedBall y R, 0 ≤ w z) :
    ∫ z, w z * explicitRadialKernel R hR 0 (z - y) ≤
      (∫ z in closedBall y R, w z) / volume.real (closedBall (0 : ComplexModel n) (R / 2)) := by
  have hyU0 : closedBall y (R / (((0 : ℕ) : ℝ) + 1)) ⊆ U := by rwa [div_zero_succ]
  have hint := integrable_mul_explicitRadialKernel_sub hU hw R hR 0 hyU0
  have hwB : IntegrableOn w (closedBall y R) :=
    (hw.mono hyU).integrableOn_compact (isCompact_closedBall y R)
  rw [← integral_indicator measurableSet_closedBall, ← integral_div]
  refine integral_mono hint ((hwB.integrable_indicator measurableSet_closedBall).div_const _)
    fun z => ?_
  by_cases hz : z ∈ closedBall y R
  · rw [indicator_of_mem hz, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (explicitRadialKernel_le_inv R hR _) (hw0 z hz)
  · rw [indicator_of_notMem hz]
    have h0 : explicitRadialKernel (n := n) R hR 0 (z - y) = 0 := by
      apply explicitRadialKernel_eq_zero_of_lt R hR 0
      rw [div_zero_succ, ← dist_eq_norm]
      simpa [mem_closedBall] using hz
    simp [h0]

/-- **Ball integral below a kernel average**: for `w ≥ 0` continuous on `U ⊇ B̄(y, R)`,
`(∫_{B̄(y, R/2)} w) / vol B(0, R) ≤ ∫ w κ_R(· - y)`. -/
theorem setIntegral_div_le_kernelAverage {w : ComplexModel n → ℝ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hw : ContinuousOn w U) {y : ComplexModel n} {R : ℝ} (hR : 0 < R)
    (hyU : closedBall y R ⊆ U) (hw0 : ∀ z ∈ closedBall y R, 0 ≤ w z) :
    (∫ z in closedBall y (R / 2), w z) / volume.real (ball (0 : ComplexModel n) R) ≤
      ∫ z, w z * explicitRadialKernel R hR 0 (z - y) := by
  have hyU0 : closedBall y (R / (((0 : ℕ) : ℝ) + 1)) ⊆ U := by rwa [div_zero_succ]
  have hint := integrable_mul_explicitRadialKernel_sub hU hw R hR 0 hyU0
  have hsub : closedBall y (R / 2) ⊆ closedBall y R :=
    closedBall_subset_closedBall (half_le_self hR.le)
  have hwB : IntegrableOn w (closedBall y (R / 2)) :=
    (hw.mono (hsub.trans hyU)).integrableOn_compact (isCompact_closedBall y _)
  rw [← integral_indicator measurableSet_closedBall, ← integral_div]
  refine integral_mono ((hwB.integrable_indicator measurableSet_closedBall).div_const _) hint
    fun z => ?_
  by_cases hz : z ∈ closedBall y (R / 2)
  · rw [indicator_of_mem hz, div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_left (inv_le_explicitRadialKernel R hR ?_) (hw0 z (hsub hz))
    rw [← dist_eq_norm]
    exact mem_closedBall.mp hz
  · rw [indicator_of_notMem hz, zero_div]
    by_cases hz' : z ∈ closedBall y R
    · exact mul_nonneg (hw0 z hz') (explicitRadialKernel_nonneg R hR 0 _)
    · have h0 : explicitRadialKernel (n := n) R hR 0 (z - y) = 0 := by
        apply explicitRadialKernel_eq_zero_of_lt R hR 0
        rw [div_zero_succ, ← dist_eq_norm]
        simpa [mem_closedBall] using hz'
      simp [h0]

end SGPT.Analysis.CZ
