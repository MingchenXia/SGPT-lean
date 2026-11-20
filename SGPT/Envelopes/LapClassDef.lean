import SGPT.Envelopes.LapClassGreen
import SGPT.Envelopes.LapClassFlat

/-!
# The book's `C^{1,1̄}(X)`: functions with bounded metric Laplacian

Lane LAP-CLASS (`claude-lap-class`, node `lap-class:class`).  The book uses the class
`C^{1,1̄}(X)` in `prop:DR16_C11bar`, `lma:DNTroof`, `thm:DNTcontact`, `cor:DNTenvelope1`,
`prop:DNTenvelope2`, `prop:DNTenvelope3` and `thm:DNT23_C11bar` without defining it; following
Darvas–Rubinstein and Di Nezza–Trapani (FPT `sec:metric-laplacian-obstacles`) it is the class of
continuous functions whose metric Laplacian (for the fixed Kähler form `ω` of `X`) is a bounded
function.  For `n ≥ 2` it is *not* the class of functions with bounded complex Hessian (FPT
`ex:metric-laplacian-unbounded-hessian`), and it depends on the Kähler form.

Since `Δ_ω` is symmetric for the Kähler volume (`integral_mul_laplacian_symm`), the distribution
`Δ_ω f` is `χ ↦ ∫ f Δ_ω χ ω^N`, and `Δ_ω f ∈ L^∞` with `|Δ_ω f| ≤ M` means
`-M ∫ χ ω^N ≤ ∫ f Δ_ω χ ω^N ≤ M ∫ χ ω^N` for smooth `χ ≥ 0` (FPT
`eq:penalized-distributional-trace-bound`); equivalently `|∫ f Δ_ω χ ω^N| ≤ M ∫ |χ| ω^N` for all
smooth `χ` (`abs_integral_mul_laplacian_le`).  We work with the Laplacian
`Δ_ω u = Re tr(H⁻¹ ∂∂̄u)` of TN (`KahlerLaplacianChart.laplacian`); FPT's metric Laplacian is
`L = -4π Δ_ω`, so the classes coincide.

## Main definitions

* `LaplacianLE w f M`, `LaplacianGE w f M`: `Δ_ω f ≤ M`, `Δ_ω f ≥ M` in the sense of distributions.
* `HasBoundedMetricLaplacian w f`: `f` continuous with `-M ≤ Δ_ω f ≤ M` for some `M`.

## Main results

* `laplacianLE_of_chartSmooth`, `laplacianGE_of_chartSmooth`: pointwise bounds of smooth functions.
* `hasBoundedMetricLaplacian_of_chartSmooth`: smooth functions are in the class.
* `laplacianLE_of_tendstoUniformly`: one-sided bounds pass to uniform limits.
* `abs_integral_mul_laplacian_le`: the bound against all smooth test functions.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Envelopes.LapClass

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open KahlerLaplacianChart KahlerLaplacianStokes IntegrationCurrent

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-! ### Linearity of the Laplacian -/

theorem laplacian_eq_trace (g : SmoothRealForm N Y 2) (u : Y → ℝ) (y : Y) :
    laplacian g u y = ((normalizedHermitianMatrix (g.coeff (complexChartAt (n := N) y)
      ((complexChartAt (n := N) y).val y)))⁻¹ * complexHessian
        (fun w => u ((complexChartAt (n := N) y).val.symm w))
          ((complexChartAt (n := N) y).val y)).trace.re := rfl

theorem laplacian_add (g : SmoothRealForm N Y 2) {u v : Y → ℝ} (hu : ChartSmooth (n := N) u)
    (hv : ChartSmooth (n := N) v) (y : Y) :
    laplacian g (fun x => u x + v x) y = laplacian g u y + laplacian g v y := by
  set e := complexChartAt (n := N) y
  have hz : e.val y ∈ e.val.target := e.val.map_source (mem_complexChartAt_source y)
  rw [laplacian_eq_trace, laplacian_eq_trace, laplacian_eq_trace,
    AubinYauLocalStep.complexHessian_fun_add
      (chartSmooth_two' hu e |>.contDiffAt (e.val.open_target.mem_nhds hz))
      (chartSmooth_two' hv e |>.contDiffAt (e.val.open_target.mem_nhds hz)),
    Matrix.mul_add, Matrix.trace_add, Complex.add_re]

theorem laplacian_const_mul (g : SmoothRealForm N Y 2) {u : Y → ℝ} (hu : ChartSmooth (n := N) u)
    (c : ℝ) (y : Y) : laplacian g (fun x => c * u x) y = c * laplacian g u y := by
  set e := complexChartAt (n := N) y
  have hz : e.val y ∈ e.val.target := e.val.map_source (mem_complexChartAt_source y)
  rw [laplacian_eq_trace, laplacian_eq_trace,
    AubinYauLocalStep.complexHessian_const_mul
      (chartSmooth_two' hu e |>.contDiffAt (e.val.open_target.mem_nhds hz)),
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

theorem laplacian_sub (g : SmoothRealForm N Y 2) {u v : Y → ℝ} (hu : ChartSmooth (n := N) u)
    (hv : ChartSmooth (n := N) v) (y : Y) :
    laplacian g (fun x => u x - v x) y = laplacian g u y - laplacian g v y := by
  have hv' : ChartSmooth (n := N) (fun x => (-1) * v x) := fun e => contDiffOn_const.mul (hv e)
  have h := laplacian_add g hu hv' y
  rw [laplacian_const_mul g hv] at h
  simp only [neg_one_mul, ← sub_eq_add_neg] at h
  exact h

/-- At a maximum point the Laplacian is nonpositive. -/
theorem laplacian_nonpos_of_isMax {g : SmoothRealForm N Y 2} (hg : g.IsHermitian) {u : Y → ℝ}
    (hu : ChartSmooth (n := N) u) {y₀ : Y} (hmax : ∀ y, u y ≤ u y₀) :
    laplacian g u y₀ ≤ 0 := by
  set e := complexChartAt (n := N) y₀
  have hy : y₀ ∈ e.val.source := mem_complexChartAt_source y₀
  have hz : e.val y₀ ∈ e.val.target := e.val.map_source hy
  have h2 : ContDiffAt ℝ 2 (fun w => u (e.val.symm w)) (e.val y₀) :=
    chartSmooth_two' hu e |>.contDiffAt (e.val.open_target.mem_nhds hz)
  have hloc : IsLocalMax (fun w => u (e.val.symm w)) (e.val y₀) :=
    Eventually.of_forall fun w => by
      show u (e.val.symm w) ≤ u (e.val.symm (e.val y₀))
      rw [e.val.left_inv hy]
      exact hmax _
  rw [laplacian_eq_trace]
  obtain ⟨m, v, hv, -⟩ := exists_trace_eq_sum_leviForm (posDef_coeff hg hz).inv.posSemidef
  rw [hv _ _ h2]
  exact Finset.sum_nonpos fun i _ =>
    SGPT.Okounkov.TranscendentalWNReg.leviForm_nonpos_of_isLocalMax h2 hloc (v i)

/-- Laplacians of chart-smooth functions are continuous. -/
theorem continuous_laplacian_of_chartSmooth {g : SmoothRealForm N Y 2} (hg : g.IsHermitian)
    {u : Y → ℝ} (hu : ChartSmooth (n := N) u) : Continuous (laplacian g u) :=
  continuous_laplacian hg (chartSmooth_two' hu)

variable [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

/-! ### Green's identity in every dimension -/

theorem integral_continuous {f : Y → ℝ} (hf : Continuous f) (μ : Measure Y) [IsFiniteMeasure μ] :
    Integrable f μ :=
  hf.integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))

/-- **Green's identity** (all dimensions). -/
theorem integral_mul_laplacian_comm (w : KahlerBackground N Y) {u v : Y → ℝ}
    (hu : ChartSmooth (n := N) u) (hv : ChartSmooth (n := N) v) :
    ∫ x, u x * laplacian w.form.val v x ∂(kahlerVolume w) =
      ∫ x, v x * laplacian w.form.val u x ∂(kahlerVolume w) := by
  rcases N with _ | m
  · have h0 : ∀ (f : Y → ℝ) x, laplacian w.form.val f x = 0 := fun f x => by
      simp [laplacian, chartLaplacian, Matrix.trace]
    simp [h0]
  · exact integral_mul_laplacian_symm w hu hv

/-! ### The class -/

/-- `Δ_ω f ≤ M` in the sense of distributions: `∫ f Δ_ω χ ω^N ≤ M ∫ χ ω^N` for every chart-smooth
`χ ≥ 0`. -/
def LaplacianLE (w : KahlerBackground N Y) (f : Y → ℝ) (M : ℝ) : Prop :=
  ∀ χ : Y → ℝ, ChartSmooth (n := N) χ → (∀ y, 0 ≤ χ y) →
    ∫ y, f y * laplacian w.form.val χ y ∂(kahlerVolume w) ≤ M * ∫ y, χ y ∂(kahlerVolume w)

/-- `M ≤ Δ_ω f` in the sense of distributions. -/
def LaplacianGE (w : KahlerBackground N Y) (f : Y → ℝ) (M : ℝ) : Prop :=
  ∀ χ : Y → ℝ, ChartSmooth (n := N) χ → (∀ y, 0 ≤ χ y) →
    M * ∫ y, χ y ∂(kahlerVolume w) ≤ ∫ y, f y * laplacian w.form.val χ y ∂(kahlerVolume w)

/-- **Bounded metric Laplacian: the book's `C^{1,1̄}(X)`** (Darvas–Rubinstein, Di Nezza–Trapani;
FPT `sec:metric-laplacian-obstacles`).  `f` is continuous and `-M ≤ Δ_ω f ≤ M` in the sense of
distributions for some `M`, i.e. `Δ_ω f ∈ L^∞(X)`. -/
def HasBoundedMetricLaplacian (w : KahlerBackground N Y) (f : Y → ℝ) : Prop :=
  Continuous f ∧ ∃ M : ℝ, LaplacianLE w f M ∧ LaplacianGE w f (-M)

/-- A pointwise upper bound of the Laplacian of a smooth function is a distributional one. -/
theorem laplacianLE_of_chartSmooth (w : KahlerBackground N Y) {f : Y → ℝ}
    (hf : ChartSmooth (n := N) f) {M : ℝ} (hM : ∀ y, laplacian w.form.val f y ≤ M) :
    LaplacianLE w f M := by
  intro χ hχ hχ0
  rw [integral_mul_laplacian_comm w hf hχ, ← integral_const_mul]
  refine integral_mono (integral_continuous ((YauUniformEstimate.continuous_of_chartSmooth
    hχ).mul (continuous_laplacian_of_chartSmooth w.isKahler.1 hf)) _)
    (integral_continuous (continuous_const.mul
      (YauUniformEstimate.continuous_of_chartSmooth hχ)) _) fun y => ?_
  rw [mul_comm M]
  exact mul_le_mul_of_nonneg_left (hM y) (hχ0 y)

/-- A pointwise lower bound of the Laplacian of a smooth function is a distributional one. -/
theorem laplacianGE_of_chartSmooth (w : KahlerBackground N Y) {f : Y → ℝ}
    (hf : ChartSmooth (n := N) f) {M : ℝ} (hM : ∀ y, M ≤ laplacian w.form.val f y) :
    LaplacianGE w f M := by
  intro χ hχ hχ0
  rw [integral_mul_laplacian_comm w hf hχ, ← integral_const_mul]
  refine integral_mono (integral_continuous (continuous_const.mul
      (YauUniformEstimate.continuous_of_chartSmooth hχ)) _)
    (integral_continuous ((YauUniformEstimate.continuous_of_chartSmooth
    hχ).mul (continuous_laplacian_of_chartSmooth w.isKahler.1 hf)) _) fun y => ?_
  rw [mul_comm M]
  exact mul_le_mul_of_nonneg_left (hM y) (hχ0 y)

/-- **Smooth functions have bounded metric Laplacian.** -/
theorem hasBoundedMetricLaplacian_of_chartSmooth (w : KahlerBackground N Y) {f : Y → ℝ}
    (hf : ChartSmooth (n := N) f) : HasBoundedMetricLaplacian w f := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_laplacian_of_chartSmooth w.isKahler.1 hf).continuousOn
  refine ⟨YauUniformEstimate.continuous_of_chartSmooth hf, M,
    laplacianLE_of_chartSmooth w hf fun y => ?_, laplacianGE_of_chartSmooth w hf fun y => ?_⟩
  · have := hM y (mem_univ y)
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  · have := hM y (mem_univ y)
    rw [Real.norm_eq_abs] at this
    exact neg_le_of_abs_le this

/-- An error estimate for the pairing with `Δ_ω χ`. -/
theorem abs_integral_sub_mul_laplacian_le (w : KahlerBackground N Y) {f g χ : Y → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hχ : ChartSmooth (n := N) χ) {ε : ℝ}
    (hfg : ∀ y, |f y - g y| ≤ ε) :
    |∫ y, f y * laplacian w.form.val χ y ∂(kahlerVolume w) -
        ∫ y, g y * laplacian w.form.val χ y ∂(kahlerVolume w)| ≤
      ε * ∫ y, |laplacian w.form.val χ y| ∂(kahlerVolume w) := by
  have hL := continuous_laplacian_of_chartSmooth w.isKahler.1 hχ
  have e := integral_sub (integral_continuous (hf.mul hL) (kahlerVolume w))
    (integral_continuous (hg.mul hL) (kahlerVolume w))
  have e2 := integral_const_mul (μ := kahlerVolume w) ε
    (fun y => |laplacian w.form.val χ y|)
  have hle : |∫ y, (f y * laplacian w.form.val χ y - g y * laplacian w.form.val χ y)
      ∂(kahlerVolume w)| ≤ ∫ y, ε * |laplacian w.form.val χ y| ∂(kahlerVolume w) := by
    refine (abs_integral_le_integral_abs).trans (integral_mono
      (integral_continuous ((hf.mul hL).sub (hg.mul hL)).abs _)
      (integral_continuous (continuous_const.mul hL.abs) _) fun y => ?_)
    simp only
    rw [← sub_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right (hfg y) (abs_nonneg _)
  exact (congrArg abs e).symm.trans_le (hle.trans_eq e2)

/-- **Upper bounds pass to uniform limits.** -/
theorem laplacianLE_of_tendstoUniformly (w : KahlerBackground N Y) {f : ℕ → Y → ℝ}
    {g : Y → ℝ} (hf : ∀ j, Continuous (f j)) (hconv : TendstoUniformly f g atTop) {M : ℝ}
    (hM : ∀ᶠ j in atTop, LaplacianLE w (f j) M) : LaplacianLE w g M := by
  intro χ hχ hχ0
  have hg : Continuous g := hconv.continuous (Frequently.of_forall hf)
  set I := ∫ y, |laplacian w.form.val χ y| ∂(kahlerVolume w) with hI
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  set ε := δ / (I + 1) with hε
  have hI0 : 0 ≤ I := integral_nonneg fun y => abs_nonneg _
  have hε0 : 0 < ε := div_pos hδ (by linarith)
  obtain ⟨j, hj1, hj2⟩ := ((Metric.tendstoUniformly_iff.mp hconv ε hε0).and hM).exists
  have hdist : ∀ y, |g y - f j y| ≤ ε := fun y => by
    have := hj1 y
    rw [Real.dist_eq] at this
    exact this.le
  have herr := abs_integral_sub_mul_laplacian_le w hg (hf j) hχ hdist
  have hj := hj2 χ hχ hχ0
  have hεI : ε * I < δ := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  linarith [(abs_le.mp herr).2]

/-- **Lower bounds pass to uniform limits.** -/
theorem laplacianGE_of_tendstoUniformly (w : KahlerBackground N Y) {f : ℕ → Y → ℝ}
    {g : Y → ℝ} (hf : ∀ j, Continuous (f j)) (hconv : TendstoUniformly f g atTop) {M : ℝ}
    (hM : ∀ᶠ j in atTop, LaplacianGE w (f j) M) : LaplacianGE w g M := by
  intro χ hχ hχ0
  have hg : Continuous g := hconv.continuous (Frequently.of_forall hf)
  set I := ∫ y, |laplacian w.form.val χ y| ∂(kahlerVolume w) with hI
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  set ε := δ / (I + 1) with hε
  have hI0 : 0 ≤ I := integral_nonneg fun y => abs_nonneg _
  have hε0 : 0 < ε := div_pos hδ (by linarith)
  obtain ⟨j, hj1, hj2⟩ := ((Metric.tendstoUniformly_iff.mp hconv ε hε0).and hM).exists
  have hdist : ∀ y, |g y - f j y| ≤ ε := fun y => by
    have := hj1 y
    rw [Real.dist_eq] at this
    exact this.le
  have herr := abs_integral_sub_mul_laplacian_le w hg (hf j) hχ hdist
  have hj := hj2 χ hχ hχ0
  have hεI : ε * I < δ := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  linarith [(abs_le.mp herr).1]

/-! ### The bound against all test functions -/

omit [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] in
/-- A smooth function splits as `χ = χ₊ - χ₋` with smooth `χ± ≥ 0` and
`χ₊ + χ₋ = √(χ² + δ²)`. -/
theorem chartSmooth_sqrt_sq_add {χ : Y → ℝ} (hχ : ChartSmooth (n := N) χ) {δ : ℝ} (hδ : 0 < δ) :
    ChartSmooth (n := N) (fun y => Real.sqrt (χ y ^ 2 + δ ^ 2)) := by
  intro e
  have h1 : ContDiffOn ℝ ∞ (fun z => χ (e.val.symm z) ^ 2 + δ ^ 2) e.val.target :=
    ((hχ e).pow 2).add contDiffOn_const
  exact h1.sqrt fun z _ => (by positivity : χ (e.val.symm z) ^ 2 + δ ^ 2 ≠ 0)

/-- **The `L¹`-dual form of the class**: if `-M ≤ Δ_ω f ≤ M` against nonnegative test functions,
then `|∫ f Δ_ω χ ω^N| ≤ M ∫ |χ| ω^N` for every chart-smooth `χ`, i.e. the distribution `Δ_ω f`
extends to a functional of norm `≤ M` on `L¹(ω^N)` (its density is bounded by `M`). -/
theorem abs_integral_mul_laplacian_le (w : KahlerBackground N Y) {f : Y → ℝ}
    (hf : Continuous f) {M : ℝ} (hLE : LaplacianLE w f M) (hGE : LaplacianGE w f (-M))
    {χ : Y → ℝ} (hχ : ChartSmooth (n := N) χ) :
    |∫ y, f y * laplacian w.form.val χ y ∂(kahlerVolume w)| ≤
      M * ∫ y, |χ y| ∂(kahlerVolume w) := by
  have hM0 : 0 ≤ M ∨ ∀ χ : Y → ℝ, ChartSmooth (n := N) χ → (∀ y, 0 ≤ χ y) →
      ∫ y, χ y ∂(kahlerVolume w) = 0 := by
    by_cases hM : 0 ≤ M
    · exact Or.inl hM
    · right
      intro ψ hψ hψ0
      have h1 := hLE ψ hψ hψ0
      have h2 := hGE ψ hψ hψ0
      have hI : 0 ≤ ∫ y, ψ y ∂(kahlerVolume w) := integral_nonneg hψ0
      push Not at hM
      nlinarith
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set V := (kahlerVolume w).real univ with hV
  have hV0 : 0 ≤ V := measureReal_nonneg
  set δ := ε / (2 * (|M| + 1) * (V + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  set s : Y → ℝ := fun y => Real.sqrt (χ y ^ 2 + δ ^ 2) with hs
  have hss : ChartSmooth (n := N) s := chartSmooth_sqrt_sq_add hχ hδ0
  set χp : Y → ℝ := fun y => (s y + χ y) / 2 with hχp
  set χm : Y → ℝ := fun y => (s y - χ y) / 2 with hχm
  have hsχ : ∀ y, |χ y| ≤ s y := fun y => by
    rw [hs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hsle : ∀ y, s y ≤ |χ y| + δ := fun y => by
    rw [hs]
    refine (Real.sqrt_le_sqrt (show χ y ^ 2 + δ ^ 2 ≤ (|χ y| + δ) ^ 2 by
      nlinarith [abs_nonneg (χ y), sq_abs (χ y)])).trans ?_
    rw [Real.sqrt_sq (by positivity)]
  have hχp0 : ∀ y, 0 ≤ χp y := fun y => by
    have := hsχ y; have := neg_abs_le (χ y); simp only [hχp]; linarith
  have hχm0 : ∀ y, 0 ≤ χm y := fun y => by
    have := hsχ y; have := le_abs_self (χ y); simp only [hχm]; linarith
  have hχps : ChartSmooth (n := N) χp := fun e => ((hss e).add (hχ e)).div_const 2
  have hχms : ChartSmooth (n := N) χm := fun e => ((hss e).sub (hχ e)).div_const 2
  have hcχ := YauUniformEstimate.continuous_of_chartSmooth hχ
  have hcs := YauUniformEstimate.continuous_of_chartSmooth hss
  have hsplit : ∀ y, laplacian w.form.val χ y =
      laplacian w.form.val χp y - laplacian w.form.val χm y := fun y => by
    have h1 : χ = fun x => χp x - χm x := funext fun x => by simp only [hχp, hχm]; ring
    conv_lhs => rw [h1]
    exact laplacian_sub _ hχps hχms y
  have hL := fun g (hg : ChartSmooth (n := N) g) =>
    continuous_laplacian_of_chartSmooth w.isKahler.1 hg
  have hint : ∫ y, f y * laplacian w.form.val χ y ∂(kahlerVolume w) =
      ∫ y, f y * laplacian w.form.val χp y ∂(kahlerVolume w) -
        ∫ y, f y * laplacian w.form.val χm y ∂(kahlerVolume w) := by
    have e := integral_sub (integral_continuous (hf.mul (hL _ hχps)) (kahlerVolume w))
      (integral_continuous (hf.mul (hL _ hχms)) (kahlerVolume w))
    refine Eq.trans ?_ e
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [Pi.mul_apply]
    rw [hsplit y]
    ring
  have hIp := hLE χp hχps hχp0
  have hIp' := hGE χp hχps hχp0
  have hIm := hLE χm hχms hχm0
  have hIm' := hGE χm hχms hχm0
  have hsum : ∫ y, χp y ∂(kahlerVolume w) + ∫ y, χm y ∂(kahlerVolume w) =
      ∫ y, s y ∂(kahlerVolume w) := by
    rw [← integral_add (integral_continuous (by simp only [hχp]; fun_prop) _)
      (integral_continuous (by simp only [hχm]; fun_prop) _)]
    congr 1
    funext y
    simp only [hχp, hχm]
    ring
  have hsbound : ∫ y, s y ∂(kahlerVolume w) ≤ ∫ y, |χ y| ∂(kahlerVolume w) + δ * V := by
    have h := integral_mono (integral_continuous hcs (kahlerVolume w))
      (integral_continuous (hcχ.abs.add continuous_const) (kahlerVolume w)) hsle
    have e1 : ∫ y, (|χ y| + δ) ∂(kahlerVolume w) =
        ∫ y, |χ y| ∂(kahlerVolume w) + ∫ _y, δ ∂(kahlerVolume w) :=
      integral_add (integral_continuous hcχ.abs (kahlerVolume w)) (integrable_const δ)
    have e2 : ∫ _y, δ ∂(kahlerVolume w) = V * δ := by
      simp only [integral_const, smul_eq_mul, hV]
    have e3 : ∫ y, s y ∂(kahlerVolume w) ≤ ∫ y, (|χ y| + δ) ∂(kahlerVolume w) := h
    rw [e1, e2] at e3
    linarith
  have hp0 : 0 ≤ ∫ y, χp y ∂(kahlerVolume w) := integral_nonneg hχp0
  have hm0 : 0 ≤ ∫ y, χm y ∂(kahlerVolume w) := integral_nonneg hχm0
  have habs : |∫ y, f y * laplacian w.form.val χ y ∂(kahlerVolume w)| ≤
      |M| * ∫ y, s y ∂(kahlerVolume w) := by
    rw [hint, abs_le, ← hsum]
    constructor <;> nlinarith [abs_nonneg M, le_abs_self M, neg_abs_le M]
  rcases hM0 with hM | hzero
  · rw [abs_of_nonneg hM] at habs
    have hδV : M * (δ * V) < ε := by
      have : M * (δ * V) ≤ (|M| + 1) * (δ * (V + 1)) := by
        rw [abs_of_nonneg hM]; nlinarith
      have h2 : (|M| + 1) * (δ * (V + 1)) = ε / 2 := by
        rw [hδ]; field_simp
      linarith
    nlinarith
  · have hp := hzero χp hχps hχp0
    have hm := hzero χm hχms hχm0
    have h0 : |∫ y, f y * laplacian w.form.val χ y ∂(kahlerVolume w)| = 0 := by
      rw [hint, abs_eq_zero]
      have := hIp; have := hIp'; have := hIm; have := hIm'
      rw [hp] at *; rw [hm] at *
      linarith
    have : 0 ≤ M * ∫ y, |χ y| ∂(kahlerVolume w) ∨ True := Or.inr trivial
    rw [h0]
    have hI : 0 ≤ ∫ y, |χ y| ∂(kahlerVolume w) := integral_nonneg fun y => abs_nonneg _
    by_cases hM : 0 ≤ M
    · nlinarith
    · -- `M < 0` forces the volume to vanish
      push Not at hM
      have hone := hzero (fun _ => 1) (ProductTestForms.chartSmooth_const 1) fun _ => zero_le_one
      have habs0 : ∫ y, |χ y| ∂(kahlerVolume w) = 0 := by
        have hb : ∃ B, ∀ y, |χ y| ≤ B := by
          obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hcχ.continuousOn
          exact ⟨B, fun y => by have := hB y (mem_univ y); rwa [Real.norm_eq_abs] at this⟩
        obtain ⟨B, hB⟩ := hb
        have h1 : ∫ y, |χ y| ∂(kahlerVolume w) ≤ ∫ _y, B ∂(kahlerVolume w) :=
          integral_mono (integral_continuous hcχ.abs (kahlerVolume w)) (integrable_const B) hB
        rw [integral_const, smul_eq_mul] at h1
        have hV' : V = 0 := by
          have : ∫ _y, (1 : ℝ) ∂(kahlerVolume w) = V := by
            rw [integral_const, smul_eq_mul, mul_one]
          rw [← this]; exact hone
        rw [← hV, hV', zero_mul] at h1
        exact le_antisymm h1 hI
      rw [habs0, mul_zero]
      linarith

end SGPT.Envelopes.LapClass
