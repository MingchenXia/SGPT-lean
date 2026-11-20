import SGPT.Okounkov.TranscendentalWNConvStatement
import SGPT.Okounkov.TranscendentalWNDeformationLine
import Mathlib.Analysis.Convex.Deriv

/-!
# The obstacles `g_k` of WN21 §6

Blueprint `tok-wn-conv6:obstacle` (chapter `claude-tok-wn-conv6`); source WN21 §6.

* `IsWNCutoff`: `x ≤ χ(x)`, `χ ≤ 0` on `(-∞, 0]`, `0 < χ' ≤ 1`, so `χ` is increasing and
  `x ↦ χ(x) - x` is nonincreasing.
* `cutoffLog χ r = r - 1` for `0 ≤ r ≤ e⁻¹`, `= χ(log r)` for `r > 0`, `= log r` for `r ≥ 1`;
  `cutoffLineProfile χ k z = cutoffLog χ (eᵏ |z|²)` is smooth on `ℂ` (`contDiff_cutoffLineProfile`).
* `affineLinePoint τ = [τ : 1]`, and `g_k([τ : 1]) = cutoffLog χ (eᵏ|τ|²) - k - log(1 + |τ|²)`.
* In the affine chart of `ℙ¹`, `g_k = cutoffLineProfile χ k - k - log(1 + |z|²)`; near `∞`, in the
  chart `σ = 1/τ`, `g_k = -log(1 + |σ|²)` for `|σ|² < eᵏ`.  Hence `g_k` is chart-smooth on `ℙ¹`
  (`chartSmooth_cutoffObstacleLine`) and on `𝒳` (`chartSmooth_cutoffObstacle`).
* `g_{k+1} ≤ g_k` and `log N₀ ≤ g_k` with equality when `eᵏ|τ|² ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Toric

/-! ### Elementary properties of the cutoff -/

namespace IsWNCutoff

variable {χ : ℝ → ℝ} (hχ : IsWNCutoff χ)
include hχ

theorem differentiable : Differentiable ℝ χ :=
  hχ.contDiff.differentiable (by simp)

theorem eventuallyEq_of_neg {x : ℝ} (hx : x < -1) :
    χ =ᶠ[𝓝 x] fun y => Real.exp y - 1 := by
  filter_upwards [Iio_mem_nhds hx] with y hy using hχ.eq_of_le_neg_one y (le_of_lt hy)

theorem eventuallyEq_of_pos {x : ℝ} (hx : 0 < x) : χ =ᶠ[𝓝 x] fun y => y := by
  filter_upwards [Ioi_mem_nhds hx] with y hy using hχ.eq_of_nonneg y (le_of_lt hy)

theorem deriv_of_neg {x : ℝ} (hx : x < -1) : deriv χ x = Real.exp x := by
  rw [(hχ.eventuallyEq_of_neg hx).deriv_eq]
  exact ((Real.hasDerivAt_exp x).sub_const 1).deriv

theorem deriv_of_pos {x : ℝ} (hx : 0 < x) : deriv χ x = 1 := by
  rw [(hχ.eventuallyEq_of_pos hx).deriv_eq]
  exact deriv_id x

theorem monotone_deriv : Monotone (deriv χ) := by
  intro x y hxy
  exact (hχ.convexOn.monotoneOn_deriv fun z _ => hχ.differentiable z) (mem_univ x) (mem_univ y)
    hxy

theorem deriv_pos (x : ℝ) : 0 < deriv χ x := by
  rcases lt_or_ge x (-2) with hx | hx
  · rw [hχ.deriv_of_neg (by linarith)]; exact Real.exp_pos x
  · calc (0 : ℝ) < Real.exp (-2) := Real.exp_pos _
      _ = deriv χ (-2) := (hχ.deriv_of_neg (by norm_num)).symm
      _ ≤ deriv χ x := hχ.monotone_deriv hx

theorem deriv_le_one (x : ℝ) : deriv χ x ≤ 1 := by
  rcases lt_or_ge 0 x with hx | hx
  · rw [hχ.deriv_of_pos hx]
  · calc deriv χ x ≤ deriv χ 1 := hχ.monotone_deriv (by linarith)
      _ = 1 := hχ.deriv_of_pos one_pos

theorem strictMono : StrictMono χ := strictMono_of_deriv_pos hχ.deriv_pos

theorem monotone : Monotone χ := hχ.strictMono.monotone

/-- `x ↦ χ(x) - x` is nonincreasing (`χ' ≤ 1`). -/
theorem antitone_sub : Antitone fun x => χ x - x := by
  refine antitone_of_deriv_nonpos (hχ.differentiable.sub differentiable_id) fun x => ?_
  have h : HasDerivAt (fun y => χ y - y) (deriv χ x - 1) x :=
    (hχ.differentiable x).hasDerivAt.sub (hasDerivAt_id x)
  rw [h.deriv]
  linarith [hχ.deriv_le_one x]

/-- `x ≤ χ(x)`. -/
theorem le_self (x : ℝ) : x ≤ χ x := by
  rcases le_total 0 x with hx | hx
  · rw [hχ.eq_of_nonneg x hx]
  · have h := hχ.antitone_sub hx
    simp only [hχ.eq_of_nonneg 0 le_rfl, sub_self] at h
    linarith

/-- `χ ≤ 0` on `(-∞, 0]`. -/
theorem le_zero {x : ℝ} (hx : x ≤ 0) : χ x ≤ 0 := by
  have := hχ.monotone hx
  rwa [hχ.eq_of_nonneg 0 le_rfl] at this

end IsWNCutoff

/-! ### `cutoffLog` -/

theorem cutoffLog_of_pos (χ : ℝ → ℝ) {r : ℝ} (hr : 0 < r) : cutoffLog χ r = χ (Real.log r) := by
  rw [cutoffLog, if_neg hr.ne']

theorem cutoffLog_zero (χ : ℝ → ℝ) : cutoffLog χ 0 = -1 := by
  rw [cutoffLog, if_pos rfl]

theorem cutoffLog_of_le {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ Real.exp (-1)) : cutoffLog χ r = r - 1 := by
  rcases hr0.eq_or_lt with h | h
  · subst h; rw [cutoffLog_zero]; ring
  · rw [cutoffLog_of_pos χ h, hχ.eq_of_le_neg_one _ ((Real.log_le_iff_le_exp h).mpr hr),
      Real.exp_log h]

theorem cutoffLog_of_one_le {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) {r : ℝ} (hr : 1 ≤ r) :
    cutoffLog χ r = Real.log r := by
  rw [cutoffLog_of_pos χ (by linarith), hχ.eq_of_nonneg _ (Real.log_nonneg hr)]

theorem neg_one_le_cutoffLog {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) (r : ℝ) : -1 ≤ cutoffLog χ r := by
  by_cases h : r = 0
  · rw [h, cutoffLog_zero]
  · rw [cutoffLog, if_neg h]
    rcases le_total (Real.log r) (-1) with hl | hl
    · rw [hχ.eq_of_le_neg_one _ hl]; linarith [Real.exp_pos (Real.log r)]
    · have := hχ.monotone hl
      rw [hχ.eq_of_le_neg_one _ le_rfl] at this
      linarith [Real.exp_pos (-1 : ℝ)]

/-! ### The profile `χ(log(eᵏ |z|²))` on the affine line -/

/-- `z ↦ cutoffLog χ (eᵏ |z|²)` on the one-dimensional model, i.e. `χ(log |z|² + k)`. -/
def cutoffLineProfile (χ : ℝ → ℝ) (k : ℕ) (z : ComplexModel 1) : ℝ :=
  cutoffLog χ (Real.exp k * ‖z 0‖ ^ 2)

theorem contDiff_normSq_zero : ContDiff ℝ ∞ (fun z : ComplexModel 1 => ‖z 0‖ ^ 2) := by
  simpa only [projectiveModelEquiv_symm_apply, ← Complex.sq_norm]
    using contDiff_projectiveModel_normSq

theorem contDiff_cutoffLineProfile {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) (k : ℕ) :
    ContDiff ℝ ∞ (cutoffLineProfile χ k) := by
  set r : ComplexModel 1 → ℝ := fun z => Real.exp k * ‖z 0‖ ^ 2 with hr
  have hrs : ContDiff ℝ ∞ r := contDiff_const.mul contDiff_normSq_zero
  have hr0 : ∀ z, 0 ≤ r z := fun z => by positivity
  rw [contDiff_iff_contDiffAt]
  intro z
  rcases lt_or_ge (r z) (Real.exp (-1)) with h | h
  · -- near small `r`, the profile is `r - 1`
    have hev : cutoffLineProfile χ k =ᶠ[𝓝 z] fun y => r y - 1 := by
      filter_upwards [hrs.continuous.continuousAt.eventually (gt_mem_nhds h)] with y hy
      exact cutoffLog_of_le hχ (hr0 y) hy.le
    exact (hrs.sub contDiff_const).contDiffAt.congr_of_eventuallyEq hev
  · have hpos : 0 < r z := lt_of_lt_of_le (Real.exp_pos _) h
    have hev : cutoffLineProfile χ k =ᶠ[𝓝 z] fun y => χ (Real.log (r y)) := by
      filter_upwards [hrs.continuous.continuousAt.eventually (lt_mem_nhds hpos)] with y hy
      exact cutoffLog_of_pos χ hy
    exact (hχ.contDiff.contDiffAt.comp z (hrs.contDiffAt.log hpos.ne')).congr_of_eventuallyEq hev

/-! ### Points of the affine line -/

theorem affineLinePoint_eq_mk (τ : ℂ) :
    affineLinePoint τ = Projectivization.mk ℂ ![τ, 1] (by simp) := by
  apply projectiveLineHomeomorph.symm.injective
  rw [affineLinePoint, Homeomorph.symm_apply_apply, projectiveLineHomeomorph_symm_mk]
  simp

@[simp] theorem projectiveAffine_affineLinePoint (τ : ℂ) :
    projectiveAffine (affineLinePoint τ) = τ := by
  rw [affineLinePoint_eq_mk, projectiveAffine_mk]; simp

theorem affineLinePoint_zero : affineLinePoint 0 = projectiveZero := rfl

theorem affineLinePoint_injective : Function.Injective affineLinePoint := by
  intro a b h
  have := congrArg projectiveAffine h
  simpa using this

theorem affineLinePoint_ne_projectiveZero {τ : ℂ} (hτ : τ ≠ 0) :
    affineLinePoint τ ≠ projectiveZero := by
  rw [← affineLinePoint_zero]; exact fun h => hτ (affineLinePoint_injective h)

theorem mk_eq_projectiveInfinity_iff (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv = projectiveInfinity ↔ v 1 = 0 := by
  constructor
  · intro h
    have h' := congrArg projectiveLineHomeomorph.symm h
    rw [projectiveLineHomeomorph_symm_mk, projectiveInfinity, Homeomorph.symm_apply_apply] at h'
    by_contra h1
    rw [if_neg h1] at h'
    exact OnePoint.coe_ne_infty _ h'
  · intro h1
    apply projectiveLineHomeomorph.symm.injective
    rw [projectiveLineHomeomorph_symm_mk, if_pos h1, projectiveInfinity,
      Homeomorph.symm_apply_apply]

theorem affineLinePoint_ne_infinity (τ : ℂ) : affineLinePoint τ ≠ projectiveInfinity := by
  rw [affineLinePoint_eq_mk, Ne, mk_eq_projectiveInfinity_iff]; simp

theorem cutoffObstacleLine_affineLinePoint (χ : ℝ → ℝ) (k : ℕ) (τ : ℂ) :
    cutoffObstacleLine χ k (affineLinePoint τ) =
      cutoffLog χ (Real.exp k * ‖τ‖ ^ 2) - k - Real.log (1 + ‖τ‖ ^ 2) := by
  rw [cutoffObstacleLine]
  simp only [affineLinePoint_ne_infinity, if_false, projectiveAffine_affineLinePoint]

theorem cutoffObstacleLine_infinity (χ : ℝ → ℝ) (k : ℕ) :
    cutoffObstacleLine χ k projectiveInfinity = 0 := by
  rw [cutoffObstacleLine]; simp

/-! ### Chart expressions and smoothness on `ℙ¹` -/

theorem cutoffObstacleLine_chart_false (χ : ℝ → ℝ) (k : ℕ) (z : ComplexModel 1) :
    cutoffObstacleLine χ k ((projectiveModelChart false).symm z) =
      cutoffLineProfile χ k z - k - projectiveFSPotential z := by
  have hp : (projectiveModelChart false).symm z = affineLinePoint (z 0) := by
    rw [projectiveModelChart_symm_eq_mk, affineLinePoint_eq_mk]
    congr 1
  rw [hp, cutoffObstacleLine_affineLinePoint, cutoffLineProfile, projectiveFSPotential_eq,
    ← Complex.sq_norm]

theorem cutoffObstacleLine_chart_true_of_ne (χ : ℝ → ℝ) (k : ℕ) {z : ComplexModel 1}
    (hz : z 0 ≠ 0) :
    cutoffObstacleLine χ k ((projectiveModelChart true).symm z) =
      cutoffLog χ (Real.exp k * ‖(z 0)⁻¹‖ ^ 2) - k - Real.log (1 + ‖(z 0)⁻¹‖ ^ 2) := by
  have hp : (projectiveModelChart true).symm z = affineLinePoint (z 0)⁻¹ := by
    rw [projectiveModelChart_symm_eq_mk, affineLinePoint_eq_mk]
    rw [Projectivization.mk_eq_mk_iff]
    refine ⟨Units.mk0 (z 0) hz, ?_⟩
    ext i
    fin_cases i <;> simp [projectiveAffineLift, projectiveModelEquiv_symm_apply, hz]
  rw [hp, cutoffObstacleLine_affineLinePoint]

theorem cutoffObstacleLine_chart_true_of_small {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) (k : ℕ)
    {z : ComplexModel 1} (hz : ‖z 0‖ ^ 2 < Real.exp k) :
    cutoffObstacleLine χ k ((projectiveModelChart true).symm z) =
      -Real.log (1 + ‖z 0‖ ^ 2) := by
  by_cases h0 : z 0 = 0
  · have hp : (projectiveModelChart true).symm z = projectiveInfinity := by
      rw [projectiveModelChart_symm_eq_mk, mk_eq_projectiveInfinity_iff]
      simp [projectiveAffineLift, projectiveModelEquiv_symm_apply, h0]
    rw [hp, cutoffObstacleLine_infinity, h0]; simp
  · rw [cutoffObstacleLine_chart_true_of_ne χ k h0]
    have hn : 0 < ‖z 0‖ ^ 2 := by positivity
    have hinv : ‖(z 0)⁻¹‖ ^ 2 = (‖z 0‖ ^ 2)⁻¹ := by rw [norm_inv, inv_pow]
    rw [hinv]
    have hge : 1 ≤ Real.exp k * (‖z 0‖ ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hn, one_mul]; exact hz.le
    rw [cutoffLog_of_one_le hχ hge, Real.log_mul (Real.exp_pos _).ne' (inv_pos.mpr hn).ne',
      Real.log_exp, Real.log_inv]
    have h1 : 1 + (‖z 0‖ ^ 2)⁻¹ = (‖z 0‖ ^ 2 + 1) / ‖z 0‖ ^ 2 := by field_simp
    rw [h1, Real.log_div (by positivity) hn.ne', add_comm (‖z 0‖ ^ 2) 1]
    ring

theorem contDiff_chart_true {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) (k : ℕ) :
    ContDiff ℝ ∞ fun z => cutoffObstacleLine χ k ((projectiveModelChart true).symm z) := by
  have hn := contDiff_normSq_zero
  rw [contDiff_iff_contDiffAt]
  intro z
  rcases lt_or_ge (‖z 0‖ ^ 2) (Real.exp k) with h | h
  · have hev : (fun z => cutoffObstacleLine χ k ((projectiveModelChart true).symm z)) =ᶠ[𝓝 z]
        fun y => -Real.log (1 + ‖y 0‖ ^ 2) := by
      filter_upwards [hn.continuous.continuousAt.eventually (gt_mem_nhds h)] with y hy
      exact cutoffObstacleLine_chart_true_of_small hχ k hy
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    exact ((contDiff_const.add hn).contDiffAt.log (by positivity)).neg
  · have hpos : 0 < ‖z 0‖ ^ 2 := lt_of_lt_of_le (Real.exp_pos _) h
    have hz0 : z 0 ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hpos; norm_num at hpos
    have hcoord : ContDiff ℂ ∞ (fun y : ComplexModel 1 => y 0) :=
      (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).contDiff
    have hinv : ContDiffAt ℝ ∞ (fun y : ComplexModel 1 => (y 0)⁻¹) z :=
      ((contDiffAt_inv ℂ hz0).comp z hcoord.contDiffAt).restrict_scalars ℝ
    have hinvsq : ContDiffAt ℝ ∞ (fun y : ComplexModel 1 => ‖(y 0)⁻¹‖ ^ 2) z :=
      (contDiff_norm_sq ℝ).contDiffAt.comp z hinv
    have hev : (fun z => cutoffObstacleLine χ k ((projectiveModelChart true).symm z)) =ᶠ[𝓝 z]
        fun y => cutoffLog χ (Real.exp k * ‖(y 0)⁻¹‖ ^ 2) - k - Real.log (1 + ‖(y 0)⁻¹‖ ^ 2) := by
      filter_upwards [hcoord.continuous.continuousAt.eventually_ne hz0] with y hy
      exact cutoffObstacleLine_chart_true_of_ne χ k hy
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    have hq : 0 < Real.exp k * ‖(z 0)⁻¹‖ ^ 2 := by
      have : (z 0)⁻¹ ≠ 0 := inv_ne_zero hz0
      positivity
    have hqs : ContDiffAt ℝ ∞ (fun y : ComplexModel 1 => Real.exp k * ‖(y 0)⁻¹‖ ^ 2) z :=
      contDiffAt_const.mul hinvsq
    have hprof : ContDiffAt ℝ ∞ (fun y : ComplexModel 1 =>
        cutoffLog χ (Real.exp k * ‖(y 0)⁻¹‖ ^ 2)) z := by
      have hev2 : (fun y : ComplexModel 1 => cutoffLog χ (Real.exp k * ‖(y 0)⁻¹‖ ^ 2)) =ᶠ[𝓝 z]
          fun y => χ (Real.log (Real.exp k * ‖(y 0)⁻¹‖ ^ 2)) := by
        filter_upwards [hqs.continuousAt.eventually (lt_mem_nhds hq)] with y hy
        exact cutoffLog_of_pos χ hy
      exact (hχ.contDiff.contDiffAt.comp z (hqs.log hq.ne')).congr_of_eventuallyEq hev2
    exact (hprof.sub contDiffAt_const).sub ((contDiffAt_const.add hinvsq).log (by positivity))

theorem contDiff_chart_false {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) (k : ℕ) :
    ContDiff ℝ ∞ fun z => cutoffObstacleLine χ k ((projectiveModelChart false).symm z) := by
  simp_rw [cutoffObstacleLine_chart_false]
  exact ((contDiff_cutoffLineProfile hχ k).sub contDiff_const).sub contDiff_projectiveFSPotential

/-- **`g_k` is chart-smooth on `ℙ¹`.** -/
theorem chartSmooth_cutoffObstacleLine {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) (k : ℕ) :
    ChartSmooth (n := 1) (cutoffObstacleLine χ k) := by
  intro e
  obtain ⟨b, hb⟩ := (mem_projectiveNativeAtlas_iff e.val).mp e.property
  rw [hb]
  cases b
  · exact (contDiff_chart_false hχ k).contDiffOn
  · exact (contDiff_chart_true hχ k).contDiffOn

theorem continuous_cutoffObstacleLine {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) (k : ℕ) :
    Continuous (cutoffObstacleLine χ k) :=
  SGPT.Foundations.Analysis.Pending.ProductTestForms.ChartSmooth.continuous
    (chartSmooth_cutoffObstacleLine hχ k)

/-! ### Monotonicity and comparison with `log N₀` -/

/-- `g_{k+1} ≤ g_k`. -/
theorem cutoffObstacleLine_succ_le {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) (k : ℕ) (p : ProjectiveLine) :
    cutoffObstacleLine χ (k + 1) p ≤ cutoffObstacleLine χ k p := by
  by_cases hp : p = projectiveInfinity
  · subst hp; rw [cutoffObstacleLine_infinity, cutoffObstacleLine_infinity]
  · have hpt : p = affineLinePoint (projectiveAffine p) := by
      have h1 : p.rep 1 ≠ 0 := by
        intro h1
        apply hp
        rw [← Projectivization.mk_rep p, mk_eq_projectiveInfinity_iff]; exact h1
      conv_lhs => rw [← Projectivization.mk_rep p]
      rw [affineLinePoint_eq_mk, Projectivization.mk_eq_mk_iff]
      refine ⟨Units.mk0 (p.rep 1) h1, ?_⟩
      ext i
      fin_cases i <;> simp [projectiveAffine, Units.smul_def]; field_simp
    rw [hpt, cutoffObstacleLine_affineLinePoint, cutoffObstacleLine_affineLinePoint]
    set τ := projectiveAffine p
    by_cases hτ : τ = 0
    · simp [hτ, cutoffLog_zero]; linarith
    · have hn : 0 < ‖τ‖ ^ 2 := by positivity
      rw [cutoffLog_of_pos χ (by positivity), cutoffLog_of_pos χ (by positivity),
        Real.log_mul (Real.exp_pos _).ne' hn.ne', Real.log_mul (Real.exp_pos _).ne' hn.ne',
        Real.log_exp, Real.log_exp]
      have h := hχ.antitone_sub (show (k : ℝ) + Real.log (‖τ‖ ^ 2) ≤
        ((k + 1 : ℕ) : ℝ) + Real.log (‖τ‖ ^ 2) by push_cast; linarith)
      push_cast at h ⊢
      linarith

theorem cutoffObstacleLine_antitone {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) (p : ProjectiveLine) :
    Antitone fun k => cutoffObstacleLine χ k p :=
  antitone_nat_of_succ_le fun k => cutoffObstacleLine_succ_le hχ k p

/-! ### The obstacle on `𝒳` -/

section Deformation

variable {X : Type*} {N : ℕ} {𝒳 : Type*} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel N) 𝒳]
  [IsComplexManifold N 𝒳]

/-- **`g_k` is chart-smooth on `𝒳`** (`g_k ∘ π_{ℙ¹} ∘ μ`, with `π_{ℙ¹} ∘ μ` holomorphic). -/
theorem chartSmooth_cutoffObstacle {μ : 𝒳 → X × ProjectiveLine}
    (hμ : ContMDiff 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel 1) ∞ fun z => (μ z).2)
    {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) (k : ℕ) :
    ChartSmooth (n := N) (cutoffObstacle μ χ k) :=
  SGPT.Foundations.Analysis.Pending.ProductTestForms.chartSmooth_comp hμ
    (chartSmooth_cutoffObstacleLine hχ k)

omit [IsComplexManifold N 𝒳] in
theorem continuous_cutoffObstacle {μ : 𝒳 → X × ProjectiveLine}
    (hμ : ContMDiff 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel 1) ∞ fun z => (μ z).2)
    {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) (k : ℕ) : Continuous (cutoffObstacle μ χ k) :=
  (continuous_cutoffObstacleLine hχ k).comp hμ.continuous

omit [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel N) 𝒳] [IsComplexManifold N 𝒳] in
theorem cutoffObstacle_antitone {μ : 𝒳 → X × ProjectiveLine} {χ : ℝ → ℝ} (hχ : IsWNCutoff χ)
    (z : 𝒳) : Antitone fun k => cutoffObstacle μ χ k z :=
  cutoffObstacleLine_antitone hχ (μ z).2

end Deformation

end SGPT.Okounkov.TranscendentalWN
