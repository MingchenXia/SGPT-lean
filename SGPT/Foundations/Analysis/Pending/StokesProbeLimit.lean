import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false

/-!
# The limit step of the one-sided probe (TN.4 #4, Stokes against `[V]`)

Remark `ana:stokes-one-sided-probe` and Theorem `ana:stokes-regular-locus-identity` prove
`∫_{V_reg} ddᶜv ∧ S = 0` from three facts: an integration by parts against cutoffs `χ_m`
vanishing near `V_sing`, `∫ χ_m ddᶜv ∧ S = ∫ (v - c) ddᶜχ_m ∧ S` for every constant `c`
(`ana:stokes-patch-ibp`); the almost-positivity `ddᶜχ_m + ε_m β ≥ 0` with `ε_m → 0`
(`ana:stokes-cutoffs`), wedged with the positive `S`; and the finiteness of `∫ β ∧ S`.  This module
is the measure-theoretic core of that argument, stated for an abstract measure `μ` (the
measure of `V_reg`) and densities: `f` (of `ddᶜv ∧ S`), `b ≥ 0` (of `β ∧ S`), `q_m` (of
`ddᶜχ_m ∧ S`), a bounded `v`.  Taking `c = sup v` and `c = inf v` gives
`|∫ χ_m f| ≤ ε_m (sup v - inf v) ∫ b`, and dominated convergence gives `∫ f = 0`.

Source: Demailly, CADG III.2.2--2.3, 2.7 (`demailly-cadg:III.2.3`), in the form of the remark;
no Cauchy--Schwarz inequality is needed for smooth potentials.

## Main results

* `abs_integral_mul_le` — one cutoff: `|∫ χ f| ≤ ε (hi - lo) ∫ b`.
* `integral_eq_zero_of_probe` — the limit: `∫ f = 0`.
-/


open Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.StokesProbeLimit

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- One cutoff: if `∫ χ f = ∫ (v - c) q` for the two constants `c = hi` and `c = lo` bounding
`v`, and `q + ε b ≥ 0` with `b ≥ 0`, then `|∫ χ f| ≤ ε (hi - lo) ∫ b`. -/
theorem abs_integral_mul_le {f b v χ q : α → ℝ} {ε lo hi : ℝ}
    (hb : Integrable b μ) (hb0 : ∀ x, 0 ≤ b x)
    (hv : ∀ x, lo ≤ v x ∧ v x ≤ hi) (hvm : AEStronglyMeasurable v μ)
    (hq : Integrable q μ) (hε : 0 ≤ ε) (hqpos : ∀ x, 0 ≤ q x + ε * b x)
    (hhi : ∫ x, χ x * f x ∂μ = ∫ x, (v x - hi) * q x ∂μ)
    (hlo : ∫ x, χ x * f x ∂μ = ∫ x, (v x - lo) * q x ∂μ) :
    |∫ x, χ x * f x ∂μ| ≤ ε * (hi - lo) * ∫ x, b x ∂μ := by
  have hbnd : ∀ c : ℝ, Integrable (fun x => (v x - c) * q x) μ := by
    intro c
    refine hq.bdd_mul (c := max |lo - c| |hi - c|) (hvm.sub aestronglyMeasurable_const) ?_
    refine Eventually.of_forall fun x => ?_
    have := hv x
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have : -(max |lo - c| |hi - c|) ≤ lo - c := by
        have h1 : -|lo - c| ≤ lo - c := neg_abs_le _
        have h2 : |lo - c| ≤ max |lo - c| |hi - c| := le_max_left _ _
        linarith
      linarith [(hv x).1]
    · have : hi - c ≤ max |lo - c| |hi - c| := (le_abs_self _).trans (le_max_right _ _)
      linarith [(hv x).2]
  have hbv : ∀ c : ℝ, Integrable (fun x => (v x - c) * b x) μ := by
    intro c
    refine hb.bdd_mul (c := max |lo - c| |hi - c|) (hvm.sub aestronglyMeasurable_const) ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have h1 : -|lo - c| ≤ lo - c := neg_abs_le _
      have h2 : |lo - c| ≤ max |lo - c| |hi - c| := le_max_left _ _
      linarith [(hv x).1]
    · have : hi - c ≤ max |lo - c| |hi - c| := (le_abs_self _).trans (le_max_right _ _)
      linarith [(hv x).2]
  -- split `∫ (v - c) q = ∫ (v - c)(q + ε b) - ε ∫ (v - c) b`
  have hsplit : ∀ c : ℝ, ∫ x, (v x - c) * q x ∂μ =
      ∫ x, (v x - c) * (q x + ε * b x) ∂μ - ε * ∫ x, (v x - c) * b x ∂μ := by
    intro c
    have h1 : Integrable (fun x => (v x - c) * (q x + ε * b x)) μ := by
      have := (hbnd c).add ((hbv c).const_mul ε)
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply]; ring
    rw [← integral_const_mul, ← integral_sub h1 ((hbv c).const_mul ε)]
    congr 1; funext x; ring
  have hint_b : 0 ≤ ∫ x, b x ∂μ := integral_nonneg hb0
  -- upper bound with `c = hi`
  have hup : ∫ x, χ x * f x ∂μ ≤ ε * (hi - lo) * ∫ x, b x ∂μ := by
    rw [hhi, hsplit hi]
    have h1 : ∫ x, (v x - hi) * (q x + ε * b x) ∂μ ≤ 0 :=
      integral_nonpos fun x => mul_nonpos_of_nonpos_of_nonneg (by linarith [(hv x).2]) (hqpos x)
    have h2 : -(∫ x, (v x - hi) * b x ∂μ) ≤ (hi - lo) * ∫ x, b x ∂μ := by
      rw [← integral_neg, ← integral_const_mul]
      refine integral_mono (hbv hi).neg (hb.const_mul _) fun x => ?_
      have := hb0 x
      nlinarith [(hv x).1]
    nlinarith [mul_le_mul_of_nonneg_left h2 hε]
  -- lower bound with `c = lo`
  have hdown : -(ε * (hi - lo) * ∫ x, b x ∂μ) ≤ ∫ x, χ x * f x ∂μ := by
    rw [hlo, hsplit lo]
    have h1 : 0 ≤ ∫ x, (v x - lo) * (q x + ε * b x) ∂μ :=
      integral_nonneg fun x => mul_nonneg (by linarith [(hv x).1]) (hqpos x)
    have h2 : ∫ x, (v x - lo) * b x ∂μ ≤ (hi - lo) * ∫ x, b x ∂μ := by
      rw [← integral_const_mul]
      refine integral_mono (hbv lo) (hb.const_mul _) fun x => ?_
      have := hb0 x
      nlinarith [(hv x).2]
    nlinarith [mul_le_mul_of_nonneg_left h2 hε]
  exact abs_le.2 ⟨hdown, hup⟩

/-- **The limit of the one-sided probe** (Remark `ana:stokes-one-sided-probe`): if cutoffs
`0 ≤ χ_m ≤ 1` tend to `1` almost everywhere and every `∫ χ_m f` is controlled as in
`abs_integral_mul_le` with errors `ε_m → 0`, then `∫ f = 0`. -/
theorem integral_eq_zero_of_probe {f b v : α → ℝ} {χ q : ℕ → α → ℝ} {ε : ℕ → ℝ} {lo hi : ℝ}
    (hf : Integrable f μ) (hb : Integrable b μ) (hb0 : ∀ x, 0 ≤ b x)
    (hv : ∀ x, lo ≤ v x ∧ v x ≤ hi) (hvm : AEStronglyMeasurable v μ)
    (hχ : ∀ m x, 0 ≤ χ m x ∧ χ m x ≤ 1) (hχm : ∀ m, AEStronglyMeasurable (χ m) μ)
    (hχlim : ∀ᵐ x ∂μ, Tendsto (fun m => χ m x) atTop (𝓝 1))
    (hε0 : ∀ m, 0 ≤ ε m) (hε : Tendsto ε atTop (𝓝 0))
    (hq : ∀ m, Integrable (q m) μ) (hqpos : ∀ m x, 0 ≤ q m x + ε m * b x)
    (hibp : ∀ m (c : ℝ), ∫ x, χ m x * f x ∂μ = ∫ x, (v x - c) * q m x ∂μ) :
    ∫ x, f x ∂μ = 0 := by
  -- dominated convergence: `∫ χ_m f → ∫ f`
  have hdom : Tendsto (fun m => ∫ x, χ m x * f x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
    have := tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
      (fun m => (hχm m).mul hf.aestronglyMeasurable) hf.norm
      (fun m => Eventually.of_forall fun x => by
        rw [Pi.mul_apply, norm_mul]
        have h := hχ m x
        have : ‖χ m x‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
        calc ‖χ m x‖ * ‖f x‖ ≤ 1 * ‖f x‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
          _ = ‖f x‖ := one_mul _)
      (hχlim.mono fun x hx => by simpa using hx.mul_const (f x))
    exact this
  -- the bound: `|∫ χ_m f| ≤ ε_m (hi - lo) ∫ b → 0`
  have hbound : ∀ m, |∫ x, χ m x * f x ∂μ| ≤ ε m * (hi - lo) * ∫ x, b x ∂μ := fun m =>
    abs_integral_mul_le hb hb0 hv hvm (hq m) (hε0 m) (hqpos m) (hibp m hi) (hibp m lo)
  have hzero : Tendsto (fun m => ∫ x, χ m x * f x ∂μ) atTop (𝓝 0) := by
    have hlim : Tendsto (fun m => ε m * (hi - lo) * ∫ x, b x ∂μ) atTop (𝓝 0) := by
      simpa using (hε.mul_const (hi - lo)).mul_const (∫ x, b x ∂μ)
    exact squeeze_zero_norm (fun m => by rw [Real.norm_eq_abs]; exact hbound m) hlim
  exact tendsto_nhds_unique hdom hzero

end SGPT.Foundations.Analysis.Pending.StokesProbeLimit
