import SGPT.Okounkov.TranscendentalWNRegLaplacian
import SGPT.Okounkov.TranscendentalWNRegC11bar
import SGPT.Analysis.CZGradient
import SGPT.Envelopes.C11RealStatement

/-!
# Uniform bounds for the solutions of the penalized equations: values and gradients

Lane TOS-C11b (`claude-tos-c11b`, node `tos-c11b:gradient`).  Source: Xia, *Foundations of
pluripotential theory*, `lem:penalized-real-hessian`, Step 1 ("it bounds `|a|` by `‖f‖_∞` and …
bounds `∇a` uniformly"), for SGPT `thm:Tos_C11` (Tosatti, Chu–Zhou).

Let `Y` be a compact connected complex manifold with a Kähler background `A` and let `u = u_β` be
a β-solution of `(A + ddᶜu)^N = e^{β(u - F)} A^N` (`BetaSolution`, Berman's equation; smooth
existence by Aubin–Yau is `exists_betaSolution`) for a chart-smooth obstacle `F` with `|F| ≤ B` and
`ddᶜF ≤ S·A` on complex lines.

* `abs_betaSolution_le` — `|u| ≤ B + N log(1 + S)` for `β ≥ 1` (Berman's comparison,
  `betaSolution_le_add` and `le_betaSolution_of_le`).
* `abs_ddc_betaSolution_le` — for `β ≥ β₀` (Berman's Laplacian estimate `betaSolution_line_le`):
  `|ddᶜu| ≤ (Λ' + 1)·A` on complex lines, with `Λ'` depending only on `(Y, A, B, S)`.
* `exists_betaSolution_gradient_bound` — **the uniform gradient bound**: for chart data `D` and
  `δ > 0` with the closed `2δ`-thickenings of the pieces inside the chart targets, there is `C`
  depending only on `(Y, A, D, δ, B, S)` with `‖D(u ∘ e_i⁻¹)‖ ≤ C` on the `δ`-thickening of every
  piece, for every `β ≥ β₀`.

FPT obtains the gradient bound from `W^{2,p}` estimates and Morrey's inequality.  Here the
Calderón–Zygmund-free interior Lipschitz estimate `exists_lipschitz_of_laplacian_bound` (lane
C11-REAL) is applied to `u ∘ e_i⁻¹`, whose flat Laplacian is bounded because its complex Hessian is.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace SGPT.Envelopes.TosC11b

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Foundations.Analysis.Pending.RadialLeviPreimage
open SGPT.Okounkov.TranscendentalWNReg SGPT.Analysis.CZ SGPT.Envelopes.C11Real

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- **Bound for the values** (FPT Step 1; Berman 2019, Proposition 2.3): for `β ≥ 1`, `|F| ≤ B` and
`ddᶜF ≤ S·A` on lines (`S ≥ 0`), a β-solution satisfies `|u| ≤ B + N log(1 + S)`. -/
theorem abs_betaSolution_le [CompactSpace Y] {A : KahlerBackground N Y} {β : ℝ} (hβ : 1 ≤ β)
    {F : Y → ℝ} (hF : ChartSmooth (n := N) F) {S : ℝ} (hS : 0 ≤ S)
    (hFS : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      ∀ v : ComplexModel N, (ddcClosedForm F hF).val.coeff e z ![v, Complex.I • v] ≤
        S * A.form.val.coeff e z ![v, Complex.I • v])
    {B : ℝ} (hB : ∀ y, |F y| ≤ B) (U : BetaSolution A β F) (y : Y) :
    |U.u y| ≤ B + N * Real.log (1 + S) := by
  have hβ0 : 0 < β := by linarith
  have hlog : 0 ≤ N * Real.log (1 + S) := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
  have hup := betaSolution_le_add hβ0 hF hS hFS U y
  have hdiv : N * Real.log (1 + S) / β ≤ N * Real.log (1 + S) := div_le_self hlog hβ
  have hlow := le_betaSolution_of_le hβ0 (c := -B) (fun y => by linarith [neg_abs_le (F y), hB y])
    U y
  have hFy := (abs_le.mp (hB y))
  rw [abs_le]
  constructor <;> linarith

/-- **Two-sided line bound for `ddᶜu`** (Berman's Laplacian estimate, uniformly in `β ≥ β₀`): with
the constants `a, Λ, β₀` of `betaSolution_line_le`, for `β ≥ max β₀ 1`, `|F| ≤ B` and `ddᶜF ≤ S·A`,
`|ddᶜu| ≤ ((1 + S) Λ e^{a(2B + N log(1 + S))} + 1)·A` on every complex line. -/
theorem abs_ddc_betaSolution_le [CompactSpace Y] {A : KahlerBackground N Y} {a Λ β₀ : ℝ}
    (ha : 0 ≤ a) (hΛ : 0 < Λ)
    (hlap : ∀ (β : ℝ), β₀ ≤ β → ∀ (F : Y → ℝ) (hF : ChartSmooth (n := N) F) (S : ℝ), 0 ≤ S →
      (∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        ∀ v : ComplexModel N, (ddcClosedForm F hF).val.coeff e z ![v, Complex.I • v] ≤
          S * A.form.val.coeff e z ![v, Complex.I • v]) →
      ∀ (U : BetaSolution A β F) (m : ℝ), (∀ y, m ≤ U.u y) →
      ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target → ∀ v : ComplexModel N,
        (A.form + ddcClosedForm U.u U.smooth).val.coeff e z ![v, Complex.I • v] ≤
          (1 + S) * Λ * Real.exp (a * (U.u (e.val.symm z) - m)) *
            A.form.val.coeff e z ![v, Complex.I • v])
    {β : ℝ} (hβ₀ : β₀ ≤ β) (hβ : 1 ≤ β) {F : Y → ℝ} (hF : ChartSmooth (n := N) F) {S : ℝ}
    (hS : 0 ≤ S)
    (hFS : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      ∀ v : ComplexModel N, (ddcClosedForm F hF).val.coeff e z ![v, Complex.I • v] ≤
        S * A.form.val.coeff e z ![v, Complex.I • v])
    {B : ℝ} (hB : ∀ y, |F y| ≤ B) (U : BetaSolution A β F) (e : ComplexChart N Y)
    {z : ComplexModel N} (hz : z ∈ e.val.target) (v : ComplexModel N) :
    |(ddcClosedForm U.u U.smooth).val.coeff e z ![v, Complex.I • v]| ≤
      ((1 + S) * Λ * Real.exp (a * (2 * B + N * Real.log (1 + S))) + 1) *
        A.form.val.coeff e z ![v, Complex.I • v] := by
  have hβ0 : 0 < β := by linarith
  have hm : ∀ y, -B ≤ U.u y := fun y =>
    le_betaSolution_of_le hβ0 (c := -B) (fun y => by linarith [neg_abs_le (F y), hB y]) U y
  have hline := hlap β hβ₀ F hF S hS hFS U (-B) hm e z hz v
  have hA0 : 0 ≤ A.form.val.coeff e z ![v, Complex.I • v] :=
    coefficientSemipositive_of_isKahler A.isKahler hz v
  have hK0 : 0 ≤ (A.form + ddcClosedForm U.u U.smooth).val.coeff e z ![v, Complex.I • v] :=
    coefficientSemipositive_of_isKahler U.isKahler hz v
  rw [add_ddc_line] at hline hK0
  have hu := abs_betaSolution_le hβ hF hS hFS hB U (e.val.symm z)
  have hexp : Real.exp (a * (U.u (e.val.symm z) - -B)) ≤
      Real.exp (a * (2 * B + N * Real.log (1 + S))) := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ ha
    linarith [(abs_le.mp hu).2]
  have h1S : 0 ≤ (1 + S) * Λ := by have : 0 ≤ 1 + S := by linarith
                                   positivity
  have hup : (1 + S) * Λ * Real.exp (a * (U.u (e.val.symm z) - -B)) *
      A.form.val.coeff e z ![v, Complex.I • v] ≤
      (1 + S) * Λ * Real.exp (a * (2 * B + N * Real.log (1 + S))) *
        A.form.val.coeff e z ![v, Complex.I • v] :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp h1S) hA0
  have hE0 : 0 ≤ (1 + S) * Λ * Real.exp (a * (2 * B + N * Real.log (1 + S))) *
      A.form.val.coeff e z ![v, Complex.I • v] := by positivity
  rw [abs_le]
  constructor <;> nlinarith

/-- Points near a point of the `δ`-thickening stay in the open `2δ`-thickening. -/
theorem closedBall_subset_thickening_two_mul {n : ℕ} {K : Set (ComplexModel n)} {δ : ℝ}
    (hδ : 0 < δ) {z y : ComplexModel n} (hz : z ∈ cthickening δ K) (hy : y ∈ ball z (δ / 4)) :
    closedBall y (δ / 4) ⊆ thickening (2 * δ) K := by
  have hr : (0 : ℝ) ≤ δ / 4 := by positivity
  have h1 : y ∈ cthickening (δ / 4 + δ) K :=
    cthickening_cthickening_subset hr hδ.le K
      (closedBall_subset_cthickening hz (δ / 4) (ball_subset_closedBall hy))
  refine (closedBall_subset_cthickening h1 (δ / 4)).trans
    ((cthickening_cthickening_subset hr (by positivity) K).trans
      (cthickening_subset_thickening' (by positivity) (by linarith) K))

/-- **Uniform gradient bound for the β-solutions** (FPT `lem:penalized-real-hessian`, Step 1).  Let
`Y` be compact connected with a Kähler background `A`, `D` chart data and `δ > 0` with the closed
`2δ`-thickenings of the pieces inside the chart targets.  There is `β₀ ≥ 1` such that for all
`B, S` (`S ≥ 0`) there is `C` with: for every `β ≥ β₀`, every chart-smooth `F` with `|F| ≤ B` and
`ddᶜF ≤ S·A` on lines and every β-solution `u`, `‖D(u ∘ e_i⁻¹)(z)‖ ≤ C` on the closed
`δ`-thickening of every piece `K_i`. -/
theorem exists_betaSolution_gradient_bound [CompactSpace Y] [ConnectedSpace Y]
    (A : KahlerBackground N Y) (D : C11ChartData N Y) {δ : ℝ} (hδ : 0 < δ)
    (hδU : ∀ i, cthickening (2 * δ) (D.piece i) ⊆ (D.chart i).val.target) :
    ∃ β₀ : ℝ, 1 ≤ β₀ ∧ ∀ B S : ℝ, 0 ≤ S → ∃ C : ℝ, ∀ β : ℝ, β₀ ≤ β →
      ∀ (F : Y → ℝ) (hF : ChartSmooth (n := N) F), (∀ y, |F y| ≤ B) →
      (∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        ∀ v : ComplexModel N, (ddcClosedForm F hF).val.coeff e z ![v, Complex.I • v] ≤
          S * A.form.val.coeff e z ![v, Complex.I • v]) →
      ∀ (U : BetaSolution A β F) (i : Fin D.card), ∀ z ∈ cthickening δ (D.piece i),
        ‖fderiv ℝ (fun w => U.u ((D.chart i).val.symm w)) z‖ ≤ C := by
  obtain ⟨a, Λ, β₁, ha, hΛ, -, hlap⟩ := betaSolution_line_le A
  refine ⟨max β₁ 1, le_max_right _ _, fun B S hS => ?_⟩
  -- the dimension-zero case: every derivative vanishes
  rcases Nat.eq_zero_or_pos N with hN | hN
  · refine ⟨0, fun β _ F hF _ _ U i z _ => ?_⟩
    subst hN
    have : fderiv ℝ (fun w => U.u ((D.chart i).val.symm w)) z = 0 :=
      ContinuousLinearMap.ext fun v => by
        rw [Subsingleton.elim v 0, map_zero, map_zero]
    rw [this, norm_zero]
  -- constants
  obtain ⟨CZ, hCZ0, hCZ⟩ := exists_lipschitz_of_laplacian_bound hN
  set Λ' : ℝ := (1 + S) * Λ * Real.exp (a * (2 * |B| + N * Real.log (1 + S))) with hΛ'
  have hΛ'0 : 0 ≤ Λ' := by
    have : 0 ≤ 1 + S := by linarith
    positivity
  have hcK : ∀ i, ∃ c : ℝ, 0 ≤ c ∧ ∀ z ∈ cthickening (2 * δ) (D.piece i), ∀ v : ComplexModel N,
      |A.form.val.coeff (D.chart i) z ![v, Complex.I • v]| ≤ c * ‖v‖ ^ 2 := fun i =>
    exists_line_le_of_isCompact A.form.val (D.chart i) ((D.isCompact_piece i).cthickening)
      (hδU i)
  choose c hc0 hc using hcK
  set B' : ℝ := |B| + N * Real.log (1 + S) with hB'
  set r : ℝ := δ / 4 with hr
  have hr0 : 0 < r := by positivity
  set M : Fin D.card → ℝ := fun i => N * (Real.pi * ((Λ' + 1) * c i)) with hM
  have hM0 : ∀ i, 0 ≤ M i := fun i => by have := hc0 i; positivity
  have hlog : 0 ≤ N * Real.log (1 + S) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
  have hB'0 : 0 ≤ B' := by positivity
  refine ⟨∑ i, CZ * (B' / r + M i * r), fun β hβ F hF hFB hFS U i z hz => ?_⟩
  have hβ₁ : β₁ ≤ β := (le_max_left _ _).trans hβ
  have hβ1 : 1 ≤ β := (le_max_right _ _).trans hβ
  set e := D.chart i
  set w : ComplexModel N → ℝ := fun y => U.u (e.val.symm y) with hw
  set W := thickening (2 * δ) (D.piece i) with hW
  have hWU : W ⊆ e.val.target := (thickening_subset_cthickening _ _).trans (hδU i)
  have hWo : IsOpen W := isOpen_thickening
  have hsm : ContDiffOn ℝ ∞ w W := (U.smooth e).mono hWU
  -- `|w| ≤ B'`
  have hwB : ∀ y ∈ W, |w y| ≤ B' := fun y _ => by
    have := abs_betaSolution_le hβ1 hF hS hFS (fun y => (hFB y).trans (le_abs_self B)) U
      (e.val.symm y)
    exact this
  -- the Laplacian bound on `W`
  have htrace : ∀ y ∈ W, |coordinateLeviTrace w y| ≤ M i := by
    intro y hy
    have hyt := hWU hy
    have hyK : y ∈ cthickening (2 * δ) (D.piece i) := thickening_subset_cthickening _ _ hy
    have hlev : ∀ j : Fin N, |leviForm w y (coordinateVector j)| ≤
        Real.pi * ((Λ' + 1) * c i) := by
      intro j
      have h1 := ddc_line_eq U.smooth e hyt (coordinateVector j)
      have h2 := abs_ddc_betaSolution_le ha hΛ hlap hβ₁ hβ1 hF hS hFS
        (fun y => (hFB y).trans (le_abs_self B)) U e hyt (coordinateVector j)
      have h3 := hc i y hyK (coordinateVector j)
      have hnorm : ‖coordinateVector (n := N) j‖ = 1 := by
        simp [coordinateVector, PiLp.norm_single]
      rw [hnorm, one_pow, mul_one] at h3
      have hA0 : 0 ≤ A.form.val.coeff e y ![coordinateVector j, Complex.I • coordinateVector j] :=
        coefficientSemipositive_of_isKahler A.isKahler hyt _
      rw [abs_of_nonneg hA0] at h3
      have hlevi : leviForm w y (coordinateVector j) = Real.pi *
          (ddcClosedForm U.u U.smooth).val.coeff e y
            ![coordinateVector j, Complex.I • coordinateVector j] := by
        rw [h1]; field_simp; rfl
      rw [hlevi, abs_mul, abs_of_pos Real.pi_pos]
      have h2' : |(ddcClosedForm U.u U.smooth).val.coeff e y
          ![coordinateVector j, Complex.I • coordinateVector j]| ≤ (Λ' + 1) * c i := by
        refine h2.trans ?_
        have hle : (1 + S) * Λ * Real.exp (a * (2 * |B| + N * Real.log (1 + S))) + 1 ≤ Λ' + 1 :=
          le_rfl
        exact mul_le_mul hle h3 hA0 (by linarith)
      exact mul_le_mul_of_nonneg_left h2' Real.pi_pos.le
    calc |coordinateLeviTrace w y| = |∑ j : Fin N, leviForm w y (coordinateVector j)| := rfl
      _ ≤ ∑ j : Fin N, |leviForm w y (coordinateVector j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin N, Real.pi * ((Λ' + 1) * c i) := Finset.sum_le_sum fun j _ => hlev j
      _ = M i := by simp [hM]
  have hdist : ∀ φ : ComplexModel N → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ W →
      |∫ y, w y * coordinateLeviTrace φ y| ≤ M i * ∫ y, |φ y| := fun φ hφ hφc hφW =>
    abs_integral_mul_coordinateLeviTrace_le_of_contDiffOn hWo hsm htrace hφ hφc hφW
  -- the Lipschitz estimate near `z`
  have hzW : closedBall z r ⊆ W :=
    closedBall_subset_thickening_two_mul hδ hz (mem_ball_self hr0)
  have hlip : ∀ y ∈ ball z r, ‖w y - w z‖ ≤ CZ * (B' / r + M i * r) * ‖y - z‖ := by
    intro y hy
    have h := hCZ w W hWo hsm.continuousOn B' (M i) hwB hdist y z r hr0
      (closedBall_subset_thickening_two_mul hδ hz hy) hzW
    rwa [Real.norm_eq_abs]
  have hfd : ‖fderiv ℝ w z‖ ≤ CZ * (B' / r + M i * r) :=
    norm_fderiv_le_of_lip' ℝ (by have := hM0 i; positivity)
      (Filter.mem_of_superset (ball_mem_nhds z hr0) fun y hy => hlip y hy)
  refine hfd.trans ?_
  exact Finset.single_le_sum (f := fun i => CZ * (B' / r + M i * r))
    (fun j _ => by have := hM0 j; positivity) (Finset.mem_univ i)

end SGPT.Envelopes.TosC11b
