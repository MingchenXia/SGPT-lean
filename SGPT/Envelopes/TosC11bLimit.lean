import SGPT.Envelopes.C11RealStatement
import SGPT.Foundations.Analysis.Pending.SemiconcaveTaylor

/-!
# Uniform limits with bounded chart Hessians are `C^{1,1}`

Lane TOS-C11b (`claude-tos-c11b`, node `tos-c11b:limit`).  Source: Xia, *Foundations of
pluripotential theory*, proof of `thm:kahler-real-c11-envelope` (passage to the limit in the
Hessian bounds) and the discussion before `lem:penalized-real-hessian` (a `C¹` function has locally
Lipschitz first derivatives exactly when its second derivatives are locally bounded,
`prop:bounded-hessian-taylor`).  This is the last step of SGPT `thm:Tos_C11` (Tosatti, Chu–Zhou):
the solutions of the penalized equations, or the envelopes of smoothed obstacles, have uniformly
bounded second derivatives in charts, and their uniform limit `P_ω(f)` is then `C^{1,1}` with a
controlled norm.

We avoid distributions: in a ball, functions with `‖D²g_j‖ ≤ M` satisfy the Taylor bound
`|g_j(y) - g_j(x) - Dg_j(x)(y - x)| ≤ M‖y - x‖²`; this bound passes to pointwise limits
(`differentiableAt_and_taylor_of_tendsto_ball`, the `ContDiffOn` version of TN's
`differentiableAt_and_taylor_of_tendsto`), and the Taylor bound alone makes the derivative
Lipschitz on a smaller ball (TN's `norm_fderiv_sub_le_of_taylor`) and bounded
(`norm_fderiv_le_of_taylor`).

* `isCOneOne_of_tendsto` — if `u_j → v` pointwise, `|u_j| ≤ C₀`, every `u_j` is `C²` in every chart
  and the chart Hessians `‖D²(u_j ∘ e⁻¹)‖` are bounded on every compact subset of every chart target,
  uniformly in `j`, then `v ∈ C^{1,1}(X)` (`IsCOneOne`).
* `C11ChartData.exists_cthickening_subset` — chart data admit `δ > 0` with the closed
  `δ`-thickenings of the pieces `K_i` inside the chart targets.
* `exists_c11Bound_of_tendsto` — the quantitative form for fixed chart data `D` and such a `δ`: for
  all `C₀, M` there is `C` with `‖v‖_{C^{1,1}, D} ≤ C` (`C11Bound D v C`) whenever `|u_j| ≤ C₀` and
  `‖D²(u_j ∘ e_i⁻¹)‖ ≤ M` on the closed `δ`-thickening of the pieces `K_i`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace SGPT.Envelopes.TosC11b

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.SemiconcaveHessian
open SGPT.Envelopes.C11Real

section Local

variable {n : ℕ}

/-- Points close to the centre of a ball stay in the ball. -/
theorem exists_pos_add_mem_ball {c x : ComplexModel n} {ρ : ℝ} (hx : x ∈ ball c ρ) :
    ∃ r > 0, ∀ h : ComplexModel n, ‖h‖ ≤ r → x + h ∈ ball c ρ := by
  refine ⟨(ρ - dist x c) / 2, by simp only [mem_ball] at hx; linarith, fun h hh ↦ ?_⟩
  simp only [mem_ball] at hx ⊢
  calc dist (x + h) c ≤ dist (x + h) x + dist x c := dist_triangle _ _ _
    _ = ‖h‖ + dist x c := by simp [dist_eq_norm]
    _ ≤ (ρ - dist x c) / 2 + dist x c := by linarith
    _ < ρ := by linarith

/-- **The Taylor bound passes to limits** (`ContDiffOn` version of TN's
`differentiableAt_and_taylor_of_tendsto`): if `F j` is `C²` on the ball `B(c, ρ)` with
`‖D²(F j)‖ ≤ M` and `|F j| ≤ C` there, and `F j → u` pointwise on the ball, then `u` is
differentiable on the ball with `|u y - u x - Du(x)(y - x)| ≤ M ‖y - x‖²`. -/
theorem differentiableAt_and_taylor_of_tendsto_ball {c : ComplexModel n} {ρ M C : ℝ}
    (hM0 : 0 ≤ M) {F : ℕ → ComplexModel n → ℝ} {u : ComplexModel n → ℝ}
    (hF : ∀ j, ContDiffOn ℝ 2 (F j) (ball c ρ))
    (hM : ∀ j, ∀ y ∈ ball c ρ, ‖fderiv ℝ (fderiv ℝ (F j)) y‖ ≤ M)
    (hC : ∀ j, ∀ y ∈ ball c ρ, |F j y| ≤ C)
    (hconv : ∀ y ∈ ball c ρ, Tendsto (fun j ↦ F j y) atTop (𝓝 (u y))) :
    ∀ x ∈ ball c ρ, DifferentiableAt ℝ u x ∧
      ∀ y ∈ ball c ρ, |u y - u x - fderiv ℝ u x (y - x)| ≤ M * ‖y - x‖ ^ 2 := by
  have _ : ProperSpace (ComplexModel n →L[ℝ] ℝ) := FiniteDimensional.proper ℝ _
  have hball : Convex ℝ (ball c ρ) := convex_ball c ρ
  have htaylor : ∀ j, ∀ x ∈ ball c ρ, ∀ y ∈ ball c ρ,
      |F j y - F j x - fderiv ℝ (F j) x (y - x)| ≤ M * ‖y - x‖ ^ 2 := fun j x hx y hy ↦
    abs_sub_fderiv_le_of_norm_fderiv_fderiv_le_on isOpen_ball (hF j) hball subset_rfl (hM j) hx hy
  have hkey : ∀ x ∈ ball c ρ, ∃ T : ComplexModel n →L[ℝ] ℝ,
      ∀ y ∈ ball c ρ, |u y - u x - T (y - x)| ≤ M * ‖y - x‖ ^ 2 := by
    intro x hx
    obtain ⟨r, hr, hrsub⟩ := exists_pos_add_mem_ball hx
    have hbd : ∀ j, ‖fderiv ℝ (F j) x‖ ≤ 2 * (2 * |C| + M * r ^ 2) / r := by
      intro j
      refine opNorm_le_of_le_on_ball hr (by positivity) fun h hh ↦ ?_
      have hxh : x + h ∈ ball c ρ := hrsub h hh
      have h1 := htaylor j x hx (x + h) hxh
      simp only [add_sub_cancel_left] at h1
      have h4 : M * ‖h‖ ^ 2 ≤ M * r ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hh 2) hM0
      have h2' : |F j (x + h)| ≤ |C| := le_trans (hC j _ hxh) (le_abs_self C)
      have h3' : |F j x| ≤ |C| := le_trans (hC j _ hx) (le_abs_self C)
      have := abs_le.mp h1
      have := abs_le.mp h2'
      have := abs_le.mp h3'
      rw [abs_le]
      constructor <;> linarith
    obtain ⟨T, -, φ, hφ, hT⟩ := tendsto_subseq_of_bounded
      (s := closedBall (0 : ComplexModel n →L[ℝ] ℝ) (2 * (2 * |C| + M * r ^ 2) / r))
      isBounded_closedBall (x := fun j ↦ fderiv ℝ (F j) x)
      (fun j ↦ by simpa [mem_closedBall_zero_iff] using hbd j)
    refine ⟨T, fun y hy ↦ ?_⟩
    have hlim : Tendsto (fun k ↦ F (φ k) y - F (φ k) x - fderiv ℝ (F (φ k)) x (y - x)) atTop
        (𝓝 (u y - u x - T (y - x))) := by
      refine (((hconv y hy).comp hφ.tendsto_atTop).sub
        ((hconv x hx).comp hφ.tendsto_atTop)).sub ?_
      exact ((ContinuousLinearMap.apply ℝ ℝ (y - x)).continuous.tendsto T).comp hT
    exact le_of_tendsto (hlim.abs) (Eventually.of_forall fun k ↦ htaylor (φ k) x hx y hy)
  intro x hx
  obtain ⟨T, hT⟩ := hkey x hx
  have hdiff : HasFDerivAt u T x := by
    rw [hasFDerivAt_iff_isLittleO]
    refine (Asymptotics.isLittleO_iff).2 fun {ε} hε ↦ ?_
    have hnb : ball c ρ ∈ 𝓝 x := isOpen_ball.mem_nhds hx
    have hsmall : ∀ᶠ y in 𝓝 x, ‖y - x‖ ≤ ε / (M + 1) := by
      have hcont : Tendsto (fun y : ComplexModel n ↦ ‖y - x‖) (𝓝 x) (𝓝 0) := by
        have : Continuous fun y : ComplexModel n ↦ ‖y - x‖ :=
          continuous_norm.comp (continuous_id.sub continuous_const)
        simpa using this.tendsto' x 0 (by simp)
      exact hcont.eventually_le_const (by positivity)
    filter_upwards [hnb, hsmall] with y hy hy2
    have h1 := hT y hy
    have hnn : 0 ≤ ‖y - x‖ := norm_nonneg _
    have hM1 : (0 : ℝ) < M + 1 := by linarith
    have hstep : M * ‖y - x‖ ≤ ε := by
      have h2 : M * ‖y - x‖ ≤ M * (ε / (M + 1)) := mul_le_mul_of_nonneg_left hy2 hM0
      have h3 : M * (ε / (M + 1)) ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ hM1]
        nlinarith
      linarith
    simp only [Real.norm_eq_abs]
    calc |u y - u x - T (y - x)| ≤ M * ‖y - x‖ ^ 2 := h1
      _ = (M * ‖y - x‖) * ‖y - x‖ := by ring
      _ ≤ ε * ‖y - x‖ := mul_le_mul_of_nonneg_right hstep hnn
  refine ⟨hdiff.differentiableAt, fun y hy ↦ ?_⟩
  rw [hdiff.fderiv]
  exact hT y hy

/-- **Gradient bound from the Taylor bound**: if `|u| ≤ C` on `B(x, 2r)` and the Taylor bound with
constant `M` holds at `x` on `B(x, 2r)`, then `‖Du(x)‖ ≤ 2(2C + Mr²)/r`. -/
theorem norm_fderiv_le_of_taylor {u : ComplexModel n → ℝ} {x : ComplexModel n} {r M C : ℝ}
    (hr : 0 < r) (hM0 : 0 ≤ M) (hC0 : 0 ≤ C) (hC : ∀ y ∈ ball x (2 * r), |u y| ≤ C)
    (hT : ∀ y ∈ ball x (2 * r), |u y - u x - fderiv ℝ u x (y - x)| ≤ M * ‖y - x‖ ^ 2) :
    ‖fderiv ℝ u x‖ ≤ 2 * (2 * C + M * r ^ 2) / r := by
  refine opNorm_le_of_le_on_ball hr (by positivity) fun h hh ↦ ?_
  have hxh : x + h ∈ ball x (2 * r) := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; linarith
  have hx : x ∈ ball x (2 * r) := mem_ball_self (by linarith)
  have h1 := hT (x + h) hxh
  simp only [add_sub_cancel_left] at h1
  have h4 : M * ‖h‖ ^ 2 ≤ M * r ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hh 2) hM0
  have := abs_le.mp h1
  have := abs_le.mp (hC _ hxh)
  have := abs_le.mp (hC _ hx)
  rw [abs_le]
  constructor <;> linarith

end Local

section Manifold

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]

omit [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y] in
/-- A pointwise limit of functions bounded by `C` is bounded by `C`. -/
theorem abs_le_of_tendsto {u : ℕ → Y → ℝ} {v : Y → ℝ} {C : ℝ}
    (hconv : ∀ y, Tendsto (fun j => u j y) atTop (𝓝 (v y))) (hC : ∀ j y, |u j y| ≤ C) (y : Y) :
    |v y| ≤ C :=
  le_of_tendsto ((hconv y).abs) (Eventually.of_forall fun j => hC j y)

/-- The local statement in a chart: around every point of the chart target there is a ball on which
`v ∘ e⁻¹` is differentiable with the Taylor bound, for the constant `M` of a closed ball. -/
theorem chart_taylor_of_tendsto {u : ℕ → Y → ℝ} {v : Y → ℝ} {C₀ : ℝ} (e : ComplexChart N Y)
    (hsmooth : ∀ j, ContDiffOn ℝ 2 (fun z => u j (e.val.symm z)) e.val.target)
    (hconv : ∀ y, Tendsto (fun j => u j y) atTop (𝓝 (v y))) (hC : ∀ j y, |u j y| ≤ C₀)
    {c : ComplexModel N} {ρ M : ℝ} (hM0 : 0 ≤ M) (hball : ball c ρ ⊆ e.val.target)
    (hM : ∀ j, ∀ z ∈ ball c ρ, ‖fderiv ℝ (fderiv ℝ (fun z => u j (e.val.symm z))) z‖ ≤ M) :
    ∀ x ∈ ball c ρ, DifferentiableAt ℝ (fun z => v (e.val.symm z)) x ∧
      ∀ y ∈ ball c ρ, |v (e.val.symm y) - v (e.val.symm x) -
        fderiv ℝ (fun z => v (e.val.symm z)) x (y - x)| ≤ M * ‖y - x‖ ^ 2 :=
  differentiableAt_and_taylor_of_tendsto_ball (C := C₀) hM0 (fun j => (hsmooth j).mono hball) hM
    (fun j _ _ => hC j _) (fun _ _ => hconv _)

/-- **Uniform limits with locally bounded chart Hessians are `C^{1,1}`** (FPT, proof of
`thm:kahler-real-c11-envelope`; qualitative form).  Let `u_j → v` pointwise with `|u_j| ≤ C₀`,
let every `u_j` be `C²` in every chart, and assume that for every chart `e` and every compact `K`
in its target the Hessians `‖D²(u_j ∘ e⁻¹)‖` are bounded on `K` uniformly in `j`.  Then
`v ∈ C^{1,1}(X)`. -/
theorem isCOneOne_of_tendsto {u : ℕ → Y → ℝ} {v : Y → ℝ} {C₀ : ℝ}
    (hsmooth : ∀ j (e : ComplexChart N Y),
      ContDiffOn ℝ 2 (fun z => u j (e.val.symm z)) e.val.target)
    (hconv : ∀ y, Tendsto (fun j => u j y) atTop (𝓝 (v y))) (hC : ∀ j y, |u j y| ≤ C₀)
    (hhess : ∀ (e : ComplexChart N Y) (K : Set (ComplexModel N)), IsCompact K →
      K ⊆ e.val.target → ∃ M, ∀ j, ∀ z ∈ K,
        ‖fderiv ℝ (fderiv ℝ (fun z => u j (e.val.symm z))) z‖ ≤ M) :
    IsCOneOne (N := N) v := by
  intro e
  set g : ComplexModel N → ℝ := fun z => v (e.val.symm z) with hg
  have hU : IsOpen e.val.target := e.val.open_target
  -- around every point: a ball with the Taylor bound
  have hloc : ∀ c ∈ e.val.target, ∃ ρ > 0, ∃ M ≥ 0, ball c ρ ⊆ e.val.target ∧
      ∀ x ∈ ball c ρ, DifferentiableAt ℝ g x ∧
        ∀ y ∈ ball c ρ, |g y - g x - fderiv ℝ g x (y - x)| ≤ M * ‖y - x‖ ^ 2 := by
    intro c hc
    obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp hU c hc
    have hcb : closedBall c (ρ / 2) ⊆ e.val.target :=
      (closedBall_subset_ball (half_lt_self hρ)).trans hρU
    obtain ⟨M, hM⟩ := hhess e (closedBall c (ρ / 2)) (isCompact_closedBall _ _) hcb
    refine ⟨ρ / 2, half_pos hρ, max M 0, le_max_right _ _, ball_subset_closedBall.trans hcb, ?_⟩
    exact chart_taylor_of_tendsto e (fun j => hsmooth j e) hconv hC (le_max_right _ _)
      (ball_subset_closedBall.trans hcb)
      (fun j z hz => (hM j z (ball_subset_closedBall hz)).trans (le_max_left _ _))
  -- differentiability and local Lipschitz bounds for the derivative
  have hdiff : DifferentiableOn ℝ g e.val.target := fun c hc => by
    obtain ⟨ρ, hρ, M, -, -, h⟩ := hloc c hc
    exact (h c (mem_ball_self hρ)).1.differentiableWithinAt
  have hlip : LocallyLipschitzOn e.val.target (fderiv ℝ g) := by
    intro c hc
    obtain ⟨ρ, hρ, M, hM0, -, h⟩ := hloc c hc
    refine ⟨⟨12 * M, by positivity⟩, ball c (ρ / 4),
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds c (by positivity)), ?_⟩
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have := norm_fderiv_sub_le_of_taylor hM0 (fun a ha b hb => (h a ha).2 b hb) hy hx
    rw [norm_sub_rev y x] at this
    exact this
  have hcont : ContinuousOn (fderiv ℝ g) e.val.target := hlip.continuousOn
  refine ⟨?_, fun K hK hKU => (hlip.mono hKU).exists_lipschitzOnWith_of_compact hK⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen hU]
  exact ⟨hdiff, by simp, contDiffOn_zero.mpr hcont⟩

/-- A positive number below finitely many positive numbers. -/
theorem exists_pos_le_of_fin {k : ℕ} (δ : Fin k → ℝ) (hδ : ∀ i, 0 < δ i) :
    ∃ d : ℝ, 0 < d ∧ ∀ i, d ≤ δ i := by
  have hs : 0 ≤ ∑ i, (δ i)⁻¹ := Finset.sum_nonneg fun i _ => (inv_pos.mpr (hδ i)).le
  refine ⟨(∑ i, (δ i)⁻¹ + 1)⁻¹, by positivity, fun i => ?_⟩
  rw [inv_le_comm₀ (by positivity) (hδ i)]
  have : (δ i)⁻¹ ≤ ∑ j, (δ j)⁻¹ :=
    Finset.single_le_sum (f := fun j => (δ j)⁻¹) (fun j _ => (inv_pos.mpr (hδ j)).le)
      (Finset.mem_univ i)
  linarith

/-- **A uniform thickening**: for chart data `D` there is `δ > 0` such that the closed
`δ`-thickening of every piece lies in its chart target. -/
theorem C11ChartData.exists_cthickening_subset (D : C11ChartData N Y) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, cthickening δ (D.piece i) ⊆ (D.chart i).val.target := by
  have hδi : ∀ i, ∃ δ : ℝ, 0 < δ ∧ cthickening δ (D.piece i) ⊆ (D.chart i).val.target :=
    fun i => (D.isCompact_piece i).exists_cthickening_subset_open (D.chart i).val.open_target
      (D.piece_subset i)
  choose δs hδs hδsU using hδi
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_of_fin δs hδs
  exact ⟨δ, hδ, fun i => (cthickening_mono (hδle i) _).trans (hδsU i)⟩

/-- **Quantitative `C^{1,1}` bound for limits** (FPT, proof of `thm:kahler-real-c11-envelope`).  Let
`D` be chart data and `δ > 0` with the closed `δ`-thickenings of the pieces inside the chart targets
(`C11ChartData.exists_cthickening_subset`).  For all `C₀, M ≥ 0` there is `C` such that: whenever
`u_j → v` pointwise, `|u_j| ≤ C₀`, the `u_j` are `C²` in the charts of `D` and
`‖D²(u_j ∘ e_i⁻¹)‖ ≤ M` on the `δ`-thickening of the piece `K_i`, the limit satisfies
`‖v‖_{C^{1,1}, D} ≤ C`. -/
theorem exists_c11Bound_of_tendsto (D : C11ChartData N Y) {δ : ℝ} (hδ : 0 < δ)
    (hδU : ∀ i, cthickening δ (D.piece i) ⊆ (D.chart i).val.target) (C₀ M : ℝ) (hC₀ : 0 ≤ C₀)
    (hM0 : 0 ≤ M) : ∃ C : ℝ, ∀ (u : ℕ → Y → ℝ) (v : Y → ℝ),
        (∀ j i, ContDiffOn ℝ 2 (fun z => u j ((D.chart i).val.symm z))
          (D.chart i).val.target) →
        (∀ y, Tendsto (fun j => u j y) atTop (𝓝 (v y))) → (∀ j y, |u j y| ≤ C₀) →
        (∀ j i, ∀ z ∈ cthickening δ (D.piece i),
          ‖fderiv ℝ (fderiv ℝ (fun z => u j ((D.chart i).val.symm z))) z‖ ≤ M) →
        C11Bound D v C := by
  set B₁ : ℝ := 2 * (2 * C₀ + M * (δ / 2) ^ 2) / (δ / 2) with hB₁
  have hB₁0 : 0 ≤ B₁ := by positivity
  refine ⟨C₀ + B₁ + (12 * M + 8 * B₁ / δ), fun u v hsmooth hconv hC hM => ?_⟩
  have hball : ∀ i, ∀ z ∈ D.piece i, ball z δ ⊆ cthickening δ (D.piece i) := fun i z hz =>
    (ball_subset_thickening hz δ).trans (thickening_subset_cthickening δ _)
  -- the local Taylor bound on `B(z, δ)` for `z ∈ K_i`
  have hT : ∀ i, ∀ z ∈ D.piece i, ∀ x ∈ ball z δ,
      DifferentiableAt ℝ (fun w => v ((D.chart i).val.symm w)) x ∧
        ∀ y ∈ ball z δ, |v ((D.chart i).val.symm y) - v ((D.chart i).val.symm x) -
          fderiv ℝ (fun w => v ((D.chart i).val.symm w)) x (y - x)| ≤ M * ‖y - x‖ ^ 2 :=
    fun i z hz => chart_taylor_of_tendsto (D.chart i) (fun j => hsmooth j i) hconv hC hM0
      ((hball i z hz).trans (hδU i)) (fun j w hw => hM j i w (hball i z hz hw))
  have hv : ∀ y, |v y| ≤ C₀ := abs_le_of_tendsto hconv hC
  -- gradient bound
  have hgrad : ∀ i, ∀ z ∈ D.piece i,
      ‖fderiv ℝ (fun w => v ((D.chart i).val.symm w)) z‖ ≤ B₁ := by
    intro i z hz
    have h2 : 2 * (δ / 2) = δ := by ring
    refine norm_fderiv_le_of_taylor (half_pos hδ) hM0 hC₀ (fun y _ => hv _) ?_
    rw [h2]
    exact (hT i z hz z (mem_ball_self hδ)).2
  have h8 : 0 ≤ 8 * B₁ / δ := by positivity
  refine ⟨fun y => by have := hv y; nlinarith, fun i => ⟨fun z hz => ?_, fun z hz z' hz' => ?_⟩⟩
  · have := hgrad i z hz
    linarith
  · set g : ComplexModel N → ℝ := fun w => v ((D.chart i).val.symm w)
    by_cases hzz : ‖z - z'‖ < δ / 4
    · -- close points: the Lipschitz bound of TN on `B(z, δ/4)`
      have hz1 : z ∈ ball z (δ / 4) := mem_ball_self (by positivity)
      have hz2 : z' ∈ ball z (δ / 4) := by rw [mem_ball, dist_eq_norm, norm_sub_rev]; exact hzz
      have := norm_fderiv_sub_le_of_taylor (u := g) hM0
        (fun a ha b hb => (hT i z hz a ha).2 b hb) hz2 hz1
      have h8 : 0 ≤ 8 * B₁ / δ * ‖z - z'‖ := by positivity
      calc ‖fderiv ℝ g z - fderiv ℝ g z'‖ ≤ 12 * M * ‖z' - z‖ := by
            exact this
        _ = 12 * M * ‖z - z'‖ := by rw [norm_sub_rev]
        _ ≤ (C₀ + B₁ + (12 * M + 8 * B₁ / δ)) * ‖z - z'‖ := by
            have : 0 ≤ (C₀ + B₁) * ‖z - z'‖ := by positivity
            nlinarith
    · -- distant points: the gradient bound
      push Not at hzz
      have h1 : ‖fderiv ℝ g z - fderiv ℝ g z'‖ ≤ 2 * B₁ :=
        (norm_sub_le _ _).trans (by linarith [hgrad i z hz, hgrad i z' hz'])
      have h2 : 2 * B₁ ≤ 8 * B₁ / δ * ‖z - z'‖ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
        nlinarith
      have : 0 ≤ (C₀ + B₁ + 12 * M) * ‖z - z'‖ := by positivity
      nlinarith

end Manifold

end SGPT.Envelopes.TosC11b
