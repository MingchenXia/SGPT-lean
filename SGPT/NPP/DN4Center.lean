import SGPT.NPP.DN4Curve

/-!
# The joint Levi estimate at a centre, for smooth plurisubharmonic potentials

Lane DN4 (`thm:DNT23_C11bar`, big classes; FPT `lem:chern-joint-smoothing`, Steps 2–5,
estimate `eq:chern-potential-joint-bound`).

Let `F(z, ξ)` be a smooth map, holomorphic in `ξ`, with `F(z, 0) = z` near the centre `z = 0`,
satisfying the *centre condition* `D_ξ ∂̄_v F(0, 0) = 0` (`CenterData.center`; it holds for the
fibre map read in a frame that is holomorphic to first order at the centre), with bounds
`M₀ ≥ ‖D_ξF(0, ξ)⁻¹‖`, `M₁ ≥ ‖DF(0, ξ)‖`, `M₂ ≥ ‖D²F(0, ξ)‖` on `|ξ| < r₁`.  For
`0 < |w₀| < r₁/12` and a `C²` function `p`, plurisubharmonic on `F(0, B̄(0, |w₀|))`, the Levi form
of `τ ↦ ∫ p(F(τ v, (w₀ + τ η) ζ)) χ(|ζ|²) dζ` at `τ = 0` satisfies (`leviForm_lineIntegral_ge`)

  `L ≥ -(n² · 5 K_X |w₀| |v|)² ∫ χ T - 8 n² K_R (|v|² + |v||η|) ∫ (-χ₁) T`,

`T = levTr (p ∘ F(0, w₀ ·))`, with constants `K_X`, `K_R` depending only on `M₀, M₁, M₂, r₁`.
The proof instantiates `SGPT.NPP.DN4.leviForm_integral_ge` with the curve family
`c(τ, ζ) = F(τ v, (w₀ + τ η) ζ)` and the holomorphic vector fields
`X = (w₀ D_ξF)⁻¹ ∂̄_τ c`, `R = (w₀ D_ξF)⁻¹ (∂_τ∂_τ̄ c - D(∂_τ c) X)` (`Xfield`, `Rfield`), whose
sizes follow from the Schwarz-type bounds of `SGPT.NPP.DN4Holo` and Cauchy estimates.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff

namespace SGPT.NPP.DN4

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.NPP.DN3 SGPT.Envelopes.LapClass

variable {n : ℕ}

/-- **The data of a local fibre map at a centre** (the origin), with bounds. -/
structure CenterData (F : ComplexModel n → ComplexModel n → ComplexModel n)
    (δ r₁ M₀ M₁ M₂ : ℝ) : Prop where
  δ_pos : 0 < δ
  r₁_pos : 0 < r₁
  smooth : ContDiff ℝ 3 (uncurryF F)
  holo : ∀ z ∈ ball (0 : ComplexModel n) δ, DifferentiableOn ℂ (F z) (ball 0 r₁)
  map_zero : ∀ z ∈ ball (0 : ComplexModel n) δ, F z 0 = z
  center : ∀ v : ComplexModel n, fderiv ℂ (dbarZ F v) 0 = 0
  inv : ∀ ξ ∈ ball (0 : ComplexModel n) r₁, (fderiv ℂ (F 0) ξ).IsInvertible
  inv_bound : ∀ ξ ∈ ball (0 : ComplexModel n) r₁, ‖(fderiv ℂ (F 0) ξ).inverse‖ ≤ M₀
  d1_bound : ∀ ξ ∈ ball (0 : ComplexModel n) r₁, ‖fderiv ℝ (uncurryF F) (0, ξ)‖ ≤ M₁
  d2_bound : ∀ ξ ∈ ball (0 : ComplexModel n) r₁,
    ‖fderiv ℝ (fderiv ℝ (uncurryF F)) (0, ξ)‖ ≤ M₂

/-- `X(ζ) = w₀⁻¹ D_ξF(0, w₀ζ)⁻¹ ∂̄_v F(0, w₀ ζ)`. -/
def Xfield (F : ComplexModel n → ComplexModel n → ComplexModel n) (w₀ : ℂ) (v : ComplexModel n) :
    ComplexModel n → ComplexModel n :=
  fun ζ => w₀⁻¹ • (fderiv ℂ (F 0) (w₀ • ζ)).inverse (dbarZ F v (w₀ • ζ))

/-- `R(ζ) = w₀⁻¹ D_ξF(0, w₀ζ)⁻¹ (∂_τ∂_τ̄ c - D(∂_τ c) X)(ζ)`. -/
def Rfield (F : ComplexModel n → ComplexModel n → ComplexModel n) (w₀ : ℂ) (v : ComplexModel n)
    (η : ℂ) : ComplexModel n → ComplexModel n :=
  fun ζ => w₀⁻¹ • (fderiv ℂ (F 0) (w₀ • ζ)).inverse
    (curveLevi (lineCurve F w₀ v η) ζ -
      fderiv ℂ (curveDz (lineCurve F w₀ v η)) ζ (Xfield F w₀ v ζ))

section Center

variable {F : ComplexModel n → ComplexModel n → ComplexModel n} {δ r₁ M₀ M₁ M₂ : ℝ}
  {w₀ η : ℂ} {v : ComplexModel n}

theorem lineCurve_zero (F : ComplexModel n → ComplexModel n → ComplexModel n) (w₀ : ℂ)
    (v : ComplexModel n) (η : ℂ) : lineCurve F w₀ v η 0 = fun ζ => F 0 (w₀ • ζ) := by
  funext ζ
  simp [lineCurve]

theorem smul_mem_ball_of {w₀ : ℂ} {ρ R : ℝ} (hw : ‖w₀‖ * ρ ≤ R) {ζ : ComplexModel n}
    (hζ : ζ ∈ ball (0 : ComplexModel n) ρ) : w₀ • ζ ∈ ball (0 : ComplexModel n) R ∨ w₀ = 0 := by
  by_cases h0 : w₀ = 0
  · exact Or.inr h0
  left
  rw [mem_ball, dist_zero_right] at hζ ⊢
  rw [norm_smul]
  have hw0 : 0 < ‖w₀‖ := norm_pos_iff.mpr h0
  calc ‖w₀‖ * ‖ζ‖ < ‖w₀‖ * ρ := mul_lt_mul_of_pos_left hζ hw0
    _ ≤ R := hw

/-- Points `w₀ ζ` with `|ζ| < 3` lie in `B(0, r₁/4)` when `|w₀| < r₁/12`. -/
theorem smul_mem_ball_quarter {r₁ : ℝ} (hw : ‖w₀‖ < r₁ / 12) {ζ : ComplexModel n}
    (hζ : ζ ∈ ball (0 : ComplexModel n) 3) : w₀ • ζ ∈ ball (0 : ComplexModel n) (r₁ / 4) := by
  rw [mem_ball, dist_zero_right] at hζ ⊢
  rw [norm_smul]
  have hr : 0 < r₁ := by have := norm_nonneg w₀; linarith
  calc ‖w₀‖ * ‖ζ‖ ≤ ‖w₀‖ * 3 := mul_le_mul_of_nonneg_left hζ.le (norm_nonneg _)
    _ < r₁ / 12 * 3 := by
        rcases eq_or_lt_of_le (norm_nonneg w₀) with h | h
        · rw [← h]; linarith
        · exact mul_lt_mul_of_pos_right hw (by norm_num)
    _ = r₁ / 4 := by ring

theorem norm_pair_left (u : ComplexModel n) : ‖((u, 0) : ComplexModel n × ComplexModel n)‖ = ‖u‖ := by
  simp [Prod.norm_def]

theorem norm_pair_right (u : ComplexModel n) :
    ‖(((0 : ComplexModel n), u) : ComplexModel n × ComplexModel n)‖ = ‖u‖ := by
  simp [Prod.norm_def]

theorem norm_I_smul (u : ComplexModel n) : ‖I • u‖ = ‖u‖ := by
  rw [norm_smul, Complex.norm_I, one_mul]

variable (hD : CenterData F δ r₁ M₀ M₁ M₂)
include hD

theorem CenterData.smooth2 : ContDiff ℝ 2 (uncurryF F) := hD.smooth.of_le (by norm_num)

theorem CenterData.differentiable : Differentiable ℝ (uncurryF F) :=
  hD.smooth.differentiable (by norm_num)

theorem CenterData.holo0 : DifferentiableOn ℂ (F 0) (ball 0 r₁) :=
  hD.holo 0 (mem_ball_self hD.δ_pos)

theorem CenterData.holo_fderiv : DifferentiableOn ℂ (fderiv ℂ (F 0)) (ball 0 r₁) :=
  ((contDiffOn_of_differentiableOn_complex hD.holo0 isOpen_ball).fderiv_of_isOpen isOpen_ball
    (by simp) : ContDiffOn ℂ ∞ (fderiv ℂ (F 0)) (ball 0 r₁)).differentiableOn (by simp)

theorem CenterData.M₀_nonneg : 0 ≤ M₀ :=
  (norm_nonneg _).trans (hD.inv_bound 0 (mem_ball_self hD.r₁_pos))

theorem CenterData.M₁_nonneg : 0 ≤ M₁ :=
  (norm_nonneg _).trans (hD.d1_bound 0 (mem_ball_self hD.r₁_pos))

theorem CenterData.M₂_nonneg : 0 ≤ M₂ :=
  (norm_nonneg (fderiv ℝ (fderiv ℝ (uncurryF F)) ((0 : ComplexModel n), (0 : ComplexModel n)))).trans
    (hD.d2_bound 0 (mem_ball_self hD.r₁_pos))

theorem CenterData.norm_partial_left_le {ξ : ComplexModel n} (hξ : ξ ∈ ball (0 : ComplexModel n) r₁)
    (u : ComplexModel n) : ‖fderiv ℝ (fun z => F z ξ) 0 u‖ ≤ M₁ * ‖u‖ := by
  rw [fderiv_partial_left hD.differentiable]
  calc ‖fderiv ℝ (uncurryF F) (0, ξ) (u, 0)‖ ≤ ‖fderiv ℝ (uncurryF F) (0, ξ)‖ * ‖((u, 0) :
        ComplexModel n × ComplexModel n)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ M₁ * ‖u‖ := by
        rw [norm_pair_left]
        exact mul_le_mul_of_nonneg_right (hD.d1_bound ξ hξ) (norm_nonneg _)

theorem CenterData.norm_dbarZ_le {ξ : ComplexModel n} (hξ : ξ ∈ ball (0 : ComplexModel n) r₁)
    (v : ComplexModel n) : ‖dbarZ F v ξ‖ ≤ M₁ * ‖v‖ := by
  rw [dbarZ, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
  have h1 := hD.norm_partial_left_le hξ v
  have h2 := hD.norm_partial_left_le hξ (I • v)
  rw [norm_I_smul] at h2
  calc 2⁻¹ * ‖fderiv ℝ (fun z => F z ξ) 0 v + I • fderiv ℝ (fun z => F z ξ) 0 (I • v)‖
      ≤ 2⁻¹ * (‖fderiv ℝ (fun z => F z ξ) 0 v‖ + ‖fderiv ℝ (fun z => F z ξ) 0 (I • v)‖) := by
        gcongr
        exact (norm_add_le _ _).trans (by rw [norm_I_smul])
    _ ≤ M₁ * ‖v‖ := by linarith

theorem CenterData.norm_dZ_le {ξ : ComplexModel n} (hξ : ξ ∈ ball (0 : ComplexModel n) r₁)
    (v : ComplexModel n) : ‖dZ F v ξ‖ ≤ M₁ * ‖v‖ := by
  rw [dZ, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
  have h1 := hD.norm_partial_left_le hξ v
  have h2 := hD.norm_partial_left_le hξ (I • v)
  rw [norm_I_smul] at h2
  calc 2⁻¹ * ‖fderiv ℝ (fun z => F z ξ) 0 v - I • fderiv ℝ (fun z => F z ξ) 0 (I • v)‖
      ≤ 2⁻¹ * (‖fderiv ℝ (fun z => F z ξ) 0 v‖ + ‖fderiv ℝ (fun z => F z ξ) 0 (I • v)‖) := by
        gcongr
        exact (norm_sub_le _ _).trans (by rw [norm_I_smul])
    _ ≤ M₁ * ‖v‖ := by linarith

theorem CenterData.norm_fderiv_F0_le {ξ : ComplexModel n} (hξ : ξ ∈ ball (0 : ComplexModel n) r₁) :
    ‖fderiv ℂ (F 0) ξ‖ ≤ M₁ := by
  have hd : DifferentiableAt ℂ (F 0) ξ := hD.holo0.differentiableAt (isOpen_ball.mem_nhds hξ)
  have hR : (fderiv ℂ (F 0) ξ).restrictScalars ℝ = fderiv ℝ (F 0) ξ :=
    (hd.hasFDerivAt.restrictScalars ℝ).fderiv.symm
  rw [← ContinuousLinearMap.norm_restrictScalars (𝕜' := ℝ), hR]
  refine ContinuousLinearMap.opNorm_le_bound _ hD.M₁_nonneg fun e => ?_
  rw [fderiv_partial_right hD.differentiable]
  calc ‖fderiv ℝ (uncurryF F) (0, ξ) (0, e)‖ ≤ ‖fderiv ℝ (uncurryF F) (0, ξ)‖ * ‖(((0 : ComplexModel n), e) :
        ComplexModel n × ComplexModel n)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ M₁ * ‖e‖ := by
        rw [norm_pair_right]
        exact mul_le_mul_of_nonneg_right (hD.d1_bound ξ hξ) (norm_nonneg _)

theorem CenterData.norm_levZ_le {ξ : ComplexModel n} (hξ : ξ ∈ ball (0 : ComplexModel n) r₁)
    (v : ComplexModel n) : ‖levZ F v ξ‖ ≤ M₂ * ‖v‖ ^ 2 / 2 := by
  have hterm : ∀ u : ComplexModel n,
      ‖fderiv ℝ (fderiv ℝ (uncurryF F)) (0, ξ) (u, 0) (u, 0)‖ ≤ M₂ * ‖u‖ ^ 2 := by
    intro u
    calc _ ≤ ‖fderiv ℝ (fderiv ℝ (uncurryF F)) (0, ξ)‖ * ‖((u, 0) : ComplexModel n × ComplexModel n)‖ *
          ‖((u, 0) : ComplexModel n × ComplexModel n)‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ M₂ * ‖u‖ ^ 2 := by
          rw [norm_pair_left, mul_assoc, ← sq]
          exact mul_le_mul_of_nonneg_right (hD.d2_bound ξ hξ) (sq_nonneg _)
  rw [levZ, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 4⁻¹)]
  have h1 := hterm v
  have h2 := hterm (I • v)
  rw [norm_I_smul] at h2
  have h3 := norm_add_le (fderiv ℝ (fderiv ℝ (uncurryF F)) (0, ξ) (v, 0) (v, 0))
    (fderiv ℝ (fderiv ℝ (uncurryF F)) (0, ξ) (I • v, 0) (I • v, 0))
  nlinarith

/-! ### Schwarz-type bounds of the coefficient functions -/

theorem CenterData.norm_dbarZ_le_sq (v : ComplexModel n) {ξ : ComplexModel n}
    (hξ : ξ ∈ ball (0 : ComplexModel n) (r₁ / 4)) :
    ‖dbarZ F v ξ‖ ≤ 32 * (M₁ * ‖v‖) / r₁ ^ 2 * ‖ξ‖ ^ 2 :=
  norm_le_sq_of_vanishing hD.r₁_pos (differentiableOn_dbarZ hD.smooth2 hD.holo hD.δ_pos v)
    (fun _ hξ' => hD.norm_dbarZ_le hξ' v) (dbarZ_zero hD.map_zero hD.δ_pos v) (hD.center v) hξ

theorem CenterData.norm_fderiv_dbarZ_le (v : ComplexModel n) {ξ : ComplexModel n}
    (hξ : ξ ∈ ball (0 : ComplexModel n) (r₁ / 4)) :
    ‖fderiv ℂ (dbarZ F v) ξ‖ ≤ 32 * (M₁ * ‖v‖) / r₁ ^ 2 * ‖ξ‖ :=
  norm_fderiv_le_of_vanishing hD.r₁_pos (differentiableOn_dbarZ hD.smooth2 hD.holo hD.δ_pos v)
    (fun _ hξ' => hD.norm_dbarZ_le hξ' v) (hD.center v) hξ

theorem CenterData.norm_levZ_le_lin (v : ComplexModel n) {ξ : ComplexModel n}
    (hξ : ξ ∈ ball (0 : ComplexModel n) (r₁ / 2)) :
    ‖levZ F v ξ‖ ≤ 4 * (M₂ * ‖v‖ ^ 2 / 2) / r₁ * ‖ξ‖ :=
  norm_le_of_vanishing hD.r₁_pos (differentiableOn_levZ hD.smooth hD.holo hD.δ_pos v)
    (fun _ hξ' => hD.norm_levZ_le hξ' v) (levZ_zero hD.smooth2 hD.map_zero hD.δ_pos v) hξ

/-! ### The curve family on the ball `B(0, 3)` -/

variable (hw : ‖w₀‖ < r₁ / 12) (hw0 : w₀ ≠ 0)
include hw

theorem CenterData.mem_ball_r₁ {ζ : ComplexModel n} (hζ : ζ ∈ ball (0 : ComplexModel n) 3) :
    w₀ • ζ ∈ ball (0 : ComplexModel n) r₁ :=
  ball_subset_ball (by linarith [hD.r₁_pos]) (smul_mem_ball_quarter hw hζ)

theorem CenterData.differentiableAt_F0 {ζ : ComplexModel n}
    (hζ : ζ ∈ ball (0 : ComplexModel n) 3) : DifferentiableAt ℂ (F 0) (w₀ • ζ) :=
  hD.holo0.differentiableAt (isOpen_ball.mem_nhds (hD.mem_ball_r₁ hw hζ))

theorem CenterData.differentiableOn_comp_smul {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℂ G] {g : ComplexModel n → G}
    (hg : DifferentiableOn ℂ g (ball 0 r₁)) :
    DifferentiableOn ℂ (fun ζ => g (w₀ • ζ)) (ball (0 : ComplexModel n) 3) :=
  hg.comp ((differentiable_id.const_smul w₀).differentiableOn) fun _ hζ => hD.mem_ball_r₁ hw hζ

theorem CenterData.differentiableOn_lineCurve_zero :
    DifferentiableOn ℂ (lineCurve F w₀ v η 0) (ball (0 : ComplexModel n) 3) := by
  rw [lineCurve_zero]
  exact hD.differentiableOn_comp_smul hw hD.holo0

theorem CenterData.fderiv_lineCurve_zero {ζ : ComplexModel n}
    (hζ : ζ ∈ ball (0 : ComplexModel n) 3) :
    fderiv ℂ (lineCurve F w₀ v η 0) ζ = w₀ • fderiv ℂ (F 0) (w₀ • ζ) := by
  rw [lineCurve_zero]
  have h : HasFDerivAt (fun ζ : ComplexModel n => F 0 (w₀ • ζ))
      ((fderiv ℂ (F 0) (w₀ • ζ)).comp (w₀ • ContinuousLinearMap.id ℂ (ComplexModel n))) ζ :=
    (hD.differentiableAt_F0 hw hζ).hasFDerivAt.comp ζ ((hasFDerivAt_id ζ).const_smul w₀)
  rw [h.fderiv]
  ext1 u
  simp

theorem CenterData.curveDzbar_eq {ζ : ComplexModel n} (hζ : ζ ∈ ball (0 : ComplexModel n) 3) :
    curveDzbar (lineCurve F w₀ v η) ζ = dbarZ F v (w₀ • ζ) :=
  curveDzbar_lineCurve hD.differentiable (hD.differentiableAt_F0 hw hζ)

theorem CenterData.curveDz_eq {ζ : ComplexModel n} (hζ : ζ ∈ ball (0 : ComplexModel n) 3) :
    curveDz (lineCurve F w₀ v η) ζ = dZ F v (w₀ • ζ) + η • fderiv ℂ (F 0) (w₀ • ζ) ζ :=
  curveDz_lineCurve hD.differentiable (hD.differentiableAt_F0 hw hζ)

theorem CenterData.curveLevi_eq {ζ : ComplexModel n} (hζ : ζ ∈ ball (0 : ComplexModel n) 3) :
    curveLevi (lineCurve F w₀ v η) ζ =
      levZ F v (w₀ • ζ) + fderiv ℂ (dbarZ F v) (w₀ • ζ) (η • ζ) := by
  have hξ := hD.mem_ball_r₁ hw hζ
  have h2 : ContDiffAt ℂ 2 (F 0) (w₀ • ζ) :=
    (contDiffAt_of_differentiableOn_complex hD.holo0 isOpen_ball hξ).of_le (by norm_cast)
  rw [curveLevi_lineCurve hD.smooth2 h2, mixZ_eq_fderiv hD.smooth2 hD.holo hD.δ_pos v hξ]

theorem CenterData.differentiableOn_curveDz :
    DifferentiableOn ℂ (curveDz (lineCurve F w₀ v η)) (ball (0 : ComplexModel n) 3) := by
  have h1 := hD.differentiableOn_comp_smul hw (differentiableOn_dZ hD.smooth2 hD.holo hD.δ_pos v)
  have h2 : DifferentiableOn ℂ (fun ζ : ComplexModel n => fderiv ℂ (F 0) (w₀ • ζ) ζ)
      (ball (0 : ComplexModel n) 3) :=
    (hD.differentiableOn_comp_smul hw hD.holo_fderiv).clm_apply differentiableOn_id
  exact (h1.add (h2.const_smul η)).congr fun ζ hζ => hD.curveDz_eq hw hζ

theorem CenterData.differentiableOn_curveLevi :
    DifferentiableOn ℂ (curveLevi (lineCurve F w₀ v η)) (ball (0 : ComplexModel n) 3) := by
  have h1 := hD.differentiableOn_comp_smul hw (differentiableOn_levZ hD.smooth hD.holo hD.δ_pos v)
  have hDb : DifferentiableOn ℂ (fderiv ℂ (dbarZ F v)) (ball 0 r₁) :=
    ((contDiffOn_of_differentiableOn_complex (differentiableOn_dbarZ hD.smooth2 hD.holo
      hD.δ_pos v) isOpen_ball).fderiv_of_isOpen isOpen_ball (by simp) :
      ContDiffOn ℂ ∞ (fderiv ℂ (dbarZ F v)) (ball 0 r₁)).differentiableOn (by simp)
  have h2 : DifferentiableOn ℂ (fun ζ : ComplexModel n => fderiv ℂ (dbarZ F v) (w₀ • ζ) (η • ζ))
      (ball (0 : ComplexModel n) 3) :=
    (hD.differentiableOn_comp_smul hw hDb).clm_apply (differentiableOn_id.const_smul η)
  exact (h1.add h2).congr fun ζ hζ => hD.curveLevi_eq hw hζ

theorem CenterData.differentiableOn_inverse :
    DifferentiableOn ℂ (fun ζ : ComplexModel n => (fderiv ℂ (F 0) (w₀ • ζ)).inverse)
      (ball (0 : ComplexModel n) 3) := by
  intro ζ hζ
  have hξ := hD.mem_ball_r₁ hw hζ
  obtain ⟨e, he⟩ := hD.inv _ hξ
  have hinv : DifferentiableAt ℂ ContinuousLinearMap.inverse (fderiv ℂ (F 0) (w₀ • ζ)) := by
    rw [← he]
    exact (contDiffAt_map_inverse (n := 1) e).differentiableAt (by norm_num)
  have hA : DifferentiableAt ℂ (fun ζ : ComplexModel n => fderiv ℂ (F 0) (w₀ • ζ)) ζ :=
    (hD.differentiableOn_comp_smul hw hD.holo_fderiv).differentiableAt
      (isOpen_ball.mem_nhds hζ)
  exact (hinv.comp ζ hA).differentiableWithinAt

theorem CenterData.differentiableOn_Xfield :
    DifferentiableOn ℂ (Xfield F w₀ v) (ball (0 : ComplexModel n) 3) := by
  have h1 := hD.differentiableOn_comp_smul hw (differentiableOn_dbarZ hD.smooth2 hD.holo hD.δ_pos v)
  exact ((hD.differentiableOn_inverse hw).clm_apply h1).const_smul w₀⁻¹

theorem CenterData.differentiableOn_fderiv_curveDz :
    DifferentiableOn ℂ (fderiv ℂ (curveDz (lineCurve F w₀ v η))) (ball (0 : ComplexModel n) 3) :=
  ((contDiffOn_of_differentiableOn_complex (hD.differentiableOn_curveDz (η := η) hw)
    isOpen_ball).fderiv_of_isOpen isOpen_ball (by simp) :
    ContDiffOn ℂ ∞ (fderiv ℂ (curveDz (lineCurve F w₀ v η))) _).differentiableOn (by simp)

theorem CenterData.differentiableOn_Rfield :
    DifferentiableOn ℂ (Rfield F w₀ v η) (ball (0 : ComplexModel n) 3) := by
  have h1 := (hD.differentiableOn_curveLevi (v := v) (η := η) hw).sub
    ((hD.differentiableOn_fderiv_curveDz (v := v) (η := η) hw).clm_apply
      (hD.differentiableOn_Xfield (v := v) hw))
  exact ((hD.differentiableOn_inverse hw).clm_apply h1).const_smul w₀⁻¹

theorem CenterData.Xfield_zero : Xfield F w₀ v 0 = 0 := by
  simp [Xfield, dbarZ_zero hD.map_zero hD.δ_pos v]

theorem CenterData.Rfield_zero : Rfield F w₀ v η 0 = 0 := by
  have h0 : (0 : ComplexModel n) ∈ ball (0 : ComplexModel n) 3 := mem_ball_self (by norm_num)
  simp [Rfield, hD.curveLevi_eq hw h0, levZ_zero hD.smooth2 hD.map_zero hD.δ_pos v,
    hD.Xfield_zero hw]

include hw0

theorem CenterData.fderiv_apply_Xfield {ζ : ComplexModel n} (hζ : ζ ∈ ball (0 : ComplexModel n) 3) :
    fderiv ℂ (lineCurve F w₀ v η 0) ζ (Xfield F w₀ v ζ) = curveDzbar (lineCurve F w₀ v η) ζ := by
  rw [hD.fderiv_lineCurve_zero hw hζ, hD.curveDzbar_eq hw hζ]
  obtain ⟨e, he⟩ := hD.inv _ (hD.mem_ball_r₁ hw hζ)
  simp only [Xfield, ← he, ContinuousLinearMap.inverse_equiv, smul_apply,
    map_smul, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply, smul_smul,
    inv_mul_cancel₀ hw0, one_smul]

theorem CenterData.fderiv_apply_Rfield {ζ : ComplexModel n} (hζ : ζ ∈ ball (0 : ComplexModel n) 3) :
    fderiv ℂ (lineCurve F w₀ v η 0) ζ (Rfield F w₀ v η ζ) =
      curveLevi (lineCurve F w₀ v η) ζ -
        fderiv ℂ (curveDz (lineCurve F w₀ v η)) ζ (Xfield F w₀ v ζ) := by
  rw [hD.fderiv_lineCurve_zero hw hζ]
  obtain ⟨e, he⟩ := hD.inv _ (hD.mem_ball_r₁ hw hζ)
  simp only [Rfield, ← he, ContinuousLinearMap.inverse_equiv, smul_apply,
    map_smul, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply, smul_smul,
    inv_mul_cancel₀ hw0, one_smul]

/-! ### Sizes -/

theorem CenterData.norm_Xfield_le {ρ : ℝ} (hρ : ρ ≤ 3) {ζ : ComplexModel n}
    (hζ : ζ ∈ ball (0 : ComplexModel n) ρ) :
    ‖Xfield F w₀ v ζ‖ ≤ 32 * M₀ * M₁ / r₁ ^ 2 * ρ ^ 2 * ‖w₀‖ * ‖v‖ := by
  have hζ3 : ζ ∈ ball (0 : ComplexModel n) 3 := ball_subset_ball hρ hζ
  have hξ := smul_mem_ball_quarter hw hζ3
  have hb := hD.norm_dbarZ_le_sq v hξ
  have hinv := hD.inv_bound _ (hD.mem_ball_r₁ hw hζ3)
  have hw0' : 0 < ‖w₀‖ := norm_pos_iff.mpr hw0
  have hnξ : ‖w₀ • ζ‖ ≤ ‖w₀‖ * ρ := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hζ).le (norm_nonneg _)
  have hρ0 : 0 ≤ ρ := by
    have := mem_ball_zero_iff.mp hζ; linarith [norm_nonneg ζ]
  have hK0 : 0 ≤ 32 * (M₁ * ‖v‖) / r₁ ^ 2 :=
    div_nonneg (mul_nonneg (by norm_num) (mul_nonneg hD.M₁_nonneg (norm_nonneg _)))
      (sq_nonneg _)
  have hb' : ‖dbarZ F v (w₀ • ζ)‖ ≤ 32 * (M₁ * ‖v‖) / r₁ ^ 2 * (‖w₀‖ * ρ) ^ 2 :=
    hb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnξ 2) hK0)
  have hinvapp : ‖(fderiv ℂ (F 0) (w₀ • ζ)).inverse (dbarZ F v (w₀ • ζ))‖ ≤
      M₀ * (32 * (M₁ * ‖v‖) / r₁ ^ 2 * (‖w₀‖ * ρ) ^ 2) :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul hinv hb' (norm_nonneg _) hD.M₀_nonneg)
  calc ‖Xfield F w₀ v ζ‖ = ‖w₀‖⁻¹ * ‖(fderiv ℂ (F 0) (w₀ • ζ)).inverse (dbarZ F v (w₀ • ζ))‖ := by
        rw [Xfield, norm_smul, norm_inv]
    _ ≤ ‖w₀‖⁻¹ * (M₀ * (32 * (M₁ * ‖v‖) / r₁ ^ 2 * (‖w₀‖ * ρ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hinvapp (inv_nonneg.mpr (norm_nonneg _))
    _ = 32 * M₀ * M₁ / r₁ ^ 2 * ρ ^ 2 * ‖w₀‖ * ‖v‖ := by
        field_simp

omit hw0 in
theorem CenterData.norm_curveDz_le {ζ : ComplexModel n} (hζ : ζ ∈ ball (0 : ComplexModel n) 3) :
    ‖curveDz (lineCurve F w₀ v η) ζ‖ ≤ M₁ * ‖v‖ + 3 * M₁ * ‖η‖ := by
  rw [hD.curveDz_eq hw hζ]
  have hξ := hD.mem_ball_r₁ hw hζ
  have h1 := hD.norm_dZ_le hξ v
  have h2 : ‖η • fderiv ℂ (F 0) (w₀ • ζ) ζ‖ ≤ 3 * M₁ * ‖η‖ := by
    rw [norm_smul]
    have h3 := (ContinuousLinearMap.le_opNorm (fderiv ℂ (F 0) (w₀ • ζ)) ζ).trans
      (mul_le_mul (hD.norm_fderiv_F0_le hξ) (mem_ball_zero_iff.mp hζ).le (norm_nonneg _)
        hD.M₁_nonneg)
    nlinarith [norm_nonneg η]
  exact (norm_add_le _ _).trans (by linarith)

omit hw0 in
theorem CenterData.norm_curveLevi_le {ζ : ComplexModel n} (hζ : ζ ∈ ball (0 : ComplexModel n) 2) :
    ‖curveLevi (lineCurve F w₀ v η) ζ‖ ≤
      4 * M₂ * ‖v‖ ^ 2 / r₁ * ‖w₀‖ + 128 * M₁ * ‖v‖ / r₁ ^ 2 * ‖w₀‖ * ‖η‖ := by
  have hζ3 : ζ ∈ ball (0 : ComplexModel n) 3 := ball_subset_ball (by norm_num) hζ
  rw [hD.curveLevi_eq hw hζ3]
  have hξ := smul_mem_ball_quarter hw hζ3
  have hξ2 : w₀ • ζ ∈ ball (0 : ComplexModel n) (r₁ / 2) :=
    ball_subset_ball (by linarith [hD.r₁_pos]) hξ
  have hnξ : ‖w₀ • ζ‖ ≤ 2 * ‖w₀‖ := by
    rw [norm_smul]
    nlinarith [(mem_ball_zero_iff.mp hζ).le, norm_nonneg w₀]
  have hζn : ‖ζ‖ ≤ 2 := (mem_ball_zero_iff.mp hζ).le
  have hr : 0 < r₁ := hD.r₁_pos
  have h1 : ‖levZ F v (w₀ • ζ)‖ ≤ 4 * M₂ * ‖v‖ ^ 2 / r₁ * ‖w₀‖ := by
    refine (hD.norm_levZ_le_lin v hξ2).trans ?_
    have hc : 0 ≤ 4 * (M₂ * ‖v‖ ^ 2 / 2) / r₁ :=
      div_nonneg (mul_nonneg (by norm_num) (div_nonneg (mul_nonneg hD.M₂_nonneg (sq_nonneg _))
        (by norm_num))) hr.le
    calc 4 * (M₂ * ‖v‖ ^ 2 / 2) / r₁ * ‖w₀ • ζ‖ ≤ 4 * (M₂ * ‖v‖ ^ 2 / 2) / r₁ * (2 * ‖w₀‖) :=
          mul_le_mul_of_nonneg_left hnξ hc
      _ = 4 * M₂ * ‖v‖ ^ 2 / r₁ * ‖w₀‖ := by ring
  have h2 : ‖fderiv ℂ (dbarZ F v) (w₀ • ζ) (η • ζ)‖ ≤ 128 * M₁ * ‖v‖ / r₁ ^ 2 * ‖w₀‖ * ‖η‖ := by
    have hc : 0 ≤ 32 * (M₁ * ‖v‖) / r₁ ^ 2 :=
      div_nonneg (mul_nonneg (by norm_num) (mul_nonneg hD.M₁_nonneg (norm_nonneg _)))
        (sq_nonneg _)
    have hD1 := hD.norm_fderiv_dbarZ_le v hξ
    have hD2 : ‖fderiv ℂ (dbarZ F v) (w₀ • ζ)‖ ≤ 32 * (M₁ * ‖v‖) / r₁ ^ 2 * (2 * ‖w₀‖) :=
      hD1.trans (mul_le_mul_of_nonneg_left hnξ hc)
    have hηζ : ‖η • ζ‖ ≤ 2 * ‖η‖ := by
      rw [norm_smul]; nlinarith [norm_nonneg η]
    calc ‖fderiv ℂ (dbarZ F v) (w₀ • ζ) (η • ζ)‖ ≤ ‖fderiv ℂ (dbarZ F v) (w₀ • ζ)‖ * ‖η • ζ‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (32 * (M₁ * ‖v‖) / r₁ ^ 2 * (2 * ‖w₀‖)) * (2 * ‖η‖) :=
          mul_le_mul hD2 hηζ (norm_nonneg _) (mul_nonneg hc (by positivity))
      _ = 128 * M₁ * ‖v‖ / r₁ ^ 2 * ‖w₀‖ * ‖η‖ := by ring
  exact (norm_add_le _ _).trans (by linarith)

omit hD hw hw0 in
/-- The Cauchy estimate on a unit ball inside a larger ball. -/
theorem norm_fderiv_le_cauchy {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {f : ComplexModel n → G} {ζ : ComplexModel n} {R C r : ℝ}
    (hf : DifferentiableOn ℂ f (ball ζ R)) (hC : ∀ w ∈ ball ζ R, ‖f w‖ ≤ C) (hr : 0 < r)
    (hrR : r < R) : ‖fderiv ℂ f ζ‖ ≤ C / r :=
  norm_fderiv_le_of_forall_norm_le hf hC hr hrR

omit hw0 in
theorem CenterData.norm_fderiv_curveDz_le {ζ : ComplexModel n}
    (hζ : ζ ∈ ball (0 : ComplexModel n) 2) :
    ‖fderiv ℂ (curveDz (lineCurve F w₀ v η)) ζ‖ ≤ 2 * (M₁ * ‖v‖ + 3 * M₁ * ‖η‖) := by
  have hsub : ball ζ 1 ⊆ ball (0 : ComplexModel n) 3 := by
    refine ball_subset_ball' ?_
    rw [dist_zero_right]; linarith [mem_ball_zero_iff.mp hζ]
  have h := norm_fderiv_le_cauchy ((hD.differentiableOn_curveDz (v := v) (η := η) hw).mono hsub)
    (fun w hw' => hD.norm_curveDz_le hw (hsub hw')) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  calc _ ≤ (M₁ * ‖v‖ + 3 * M₁ * ‖η‖) / (1 / 2) := h
    _ = 2 * (M₁ * ‖v‖ + 3 * M₁ * ‖η‖) := by ring

/-- The constant of the `R`-field. -/
def KR (M₀ M₁ M₂ r₁ : ℝ) : ℝ := M₀ * (4 * M₂ / r₁ + 128 * M₁ / r₁ ^ 2 + 768 * M₀ * M₁ ^ 2 / r₁ ^ 2)

theorem CenterData.norm_Rfield_le {ζ : ComplexModel n} (hζ : ζ ∈ ball (0 : ComplexModel n) 2) :
    ‖Rfield F w₀ v η ζ‖ ≤ KR M₀ M₁ M₂ r₁ * (‖v‖ ^ 2 + ‖v‖ * ‖η‖) := by
  have hζ3 : ζ ∈ ball (0 : ComplexModel n) 3 := ball_subset_ball (by norm_num) hζ
  have hinv := hD.inv_bound _ (hD.mem_ball_r₁ hw hζ3)
  have hw0' : 0 < ‖w₀‖ := norm_pos_iff.mpr hw0
  have hQ := hD.norm_curveLevi_le (v := v) (η := η) hw hζ
  have hDY := hD.norm_fderiv_curveDz_le (v := v) (η := η) hw hζ
  have hX := hD.norm_Xfield_le (v := v) hw hw0 (by norm_num : (2 : ℝ) ≤ 3) hζ
  have hr : 0 < r₁ := hD.r₁_pos
  have hM₀ := hD.M₀_nonneg
  have hM₁ := hD.M₁_nonneg
  have hM₂ := hD.M₂_nonneg
  set a := ‖v‖
  set b := ‖η‖
  set t := ‖w₀‖
  have hDYX : ‖fderiv ℂ (curveDz (lineCurve F w₀ v η)) ζ (Xfield F w₀ v ζ)‖ ≤
      2 * (M₁ * a + 3 * M₁ * b) * (32 * M₀ * M₁ / r₁ ^ 2 * 2 ^ 2 * t * a) :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hDY hX (norm_nonneg _) (by positivity))
  have hsum : ‖curveLevi (lineCurve F w₀ v η) ζ -
      fderiv ℂ (curveDz (lineCurve F w₀ v η)) ζ (Xfield F w₀ v ζ)‖ ≤
      t * ((4 * M₂ / r₁ + 256 * M₀ * M₁ ^ 2 / r₁ ^ 2) * a ^ 2 +
        (128 * M₁ / r₁ ^ 2 + 768 * M₀ * M₁ ^ 2 / r₁ ^ 2) * (a * b)) := by
    refine (norm_sub_le _ _).trans ?_
    have e : t * ((4 * M₂ / r₁ + 256 * M₀ * M₁ ^ 2 / r₁ ^ 2) * a ^ 2 +
        (128 * M₁ / r₁ ^ 2 + 768 * M₀ * M₁ ^ 2 / r₁ ^ 2) * (a * b)) =
        (4 * M₂ * a ^ 2 / r₁ * t + 128 * M₁ * a / r₁ ^ 2 * t * b) +
          2 * (M₁ * a + 3 * M₁ * b) * (32 * M₀ * M₁ / r₁ ^ 2 * 2 ^ 2 * t * a) := by
      field_simp; ring
    rw [e]
    exact add_le_add hQ hDYX
  have hRn : ‖Rfield F w₀ v η ζ‖ ≤ t⁻¹ * (M₀ * (t * ((4 * M₂ / r₁ + 256 * M₀ * M₁ ^ 2 / r₁ ^ 2) *
      a ^ 2 + (128 * M₁ / r₁ ^ 2 + 768 * M₀ * M₁ ^ 2 / r₁ ^ 2) * (a * b)))) := by
    rw [Rfield, norm_smul, norm_inv]
    exact mul_le_mul_of_nonneg_left ((ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul hinv hsum (norm_nonneg _) hM₀)) (inv_nonneg.mpr hw0'.le)
  have hcancel : t⁻¹ * (M₀ * (t * ((4 * M₂ / r₁ + 256 * M₀ * M₁ ^ 2 / r₁ ^ 2) * a ^ 2 +
      (128 * M₁ / r₁ ^ 2 + 768 * M₀ * M₁ ^ 2 / r₁ ^ 2) * (a * b)))) =
      M₀ * ((4 * M₂ / r₁ + 256 * M₀ * M₁ ^ 2 / r₁ ^ 2) * a ^ 2 +
        (128 * M₁ / r₁ ^ 2 + 768 * M₀ * M₁ ^ 2 / r₁ ^ 2) * (a * b)) := by
    field_simp
  rw [hcancel] at hRn
  refine hRn.trans ?_
  rw [KR, ← sub_nonneg]
  have e2 : M₀ * (4 * M₂ / r₁ + 128 * M₁ / r₁ ^ 2 + 768 * M₀ * M₁ ^ 2 / r₁ ^ 2) * (a ^ 2 + a * b) -
      M₀ * ((4 * M₂ / r₁ + 256 * M₀ * M₁ ^ 2 / r₁ ^ 2) * a ^ 2 +
        (128 * M₁ / r₁ ^ 2 + 768 * M₀ * M₁ ^ 2 / r₁ ^ 2) * (a * b)) =
      M₀ * (128 * M₁ / r₁ ^ 2 * a ^ 2 + 512 * M₀ * M₁ ^ 2 / r₁ ^ 2 * a ^ 2 +
        4 * M₂ / r₁ * (a * b)) := by ring
  rw [e2]
  positivity

/-! ### Cauchy estimates for the components -/

theorem CenterData.norm_fderiv_Xcoord_le (m : Fin n) {ζ : ComplexModel n}
    (hζ : ζ ∈ closedBall (0 : ComplexModel n) 1) :
    ‖fderiv ℂ (fun s => Xfield F w₀ v s m) ζ‖ ≤ 288 * M₀ * M₁ / r₁ ^ 2 * ‖w₀‖ * ‖v‖ := by
  have hζ1 : ‖ζ‖ ≤ 1 := mem_closedBall_zero_iff.mp hζ
  have hsub : ball ζ 2 ⊆ ball (0 : ComplexModel n) 3 :=
    ball_subset_ball' (by rw [dist_zero_right]; linarith)
  have hXm := (differentiableOn_coord (hD.differentiableOn_Xfield (v := v) hw) m).mono hsub
  have h := norm_fderiv_le_cauchy hXm (fun w hw' => (PiLp.norm_apply_le _ m).trans
    (hD.norm_Xfield_le hw hw0 le_rfl (hsub hw'))) one_pos (by norm_num)
  calc _ ≤ 32 * M₀ * M₁ / r₁ ^ 2 * 3 ^ 2 * ‖w₀‖ * ‖v‖ / 1 := h
    _ = 288 * M₀ * M₁ / r₁ ^ 2 * ‖w₀‖ * ‖v‖ := by ring

theorem CenterData.norm_fderiv2_Xcoord_le (m : Fin n) {ζ : ComplexModel n}
    (hζ : ζ ∈ closedBall (0 : ComplexModel n) 1) :
    ‖fderiv ℂ (fderiv ℂ (fun s => Xfield F w₀ v s m)) ζ‖ ≤
      4 * (288 * M₀ * M₁ / r₁ ^ 2 * ‖w₀‖ * ‖v‖) := by
  have hζ1 : ‖ζ‖ ≤ 1 := mem_closedBall_zero_iff.mp hζ
  set CX := 32 * M₀ * M₁ / r₁ ^ 2 * 3 ^ 2 * ‖w₀‖ * ‖v‖ with hCX
  have hXm : DifferentiableOn ℂ (fun s => Xfield F w₀ v s m) (ball (0 : ComplexModel n) 3) :=
    differentiableOn_coord (hD.differentiableOn_Xfield (v := v) hw) m
  have hDXm : DifferentiableOn ℂ (fderiv ℂ (fun s => Xfield F w₀ v s m))
      (ball (0 : ComplexModel n) 3) :=
    ((contDiffOn_of_differentiableOn_complex hXm isOpen_ball).fderiv_of_isOpen isOpen_ball
      (by simp) : ContDiffOn ℂ ∞ _ _).differentiableOn (by simp)
  have hbound : ∀ w ∈ ball ζ 1, ‖fderiv ℂ (fun s => Xfield F w₀ v s m) w‖ ≤ 2 * CX := by
    intro w hw'
    have hw2 : ‖w‖ < 2 := by
      have := norm_le_norm_add_norm_sub' w ζ
      rw [mem_ball, dist_eq_norm] at hw'
      linarith
    have hsub : ball w 1 ⊆ ball (0 : ComplexModel n) 3 :=
      ball_subset_ball' (by rw [dist_zero_right]; linarith)
    have h := norm_fderiv_le_cauchy (hXm.mono hsub) (fun u hu => (PiLp.norm_apply_le _ m).trans
      (hD.norm_Xfield_le hw hw0 le_rfl (hsub hu))) (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num)
    calc _ ≤ CX / (1 / 2) := h
      _ = 2 * CX := by ring
  have hsub1 : ball ζ 1 ⊆ ball (0 : ComplexModel n) 3 :=
    ball_subset_ball' (by rw [dist_zero_right]; linarith)
  have h := norm_fderiv_le_cauchy (hDXm.mono hsub1) hbound (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  calc _ ≤ 2 * CX / (1 / 2) := h
    _ = 4 * (288 * M₀ * M₁ / r₁ ^ 2 * ‖w₀‖ * ‖v‖) := by rw [hCX]; ring

theorem CenterData.norm_fderiv_Rcoord_le (m : Fin n) {ζ : ComplexModel n}
    (hζ : ζ ∈ closedBall (0 : ComplexModel n) 1) :
    ‖fderiv ℂ (fun s => Rfield F w₀ v η s m) ζ‖ ≤ 2 * (KR M₀ M₁ M₂ r₁ * (‖v‖ ^ 2 + ‖v‖ * ‖η‖)) := by
  have hζ1 : ‖ζ‖ ≤ 1 := mem_closedBall_zero_iff.mp hζ
  have hsub : ball ζ 1 ⊆ ball (0 : ComplexModel n) 2 :=
    ball_subset_ball' (by rw [dist_zero_right]; linarith)
  have hRm := (differentiableOn_coord (hD.differentiableOn_Rfield (v := v) (η := η) hw) m).mono
    (hsub.trans (ball_subset_ball (by norm_num)))
  have h := norm_fderiv_le_cauchy hRm (fun w hw' => (PiLp.norm_apply_le _ m).trans
    (hD.norm_Rfield_le hw hw0 (hsub hw'))) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  calc _ ≤ KR M₀ M₁ M₂ r₁ * (‖v‖ ^ 2 + ‖v‖ * ‖η‖) / (1 / 2) := h
    _ = 2 * (KR M₀ M₁ M₂ r₁ * (‖v‖ ^ 2 + ‖v‖ * ‖η‖)) := by ring

/-! ### The estimate at the centre -/

omit hD hw hw0 in
theorem contDiff_lineCurve (hF : ContDiff ℝ 2 (uncurryF F)) :
    ContDiff ℝ 2 (fun q : ℂ × ComplexModel n => lineCurve F w₀ v η q.1 q.2) := by
  have hA : ContDiff ℝ 2 (fun q : ℂ × ComplexModel n =>
      ((q.1 • v, (w₀ + q.1 * η) • q.2) : ComplexModel n × ComplexModel n)) :=
    (contDiff_fst.smul contDiff_const).prodMk
      ((contDiff_const.add (contDiff_fst.mul contDiff_const)).smul contDiff_snd)
  exact hF.comp hA

/-- **The joint Levi estimate at the centre for smooth plurisubharmonic potentials** (FPT
`eq:chern-potential-joint-bound`, in the form of the Levi form along the complex line
`τ ↦ (τ v, w₀ + τ η)`; `T = levTr (p ∘ F(0, w₀ ·))`). -/
theorem CenterData.leviForm_lineIntegral_ge {p : ComplexModel n → ℝ} (hp : ContDiff ℝ 2 p)
    (hpsh : ∀ ζ ∈ closedBall (0 : ComplexModel n) 1, ∀ u, 0 ≤ leviForm p (F 0 (w₀ • ζ)) u) :
    -(((n : ℝ) ^ 2 * (5 * (288 * M₀ * M₁ / r₁ ^ 2 * ‖w₀‖ * ‖v‖))) ^ 2 *
        ∫ ζ, chi n (‖ζ‖ ^ 2) * levTr (fun s => p (F 0 (w₀ • s))) ζ) -
      4 * (n : ℝ) ^ 2 * (2 * (KR M₀ M₁ M₂ r₁ * (‖v‖ ^ 2 + ‖v‖ * ‖η‖))) *
        ∫ ζ, -chiOne n (‖ζ‖ ^ 2) * levTr (fun s => p (F 0 (w₀ • s))) ζ ≤
    leviForm (fun τ => ∫ ζ, p (lineCurve F w₀ v η τ ζ) * chi n (‖ζ‖ ^ 2)) 0 1 := by
  have hpsh' : ∀ ζ ∈ closedBall (0 : ComplexModel n) 1, ∀ u,
      0 ≤ leviForm p (lineCurve F w₀ v η 0 ζ) u := by
    intro ζ hζ u
    rw [lineCurve_zero]
    exact hpsh ζ hζ u
  have h := leviForm_integral_ge (c := lineCurve F w₀ v η) (p := p) (X := Xfield F w₀ v)
    (R := Rfield F w₀ v η) (ρ := 3) (a₁ := 288 * M₀ * M₁ / r₁ ^ 2 * ‖w₀‖ * ‖v‖)
    (a₂ := 4 * (288 * M₀ * M₁ / r₁ ^ 2 * ‖w₀‖ * ‖v‖))
    (b₁ := 2 * (KR M₀ M₁ M₂ r₁ * (‖v‖ ^ 2 + ‖v‖ * ‖η‖))) (by norm_num) hp
    (contDiff_lineCurve hD.smooth2) (hD.differentiableOn_lineCurve_zero hw)
    (hD.differentiableOn_curveDz hw) (hD.differentiableOn_Xfield hw)
    (hD.differentiableOn_Rfield hw) (hD.Xfield_zero hw) (hD.Rfield_zero hw)
    (fun ζ hζ => hD.fderiv_apply_Xfield hw hw0 hζ) (fun ζ hζ => hD.fderiv_apply_Rfield hw hw0 hζ)
    hpsh' (fun m ζ hζ => hD.norm_fderiv_Xcoord_le hw hw0 m hζ)
    (fun m ζ hζ => hD.norm_fderiv2_Xcoord_le hw hw0 m hζ)
    (fun m ζ hζ => hD.norm_fderiv_Rcoord_le hw hw0 m hζ)
  simp only [lineCurve_zero] at h
  have e : 288 * M₀ * M₁ / r₁ ^ 2 * ‖w₀‖ * ‖v‖ + 4 * (288 * M₀ * M₁ / r₁ ^ 2 * ‖w₀‖ * ‖v‖) =
      5 * (288 * M₀ * M₁ / r₁ ^ 2 * ‖w₀‖ * ‖v‖) := by ring
  rw [e] at h
  exact h

end Center

end SGPT.NPP.DN4
