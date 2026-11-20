import SGPT.NPP.DN4Hadamard

/-!
# Holomorphy of parameter derivatives; Schwarz-type bounds

Lane DN4 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`, Steps 2–5).  Tools for the
instantiation of the core estimate `SGPT.NPP.DN4.leviForm_integral_ge` at a centre:

* `differentiableAt_complex_of_fderiv_I`: a real-differentiable map whose real derivative commutes
  with `i` is holomorphic;
* `differentiableOn_partial_param`: the derivative in a real parameter of a family of holomorphic
  maps is holomorphic (symmetry of second derivatives);
* `norm_le_of_vanishing`, `norm_fderiv_le_of_vanishing`, `norm_le_sq_of_vanishing`: Schwarz-type
  bounds for holomorphic maps vanishing at `0` to order one or two, from the Cauchy estimate
  `SGPT.Foundations.Analysis.FirstPass.norm_fderiv_le_of_forall_norm_le` and the mean value
  inequality.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric Complex
open scoped Topology ContDiff

namespace SGPT.NPP.DN4

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- A real-differentiable map whose real derivative commutes with `i` is holomorphic. -/
theorem differentiableAt_complex_of_fderiv_I {f : E → F} {x : E} (hf : DifferentiableAt ℝ f x)
    (hI : ∀ v, fderiv ℝ f x (I • v) = I • fderiv ℝ f x v) : DifferentiableAt ℂ f x := by
  set D := fderiv ℝ f x with hD
  refine (differentiableAt_iff_restrictScalars ℝ hf).2 ⟨
    { toFun := D
      map_add' := D.map_add
      map_smul' := fun c v ↦ ?_
      cont := D.continuous }, ?_⟩
  · have hc : c • v = c.re • v + c.im • (I • v) := by
      conv_lhs => rw [← Complex.re_add_im c]
      rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
    simp only [RingHom.id_apply]
    rw [hc, D.map_add, D.map_smul, D.map_smul, hI]
    conv_rhs => rw [← Complex.re_add_im c]
    rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  · ext v
    rfl

/-- **Parameter derivatives of holomorphic families are holomorphic.**  If `G : P × E → F` is
`C²` and `G(τ, ·)` is holomorphic on the open set `U` for all `τ` in the open set `W`, then
`ζ ↦ D_τ G(τ₀, ζ)(t)` is holomorphic on `U` for `τ₀ ∈ W`. -/
theorem differentiableOn_partial_param {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {G : P × E → F} (hG : ContDiff ℝ 2 G) {W : Set P} (hW : IsOpen W) {U : Set E}
    (hU : IsOpen U) (hhol : ∀ τ ∈ W, DifferentiableOn ℂ (fun ζ => G (τ, ζ)) U) {τ₀ : P}
    (hτ₀ : τ₀ ∈ W) (t : P) :
    DifferentiableOn ℂ (fun ζ => fderiv ℝ (fun τ => G (τ, ζ)) τ₀ t) U := by
  intro ζ₀ hζ₀
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hDGd : Differentiable ℝ (fderiv ℝ G) :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hpart : ∀ (τ : P) (ζ : E) (a : P), fderiv ℝ (fun τ => G (τ, ζ)) τ a =
      fderiv ℝ G (τ, ζ) (a, 0) := by
    intro τ ζ a
    have h : HasFDerivAt (fun τ => G (τ, ζ))
        ((fderiv ℝ G (τ, ζ)).comp (ContinuousLinearMap.inl ℝ P E)) τ :=
      (hGd (τ, ζ)).hasFDerivAt.comp τ (hasFDerivAt_prodMk_left (𝕜 := ℝ) τ ζ)
    rw [h.fderiv]
    simp
  have hpart' : ∀ (τ : P) (ζ : E) (e : E), fderiv ℝ (fun ζ => G (τ, ζ)) ζ e =
      fderiv ℝ G (τ, ζ) (0, e) := by
    intro τ ζ e
    have h : HasFDerivAt (fun ζ => G (τ, ζ))
        ((fderiv ℝ G (τ, ζ)).comp (ContinuousLinearMap.inr ℝ P E)) ζ :=
      (hGd (τ, ζ)).hasFDerivAt.comp ζ (hasFDerivAt_prodMk_right (𝕜 := ℝ) τ ζ)
    rw [h.fderiv]
    simp
  have e1 : (fun ζ => fderiv ℝ (fun τ => G (τ, ζ)) τ₀ t) =
      fun ζ => fderiv ℝ G (τ₀, ζ) (t, 0) := funext fun ζ => hpart τ₀ ζ t
  rw [e1]
  set D2 := fderiv ℝ (fderiv ℝ G) (τ₀, ζ₀) with hD2
  have hH : HasFDerivAt (fun ζ => fderiv ℝ G (τ₀, ζ) (t, 0))
      ((D2.comp (ContinuousLinearMap.inr ℝ P E)).flip (t, 0)) ζ₀ := by
    have h1 : HasFDerivAt (fun ζ => fderiv ℝ G (τ₀, ζ)) (D2.comp (ContinuousLinearMap.inr ℝ P E))
        ζ₀ := (hDGd (τ₀, ζ₀)).hasFDerivAt.comp ζ₀ (hasFDerivAt_prodMk_right (𝕜 := ℝ) τ₀ ζ₀)
    have h2 := h1.clm_apply (hasFDerivAt_const ((t, 0) : P × E) ζ₀)
    simpa using h2
  refine (differentiableAt_complex_of_fderiv_I hH.differentiableAt fun e => ?_).differentiableWithinAt
  rw [hH.fderiv]
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply]
  have hsymm := (hG.contDiffAt (x := (τ₀, ζ₀))).isSymmSndFDerivAt (by simp)
  rw [hsymm (0, I • e) (t, 0), hsymm (0, e) (t, 0)]
  -- the `i`-linearity of `D_ζ G(τ, ζ₀)` for `τ ∈ W`, differentiated in `τ`
  have hK : ∀ a : E, HasFDerivAt (fun τ => fderiv ℝ G (τ, ζ₀) (0, a))
      ((D2.comp (ContinuousLinearMap.inl ℝ P E)).flip (0, a)) τ₀ := by
    intro a
    have h1 : HasFDerivAt (fun τ => fderiv ℝ G (τ, ζ₀)) (D2.comp (ContinuousLinearMap.inl ℝ P E))
        τ₀ := (hDGd (τ₀, ζ₀)).hasFDerivAt.comp τ₀ (hasFDerivAt_prodMk_left (𝕜 := ℝ) τ₀ ζ₀)
    have h2 := h1.clm_apply (hasFDerivAt_const ((0, a) : P × E) τ₀)
    simpa using h2
  have hev : (fun τ => fderiv ℝ G (τ, ζ₀) (0, I • e)) =ᶠ[𝓝 τ₀]
      fun τ => I • fderiv ℝ G (τ, ζ₀) (0, e) := by
    filter_upwards [hW.mem_nhds hτ₀] with τ hτ
    have hd : DifferentiableAt ℂ (fun ζ => G (τ, ζ)) ζ₀ :=
      (hhol τ hτ).differentiableAt (hU.mem_nhds hζ₀)
    have hR : fderiv ℝ (fun ζ => G (τ, ζ)) ζ₀ =
        (fderiv ℂ (fun ζ => G (τ, ζ)) ζ₀).restrictScalars ℝ :=
      (hd.hasFDerivAt.restrictScalars ℝ).fderiv
    rw [← hpart' τ ζ₀ (I • e), ← hpart' τ ζ₀ e, hR]
    simp
  have h3 := (hK (I • e)).congr_of_eventuallyEq hev.symm
  have h4 := (hK e).const_smul I
  have h5 := h3.unique h4
  have := congrArg (fun L : P →L[ℝ] F => L t) h5
  simpa using this

end General

/-! ### Schwarz-type bounds -/

section Schwarz

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F] [FiniteDimensional ℂ E] [CompleteSpace F]

/-- The Cauchy estimate on a smaller concentric ball: `‖Dg‖ ≤ 4B/R` on `B(0, R/2)` when `|g| ≤ B`
on `B(0, R)`. -/
theorem norm_fderiv_le_of_bound {g : E → F} {R B : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball 0 R)) (hB : ∀ ξ ∈ ball (0 : E) R, ‖g ξ‖ ≤ B) {ξ : E}
    (hξ : ξ ∈ ball (0 : E) (R / 2)) : ‖fderiv ℂ g ξ‖ ≤ 4 * B / R := by
  have hsub : ball ξ (R / 2) ⊆ ball (0 : E) R := by
    refine ball_subset_ball' ?_
    rw [mem_ball, dist_zero_right] at hξ
    rw [dist_zero_right]; linarith
  have h := norm_fderiv_le_of_forall_norm_le (hg.mono hsub) (fun w hw => hB w (hsub hw))
    (by positivity : (0 : ℝ) < R / 4) (by linarith)
  calc ‖fderiv ℂ g ξ‖ ≤ B / (R / 4) := h
    _ = 4 * B / R := by field_simp

/-- **Vanishing to first order**: `|g(ξ)| ≤ (4B/R) |ξ|` on `B(0, R/2)` if `g(0) = 0`. -/
theorem norm_le_of_vanishing {g : E → F} {R B : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball 0 R)) (hB : ∀ ξ ∈ ball (0 : E) R, ‖g ξ‖ ≤ B)
    (hg0 : g 0 = 0) {ξ : E} (hξ : ξ ∈ ball (0 : E) (R / 2)) : ‖g ξ‖ ≤ 4 * B / R * ‖ξ‖ := by
  have hconv : Convex ℝ (ball (0 : E) (R / 2)) := convex_ball 0 _
  have hdiff : ∀ y ∈ ball (0 : E) (R / 2), DifferentiableAt ℂ g y := fun y hy =>
    hg.differentiableAt (isOpen_ball.mem_nhds
      (ball_subset_ball (by linarith : R / 2 ≤ R) hy))
  have h := hconv.norm_image_sub_le_of_norm_fderiv_le hdiff
    (fun y hy => norm_fderiv_le_of_bound hR hg hB hy) (mem_ball_self (by positivity)) hξ
  rwa [hg0, sub_zero, sub_zero] at h

/-- **Vanishing to second order, derivative**: `‖Dg(ξ)‖ ≤ (32B/R²) |ξ|` on `B(0, R/4)` if
`Dg(0) = 0`. -/
theorem norm_fderiv_le_of_vanishing {g : E → F} {R B : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball 0 R)) (hB : ∀ ξ ∈ ball (0 : E) R, ‖g ξ‖ ≤ B)
    (hDg0 : fderiv ℂ g 0 = 0) {ξ : E} (hξ : ξ ∈ ball (0 : E) (R / 4)) :
    ‖fderiv ℂ g ξ‖ ≤ 32 * B / R ^ 2 * ‖ξ‖ := by
  have hopen : IsOpen (ball (0 : E) R) := isOpen_ball
  have hDg : DifferentiableOn ℂ (fderiv ℂ g) (ball 0 (R / 2)) := by
    intro y hy
    have hy' : y ∈ ball (0 : E) R := ball_subset_ball (by linarith) hy
    have hd : DifferentiableAt ℂ (fderiv ℂ g) y :=
      ((contDiffAt_of_differentiableOn_complex hg hopen hy').fderiv_right (m := 1)
        (by norm_cast)).differentiableAt (by norm_num)
    exact hd.differentiableWithinAt
  have hDB : ∀ y ∈ ball (0 : E) (R / 2), ‖fderiv ℂ g y‖ ≤ 4 * B / R := fun y hy =>
    norm_fderiv_le_of_bound hR hg hB hy
  have h := norm_le_of_vanishing (g := fderiv ℂ g) (by positivity : (0 : ℝ) < R / 2) hDg hDB hDg0
    (by simpa [div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hξ)
  calc ‖fderiv ℂ g ξ‖ ≤ 4 * (4 * B / R) / (R / 2) * ‖ξ‖ := h
    _ = 32 * B / R ^ 2 * ‖ξ‖ := by field_simp; ring

/-- **Vanishing to second order**: `|g(ξ)| ≤ (32B/R²) |ξ|²` on `B(0, R/4)` if `g(0) = 0` and
`Dg(0) = 0`. -/
theorem norm_le_sq_of_vanishing {g : E → F} {R B : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball 0 R)) (hB : ∀ ξ ∈ ball (0 : E) R, ‖g ξ‖ ≤ B)
    (hg0 : g 0 = 0) (hDg0 : fderiv ℂ g 0 = 0) {ξ : E} (hξ : ξ ∈ ball (0 : E) (R / 4)) :
    ‖g ξ‖ ≤ 32 * B / R ^ 2 * ‖ξ‖ ^ 2 := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (mem_ball_self hR))
  have hconv : Convex ℝ (closedBall (0 : E) ‖ξ‖) := convex_closedBall 0 _
  have hξn : ‖ξ‖ < R / 4 := by simpa using hξ
  have hsub : closedBall (0 : E) ‖ξ‖ ⊆ ball (0 : E) (R / 4) := closedBall_subset_ball hξn
  have hdiff : ∀ y ∈ closedBall (0 : E) ‖ξ‖, DifferentiableAt ℂ g y := fun y hy =>
    hg.differentiableAt (isOpen_ball.mem_nhds (ball_subset_ball (by linarith) (hsub hy)))
  have hbound : ∀ y ∈ closedBall (0 : E) ‖ξ‖, ‖fderiv ℂ g y‖ ≤ 32 * B / R ^ 2 * ‖ξ‖ := by
    intro y hy
    refine (norm_fderiv_le_of_vanishing hR hg hB hDg0 (hsub hy)).trans ?_
    have hy' : ‖y‖ ≤ ‖ξ‖ := by simpa using hy
    exact mul_le_mul_of_nonneg_left hy' (by positivity)
  have h := hconv.norm_image_sub_le_of_norm_fderiv_le hdiff hbound
    (mem_closedBall_self (norm_nonneg _)) (mem_closedBall_zero_iff.mpr le_rfl)
  rw [hg0, sub_zero, sub_zero] at h
  calc ‖g ξ‖ ≤ 32 * B / R ^ 2 * ‖ξ‖ * ‖ξ‖ := h
    _ = 32 * B / R ^ 2 * ‖ξ‖ ^ 2 := by ring

end Schwarz

end SGPT.NPP.DN4
