import SGPT.Foundations.Analysis.LeviForm
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialIndependence
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# The Laplacian along holomorphic discs

Blueprint `claude-tok-wn-fl5`, nodes `tok-wn-fl5:disc-chain-rule`, `tok-wn-fl5:cutoff-extension`,
`tok-wn-fl5:cauchy-bound`; used in WN21 §7, proof of Lemma 7.5 (the comparison of `Δ_{ω̃} v_k`
with the Laplacian of `t ↦ v_k(σ_x(t))`).

* `laplacian_comp_holomorphic` (**chain rule along holomorphic discs**): for `f : E → ℝ` of class
  `C²` at `γ(t)` and `γ : ℂ → E` holomorphic (`C²` over `ℂ`) at `t`,
  `Δ (f ∘ γ)(t) = 4 · leviForm f (γ t) (γ'(t))`.  This generalizes TN's `laplacian_complexLine`
  (affine lines `t ↦ x + t v`): the second-order term `Df(γ t)(γ'')` cancels because the
  `ℂ`-bilinear second derivative of `γ` satisfies `γ''(i, i) = -γ''(1, 1)`.
* `laplacian_comp_holomorphic_eq_smoothDDC`: the same in TN's normalization of `ddᶜ`,
  `Δ (f ∘ γ)(t) = 4π · ddᶜf(γ t)(γ', iγ')`.
* `exists_contDiff_two_eqOn_closedBall` (**cutoff extension**): a function of class `C²` on `B(c, R)` agrees
  near every point of `B(c, r)` (`r < R`) and on `B̄(c, r)` with a `C²` function on `ℂ`.
* `norm_deriv_le_of_mapsTo_ball` (**Cauchy bound**): a holomorphic map of `B(0, 2R)` with values in a
  ball of radius `M` has `‖γ'‖ ≤ 2M/R` on `B̄(0, R)`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter Metric
open scoped Topology ContDiff Laplacian
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

/-! ### The chain rule along holomorphic discs -/

section Chain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

/-- The real derivative of a holomorphic map of one variable is multiplication by `γ'`. -/
theorem hasFDerivAt_real_of_differentiableAt {γ : ℂ → E} {s : ℂ} (hγ : DifferentiableAt ℂ γ s) :
    HasFDerivAt γ (complexLineLinear (deriv γ s)) s := by
  have h := hγ.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  exact h

/-- `v ↦ (a ↦ a • v)` as a real continuous linear map `E → (ℂ →L[ℝ] E)`. -/
def complexLineLinearCLM : E →L[ℝ] ℂ →L[ℝ] E :=
  (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] E →L[ℝ] E).flip

@[simp] theorem complexLineLinearCLM_apply (v : E) :
    complexLineLinearCLM v = complexLineLinear v := by
  ext a
  simp [complexLineLinearCLM]

/-- **The second derivative of `f ∘ γ` for a holomorphic `γ`**:
`D²(f ∘ γ)(t)(a, b) = D²f(γ t)(a γ', b γ') + Df(γ t)(b a γ'')`. -/
theorem fderiv_fderiv_comp_holomorphic {f : E → ℝ} {γ : ℂ → E} {t : ℂ}
    (hf : ContDiffAt ℝ 2 f (γ t)) (hγ : ContDiffAt ℂ 2 γ t) (a b : ℂ) :
    fderiv ℝ (fderiv ℝ (f ∘ γ)) t a b =
      fderiv ℝ (fderiv ℝ f) (γ t) (a • deriv γ t) (b • deriv γ t) +
        fderiv ℝ f (γ t) (b • a • deriv (deriv γ) t) := by
  -- regularity
  have hfev : ∀ᶠ y in 𝓝 (γ t), DifferentiableAt ℝ f y :=
    (hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hγev : ∀ᶠ s in 𝓝 t, DifferentiableAt ℂ γ s :=
    (hγ.eventually (by simp)).mono fun s hs => hs.differentiableAt (by simp)
  have hγc : ContinuousAt γ t := hγ.continuousAt
  have hfev' : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ f (γ s) := hγc.eventually hfev
  have hDf : DifferentiableAt ℝ (fderiv ℝ f) (γ t) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hDγ : DifferentiableAt ℂ (deriv γ) t := by
    have h1 : DifferentiableAt ℂ (fderiv ℂ γ) t :=
      (hγ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
    exact h1.clm_apply (differentiableAt_const (1 : ℂ))
  -- the first derivative near `t`
  have hfd : fderiv ℝ (f ∘ γ) =ᶠ[𝓝 t]
      fun s => (fderiv ℝ f (γ s)).comp (complexLineLinearCLM (deriv γ s)) := by
    filter_upwards [hγev, hfev'] with s hs hfs
    rw [complexLineLinearCLM_apply]
    exact ((hfs.hasFDerivAt).comp s (hasFDerivAt_real_of_differentiableAt hs)).fderiv
  -- the derivative of the first derivative
  have hc : HasFDerivAt (fun s => fderiv ℝ f (γ s))
      ((fderiv ℝ (fderiv ℝ f) (γ t)).comp (complexLineLinear (deriv γ t))) t :=
    hDf.hasFDerivAt.comp t
      (hasFDerivAt_real_of_differentiableAt (hγev.self_of_nhds))
  have hd : HasFDerivAt (fun s => complexLineLinearCLM (deriv γ s))
      ((complexLineLinearCLM : E →L[ℝ] ℂ →L[ℝ] E).comp
        (complexLineLinear (deriv (deriv γ) t))) t :=
    (complexLineLinearCLM : E →L[ℝ] ℂ →L[ℝ] E).hasFDerivAt.comp t
      (hasFDerivAt_real_of_differentiableAt hDγ)
  have hD := hc.clm_comp hd
  rw [hfd.fderiv_eq, hD.fderiv]
  simp [complexLineLinearCLM_apply, add_comm]

/-- **Chain rule for the Laplacian along a holomorphic disc**: for `f` of class `C²` at `γ t` and
`γ` holomorphic near `t`, `Δ (f ∘ γ)(t) = 4 · leviForm f (γ t) (γ'(t))`. -/
theorem laplacian_comp_holomorphic {f : E → ℝ} {γ : ℂ → E} {t : ℂ}
    (hf : ContDiffAt ℝ 2 f (γ t)) (hγ : ContDiffAt ℂ 2 γ t) :
    Δ (f ∘ γ) t = 4 * leviForm f (γ t) (deriv γ t) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  change realHessian (f ∘ γ) t 1 1 + realHessian (f ∘ γ) t Complex.I Complex.I = _
  rw [realHessian_eq_fderiv, realHessian_eq_fderiv, fderiv_fderiv_comp_holomorphic hf hγ,
    fderiv_fderiv_comp_holomorphic hf hγ]
  simp only [leviForm, realHessian_eq_fderiv, one_smul, smul_smul, Complex.I_mul_I, neg_one_smul,
    map_neg]
  ring

end Chain

section ChainModel

variable {n : ℕ}

/-- **The chain rule in TN's normalization of `ddᶜ`**: `Δ (f ∘ γ)(t) = 4π ddᶜf(γ t)(γ', iγ')`. -/
theorem laplacian_comp_holomorphic_eq_smoothDDC {f : ComplexModel n → ℝ} {γ : ℂ → ComplexModel n}
    {t : ℂ} (hf : ContDiffAt ℝ 2 f (γ t)) (hγ : ContDiffAt ℂ 2 γ t) :
    Δ (f ∘ γ) t =
      4 * Real.pi * smoothDDC f (γ t) ![deriv γ t, Complex.I • deriv γ t] := by
  rw [laplacian_comp_holomorphic hf hγ, smoothDDC_complexDiagonal_eq_leviForm hf]
  field_simp

end ChainModel

/-! ### Extension of a `C²` function from a disc -/

/-- **Cutoff extension.**  A function of class `C²` on the open disc `B(c, R)` coincides, on the
closed disc `B̄(c, r)` (`0 < r < R`) and near each of its points, with a function of class `C²` on
`ℂ`. -/
theorem exists_contDiff_two_eqOn_closedBall {U : ℂ → ℝ} {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hU : ContDiffOn ℝ 2 U (ball c R)) :
    ∃ V : ℂ → ℝ, ContDiff ℝ 2 V ∧ EqOn V U (closedBall c r) ∧
      ∀ t ∈ ball c r, V =ᶠ[𝓝 t] U := by
  let ρ : ContDiffBump c := ⟨r, (r + R) / 2, hr, by linarith⟩
  refine ⟨fun t => ρ t * U t, ?_, fun t ht => ?_, fun t ht => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro t
    by_cases ht : t ∈ ball c R
    · exact (ρ.contDiff.contDiffAt).mul (hU.contDiffAt (isOpen_ball.mem_nhds ht))
    · -- away from the closed support
      have hts : t ∉ tsupport (ρ : ℂ → ℝ) := by
        rw [ρ.tsupport_eq]
        intro h
        apply ht
        rw [mem_ball]
        have : dist t c ≤ (r + R) / 2 := h
        show dist t c < R
        linarith
      have h0 : (fun t => ρ t * U t) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hts] with s hs
        simp [hs]
      exact contDiffAt_const.congr_of_eventuallyEq h0
  · simp [ρ.one_of_mem_closedBall ht]
  · filter_upwards [isOpen_ball.mem_nhds ht] with s hs
    simp [ρ.one_of_mem_closedBall (ball_subset_closedBall hs)]

/-! ### A Cauchy bound for the derivative -/

/-- **Cauchy bound.**  If `γ` is holomorphic on `B(0, 2R)` with values in `B̄(p, M)`, then
`‖γ'(t)‖ ≤ 2M/R` for `‖t‖ ≤ R`. -/
theorem norm_deriv_le_of_mapsTo_ball {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {γ : ℂ → F} {R M : ℝ} (hR : 0 < R) {p : F}
    (hγ : DifferentiableOn ℂ γ (ball 0 (2 * R)))
    (hM : ∀ s ∈ ball (0 : ℂ) (2 * R), ‖γ s - p‖ ≤ M) {t : ℂ} (ht : ‖t‖ ≤ R) :
    ‖deriv γ t‖ ≤ 2 * M / R := by
  have hsub : closedBall t (R / 2) ⊆ ball (0 : ℂ) (2 * R) := by
    intro s hs
    rw [mem_closedBall] at hs
    rw [mem_ball, dist_zero_right]
    calc ‖s‖ = ‖(s - t) + t‖ := by rw [sub_add_cancel]
      _ ≤ ‖s - t‖ + ‖t‖ := norm_add_le _ _
      _ = dist s t + ‖t‖ := by rw [dist_eq_norm]
      _ < 2 * R := by linarith
  have hd : DiffContOnCl ℂ (fun s => γ s - p) (ball t (R / 2)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball t (by linarith)]
    exact (hγ.mono hsub).sub_const p
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by linarith) hd
    (fun s hs => hM s (hsub (sphere_subset_closedBall hs)))
  have hder : deriv (fun s => γ s - p) t = deriv γ t := deriv_sub_const p
  rw [hder] at h
  calc ‖deriv γ t‖ ≤ M / (R / 2) := h
    _ = 2 * M / R := by field_simp

end SGPT.Okounkov.TranscendentalWN
