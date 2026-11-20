import SGPT.Foundations.Analysis.Pending.StokesCutoff

/-!
# Second-order calculus for the Kiselman minimum with a varying end point

Lane DN2, `thm:DNT23_C11bar`; FPT `lem:varying-log-radius-minimum`
(`chapters/inputs/q10-big-envelope-regularity.tex`, lines 368–413), the Schur complement step.

For `K(x, s)` and a curve of critical points `s = σ(x)` (`∂_s K(x, σ(x)) = 0` near `x₀`), the
second derivative of `x ↦ K(x, σ(x))` is the second derivative of `K` along the tangent vector
`(a, Dσ(a))`; hence the Levi form of `x ↦ K(x, σ(x))` at `x₀` in direction `v` *equals* the joint
Levi form of `(x, ζ) ↦ K(x, Re ζ)` at `(x₀, σ(x₀))` in the direction `(v, η)` with
`η = Dσ(v) - i Dσ(iv)`.  This is the identity behind Kiselman's minimum principle (the Hessian
of the minimum is the Schur complement `P - a⁻¹ y y*`).

## Main results

* `realHessian_comp_clm`: `D²(u ∘ A) = D²u(A·, A·)` for a continuous linear `A`, at a point.
* `realHessian_comp_graph`: `D²(K ∘ (id, σ))(a, a) = D²K((a, Dσ a), (a, Dσ a))` along a curve of
  critical points.
* `leviForm_comp_re`: the joint Levi form of `(x, ζ) ↦ K(x, Re ζ)`.
* `leviForm_graph_eq_joint`: the Levi form of the critical value function is a joint Levi form.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.NPP.DN2

open SGPT.Foundations.Analysis

section Real

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The second derivative of `u ∘ A` for a continuous linear map `A`, at a point where `u` is
`C²`. -/
theorem realHessian_comp_clm (A : F →L[ℝ] E) {u : E → ℝ} {p : F} (hu : ContDiffAt ℝ 2 u (A p))
    (v w : F) : realHessian (fun q => u (A q)) p v w = realHessian u (A p) (A v) (A w) := by
  have hDu : ∀ᶠ y in 𝓝 (A p), DifferentiableAt ℝ u y :=
    (hu.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hev : fderiv ℝ (fun q => u (A q)) =ᶠ[𝓝 p] fun q => (fderiv ℝ u (A q)).comp A := by
    filter_upwards [A.continuous.continuousAt.eventually hDu] with q hq
    exact (hq.hasFDerivAt.comp q A.hasFDerivAt).fderiv
  have hDDu : DifferentiableAt ℝ (fderiv ℝ u) (A p) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hc : HasFDerivAt (fun q => fderiv ℝ u (A q))
      ((fderiv ℝ (fderiv ℝ u) (A p)).comp A) p :=
    hDDu.hasFDerivAt.comp p A.hasFDerivAt
  have hcomp : HasFDerivAt (fun q => (fderiv ℝ u (A q)).comp A)
      (((ContinuousLinearMap.compL ℝ F E ℝ).flip A).comp
        ((fderiv ℝ (fderiv ℝ u) (A p)).comp A)) p :=
    ((ContinuousLinearMap.compL ℝ F E ℝ).flip A).hasFDerivAt.comp p hc
  rw [realHessian_eq_fderiv, hev.fderiv_eq, hcomp.fderiv, realHessian_eq_fderiv]
  rfl

/-- **Second derivative along a curve of critical points.**  If `K` is `C²` at `(x₀, σ x₀)`,
`σ` is differentiable near `x₀` and `∂_s K(x, σ x) = 0` near `x₀`, then
`D²(x ↦ K(x, σ x))(a, a) = D²K((a, Dσ a), (a, Dσ a))`. -/
theorem realHessian_comp_graph {K : E × ℝ → ℝ} {σ : E → ℝ} {x₀ : E}
    (hK : ContDiffAt ℝ 2 K (x₀, σ x₀)) (hσ : ∀ᶠ x in 𝓝 x₀, DifferentiableAt ℝ σ x)
    (hcrit : ∀ᶠ x in 𝓝 x₀, fderiv ℝ K (x, σ x) (0, 1) = 0) (a : E) :
    realHessian (fun x => K (x, σ x)) x₀ a a =
      realHessian K (x₀, σ x₀) (a, fderiv ℝ σ x₀ a) (a, fderiv ℝ σ x₀ a) := by
  set Γ : E → E × ℝ := fun x => (x, σ x) with hΓ
  have hσ₀ : DifferentiableAt ℝ σ x₀ := hσ.self_of_nhds
  have hΓd : ∀ x, DifferentiableAt ℝ σ x →
      HasFDerivAt Γ ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ σ x)) x := fun x hx =>
    (hasFDerivAt_id x).prodMk hx.hasFDerivAt
  have hΓc : ContinuousAt Γ x₀ := (hΓd x₀ hσ₀).continuousAt
  have hDK : ∀ᶠ y in 𝓝 (Γ x₀), DifferentiableAt ℝ K y :=
    (hK.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hDDK : DifferentiableAt ℝ (fderiv ℝ K) (Γ x₀) :=
    (hK.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  -- the first derivative of `K ∘ Γ` near `x₀`
  have hev : fderiv ℝ (fun x => K (x, σ x)) =ᶠ[𝓝 x₀]
      fun x => (fderiv ℝ K (Γ x)).comp (ContinuousLinearMap.inl ℝ E ℝ) := by
    filter_upwards [hΓc.eventually hDK, hσ, hcrit] with x hKx hσx hcx
    have h1 := (hKx.hasFDerivAt.comp x (hΓd x hσx)).fderiv
    ext a
    change fderiv ℝ (K ∘ Γ) x a = _
    rw [h1]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_id', id_eq,
      ContinuousLinearMap.inl_apply]
    have hsplit : ((a, fderiv ℝ σ x a) : E × ℝ) = (a, 0) + (fderiv ℝ σ x a) • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    rw [hsplit, map_add, map_smul, hcx, smul_zero, add_zero]
  -- its derivative at `x₀`
  have hD1 : HasFDerivAt (fun x => fderiv ℝ K (Γ x))
      ((fderiv ℝ (fderiv ℝ K) (Γ x₀)).comp ((ContinuousLinearMap.id ℝ E).prod
        (fderiv ℝ σ x₀))) x₀ :=
    hDDK.hasFDerivAt.comp x₀ (hΓd x₀ hσ₀)
  have hD2 : HasFDerivAt (fun x => (fderiv ℝ K (Γ x)).comp (ContinuousLinearMap.inl ℝ E ℝ))
      (((ContinuousLinearMap.compL ℝ E (E × ℝ) ℝ).flip (ContinuousLinearMap.inl ℝ E ℝ)).comp
        ((fderiv ℝ (fderiv ℝ K) (Γ x₀)).comp ((ContinuousLinearMap.id ℝ E).prod
          (fderiv ℝ σ x₀)))) x₀ :=
    ((ContinuousLinearMap.compL ℝ E (E × ℝ) ℝ).flip
      (ContinuousLinearMap.inl ℝ E ℝ)).hasFDerivAt.comp x₀ hD1
  -- the derivative of the critical equation vanishes
  have hD3 : HasFDerivAt (fun x => fderiv ℝ K (Γ x) ((0 : E), (1 : ℝ)))
      ((ContinuousLinearMap.apply ℝ ℝ ((0 : E), (1 : ℝ))).comp
        ((fderiv ℝ (fderiv ℝ K) (Γ x₀)).comp ((ContinuousLinearMap.id ℝ E).prod
          (fderiv ℝ σ x₀)))) x₀ :=
    (ContinuousLinearMap.apply ℝ ℝ ((0 : E), (1 : ℝ))).hasFDerivAt.comp x₀ hD1
  have hzero : HasFDerivAt (fun x => fderiv ℝ K (Γ x) ((0 : E), (1 : ℝ))) (0 : E →L[ℝ] ℝ) x₀ :=
    (hasFDerivAt_const (0 : ℝ) x₀).congr_of_eventuallyEq (hcrit.mono fun x hx => hx)
  have hcrit2 : fderiv ℝ (fderiv ℝ K) (Γ x₀) (a, fderiv ℝ σ x₀ a) ((0 : E), (1 : ℝ)) = 0 := by
    have := congrArg (fun L : E →L[ℝ] ℝ => L a) (hD3.unique hzero)
    simpa using this
  rw [realHessian_eq_fderiv, hev.fderiv_eq, hD2.fderiv, realHessian_eq_fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_id', id_eq,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.inl_apply]
  have hsplit : ((a, fderiv ℝ σ x₀ a) : E × ℝ) = (a, 0) + (fderiv ℝ σ x₀ a) • ((0 : E), (1 : ℝ)) := by
    ext <;> simp
  change _ = fderiv ℝ (fderiv ℝ K) (Γ x₀) (a, fderiv ℝ σ x₀ a) (a, fderiv ℝ σ x₀ a)
  rw [show fderiv ℝ (fderiv ℝ K) (Γ x₀) (a, fderiv ℝ σ x₀ a) (a, fderiv ℝ σ x₀ a) =
      fderiv ℝ (fderiv ℝ K) (Γ x₀) (a, fderiv ℝ σ x₀ a)
        ((a, 0) + (fderiv ℝ σ x₀ a) • ((0 : E), (1 : ℝ))) by rw [← hsplit],
    map_add, map_smul, hcrit2, smul_zero, add_zero]

end Real

section Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The real-linear map `(x, ζ) ↦ (x, Re ζ)`. -/
def reProd : E × ℂ →L[ℝ] E × ℝ :=
  (ContinuousLinearMap.fst ℝ E ℂ).prod (Complex.reCLM.comp (ContinuousLinearMap.snd ℝ E ℂ))

@[simp] theorem reProd_apply (p : E × ℂ) : reProd p = (p.1, p.2.re) := rfl

/-- **The joint Levi form of `(x, ζ) ↦ K(x, Re ζ)`** in terms of the second derivative of `K`. -/
theorem leviForm_comp_re {K : E × ℝ → ℝ} {x : E} {s : ℝ} (hK : ContDiffAt ℝ 2 K (x, s))
    (v : E) (η : ℂ) :
    leviForm (fun p : E × ℂ => K (p.1, p.2.re)) (x, (s : ℂ)) (v, η) =
      (realHessian K (x, s) (v, η.re) (v, η.re) +
        realHessian K (x, s) (Complex.I • v, (Complex.I * η).re)
          (Complex.I • v, (Complex.I * η).re)) / 4 := by
  have hK' : ContDiffAt ℝ 2 K (reProd ((x, (s : ℂ)) : E × ℂ)) := by simpa using hK
  have h := realHessian_comp_clm (reProd (E := E)) hK'
  unfold leviForm
  rw [show (fun p : E × ℂ => K (p.1, p.2.re)) = fun p => K (reProd p) from rfl, h, h]
  simp [Prod.smul_mk]

/-- **The Levi form of a critical value function is a joint Levi form** (the Schur complement
identity of Kiselman's minimum principle). -/
theorem leviForm_graph_eq_joint {K : E × ℝ → ℝ} {σ : E → ℝ} {x₀ : E}
    (hK : ContDiffAt ℝ 2 K (x₀, σ x₀)) (hσ : ∀ᶠ x in 𝓝 x₀, DifferentiableAt ℝ σ x)
    (hcrit : ∀ᶠ x in 𝓝 x₀, fderiv ℝ K (x, σ x) (0, 1) = 0) (v : E) :
    leviForm (fun x => K (x, σ x)) x₀ v =
      leviForm (fun p : E × ℂ => K (p.1, p.2.re)) (x₀, (σ x₀ : ℂ))
        (v, (fderiv ℝ σ x₀ v : ℂ) - Complex.I * (fderiv ℝ σ x₀ (Complex.I • v) : ℂ)) := by
  rw [leviForm_comp_re hK]
  unfold leviForm
  rw [realHessian_comp_graph hK hσ hcrit, realHessian_comp_graph hK hσ hcrit]
  congr 3 <;> simp [Complex.mul_re, Complex.sub_re, Complex.mul_im]

end Complex

end SGPT.NPP.DN2
