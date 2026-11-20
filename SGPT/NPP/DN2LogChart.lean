import SGPT.NPP.DN2KiselmanCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Levi forms under holomorphic maps; logarithmic radius coordinates

Lane DN2, `thm:DNT23_C11bar`; FPT `thm:big-metric-laplacian-rooftop` applies
`lem:varying-log-radius-minimum` "in the variable `s = log t`", i.e. through the holomorphic map
`(x, ζ) ↦ (x, e^ζ)`.  The Levi form is natural under holomorphic maps:
`L(u ∘ Φ)(p)(v) = L(u)(Φ p)(DΦ v)` (the second-derivative terms of `Φ` cancel because `D²Φ` is
complex bilinear).

## Main results

* `realHessian_comp_vec`: the second-order chain rule `D²(u ∘ Φ) = D²u(DΦ, DΦ) + Du(D²Φ)`.
* `leviForm_comp_holomorphic`: naturality of the Levi form under a holomorphic map.
* `leviForm_comp_expProd`: the case `Φ(x, ζ) = (x, e^ζ)`.
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

/-- **The second-order chain rule** at a point. -/
theorem realHessian_comp_vec {Φ : E → F} {u : F → ℝ} {p : E} (hΦ : ContDiffAt ℝ 2 Φ p)
    (hu : ContDiffAt ℝ 2 u (Φ p)) (a b : E) :
    realHessian (fun q => u (Φ q)) p a b =
      realHessian u (Φ p) (fderiv ℝ Φ p a) (fderiv ℝ Φ p b) +
        fderiv ℝ u (Φ p) (fderiv ℝ (fderiv ℝ Φ) p a b) := by
  have hDu : ∀ᶠ y in 𝓝 (Φ p), DifferentiableAt ℝ u y :=
    (hu.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hDΦ : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ Φ q :=
    (hΦ.eventually (by simp)).mono fun q hq => hq.differentiableAt (by simp)
  have hev : fderiv ℝ (fun q => u (Φ q)) =ᶠ[𝓝 p] fun q => (fderiv ℝ u (Φ q)).comp (fderiv ℝ Φ q) := by
    filter_upwards [hΦ.continuousAt.eventually hDu, hDΦ] with q hq hq'
    exact (hq.hasFDerivAt.comp q hq'.hasFDerivAt).fderiv
  have hDDu : DifferentiableAt ℝ (fderiv ℝ u) (Φ p) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDDΦ : DifferentiableAt ℝ (fderiv ℝ Φ) p :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h1 : HasFDerivAt (fun q => fderiv ℝ u (Φ q))
      ((fderiv ℝ (fderiv ℝ u) (Φ p)).comp (fderiv ℝ Φ p)) p :=
    hDDu.hasFDerivAt.comp p (hΦ.differentiableAt (by simp)).hasFDerivAt
  have h2 := h1.clm_comp hDDΦ.hasFDerivAt
  rw [realHessian_eq_fderiv, hev.fderiv_eq, h2.fderiv, realHessian_eq_fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
  ring

end Real

section Complex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- The real derivative of a holomorphic map is complex linear. -/
theorem fderiv_real_eq_restrictScalars {Φ : E → F} {q : E} (hΦ : DifferentiableAt ℂ Φ q) :
    fderiv ℝ Φ q = (fderiv ℂ Φ q).restrictScalars ℝ :=
  (hΦ.hasFDerivAt.restrictScalars ℝ).fderiv

/-- The second real derivative of a holomorphic map is complex bilinear: `D²Φ(Iv, Iv) = -D²Φ(v, v)`. -/
theorem fderiv2_real_I {Φ : E → F} {p : E} (hΦ : ContDiffAt ℂ 2 Φ p) (v : E) :
    fderiv ℝ (fderiv ℝ Φ) p (Complex.I • v) (Complex.I • v) =
      -fderiv ℝ (fderiv ℝ Φ) p v v := by
  have hD : ∀ᶠ q in 𝓝 p, DifferentiableAt ℂ Φ q :=
    (hΦ.eventually (by simp)).mono fun q hq => hq.differentiableAt (by simp)
  have hev : fderiv ℝ Φ =ᶠ[𝓝 p] fun q => (fderiv ℂ Φ q).restrictScalars ℝ := by
    filter_upwards [hD] with q hq
    exact fderiv_real_eq_restrictScalars hq
  have hDD : DifferentiableAt ℂ (fderiv ℂ Φ) p :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hR : HasFDerivAt (fun q => (fderiv ℂ Φ q).restrictScalars ℝ)
      ((ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℂ).restrictScalars ℝ |>.comp
        ((fderiv ℂ (fderiv ℂ Φ) p).restrictScalars ℝ)) p :=
    ((ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℂ).restrictScalars ℝ).hasFDerivAt.comp p
      (hDD.hasFDerivAt.restrictScalars ℝ)
  rw [hev.fderiv_eq, hR.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars']
  change (fderiv ℂ (fderiv ℂ Φ) p (Complex.I • v)) (Complex.I • v) =
    -((fderiv ℂ (fderiv ℂ Φ) p v) v)
  rw [(fderiv ℂ (fderiv ℂ Φ) p).map_smul, ContinuousLinearMap.smul_apply,
    (fderiv ℂ (fderiv ℂ Φ) p v).map_smul, smul_smul, Complex.I_mul_I, neg_one_smul]

/-- **Naturality of the Levi form under a holomorphic map**. -/
theorem leviForm_comp_holomorphic {Φ : E → F} {u : F → ℝ} {p : E} (hΦ : ContDiffAt ℂ 2 Φ p)
    (hu : ContDiffAt ℝ 2 u (Φ p)) (v : E) :
    leviForm (fun q => u (Φ q)) p v = leviForm u (Φ p) (fderiv ℂ Φ p v) := by
  have hΦR : ContDiffAt ℝ 2 Φ p := hΦ.restrict_scalars ℝ
  have hD := fderiv_real_eq_restrictScalars (hΦ.differentiableAt (by simp))
  unfold leviForm
  rw [realHessian_comp_vec hΦR hu, realHessian_comp_vec hΦR hu, fderiv2_real_I hΦ, hD]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_neg,
    (fderiv ℂ Φ p).map_smul]
  ring

/-- **The logarithmic radius coordinate**: for `Φ(x, ζ) = (x, e^ζ)`,
`L(J ∘ Φ)(x, ζ)(v, η) = L(J)(x, e^ζ)(v, e^ζ η)`. -/
theorem leviForm_comp_expProd {J : E × ℂ → ℝ} {x : E} {ζ : ℂ}
    (hJ : ContDiffAt ℝ 2 J (x, Complex.exp ζ)) (v : E) (η : ℂ) :
    leviForm (fun p : E × ℂ => J (p.1, Complex.exp p.2)) (x, ζ) (v, η) =
      leviForm J (x, Complex.exp ζ) (v, Complex.exp ζ * η) := by
  have hΦ : ContDiff ℂ 2 (fun p : E × ℂ => (p.1, Complex.exp p.2)) :=
    contDiff_fst.prodMk (Complex.contDiff_exp.comp contDiff_snd)
  have h := leviForm_comp_holomorphic (Φ := fun p : E × ℂ => (p.1, Complex.exp p.2))
    (p := (x, ζ)) hΦ.contDiffAt hJ (v, η)
  rw [h]
  congr 1
  have hd : HasFDerivAt (fun p : E × ℂ => (p.1, Complex.exp p.2))
      ((ContinuousLinearMap.fst ℂ E ℂ).prod
        ((Complex.exp ζ) • ContinuousLinearMap.snd ℂ E ℂ)) (x, ζ) := by
    refine (hasFDerivAt_fst).prodMk ?_
    have := (Complex.hasDerivAt_exp ζ).comp_hasFDerivAt (x, ζ)
      (hasFDerivAt_snd : HasFDerivAt (Prod.snd : E × ℂ → ℂ) (ContinuousLinearMap.snd ℂ E ℂ) (x, ζ))
    exact this
  rw [hd.fderiv]
  simp

end Complex

end SGPT.NPP.DN2
