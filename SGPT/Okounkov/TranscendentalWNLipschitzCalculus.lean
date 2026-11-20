import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The Laplacian of a convolution on `ℂ` (package WN-LIP)

Calculus needed for the blueprint node `tok-wn:lipschitz` (WN21 Corollary 7.6), recorded in
`claude-tok-wn-lip` as `tok-wn-lip:convolution`:

* `contDiff_laplacian`: the Laplacian of a smooth function on `ℂ` is smooth;
* `laplacian_eq_fderiv_fderiv`: `Δ F = ∂₁∂₁ F + ∂_I∂_I F` for `C²` functions `F`, written with
  iterated directional (Fréchet) derivatives;
* `fderiv_convolution_right_apply`: `∂_v (f ⋆ g) = f ⋆ ∂_v g` for `f` locally integrable and `g`
  of class `C¹` with compact support;
* `laplacian_convolution_right`: `Δ (f ⋆ g) = f ⋆ Δ g` for `f` locally integrable and `g` smooth
  with compact support;
* `laplacian_comp_neg`, `laplacian_comp_sub_left`: the Laplacian commutes with the reflections
  `t ↦ -t` and `t ↦ a - t`.

Here `f ⋆ g` is Mathlib's convolution `x ↦ ∫ f t * g (x - t) dt` with respect to Lebesgue measure
on `ℂ`, and `Δ` is Mathlib's Laplacian (`∂²/∂x² + ∂²/∂y²`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN.Lipschitz

open MeasureTheory Metric Laplacian Complex
open scoped Convolution ContDiff

/-- The Laplacian of a smooth function on `ℂ` is smooth. -/
theorem contDiff_laplacian {u : ℂ → ℝ} (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (Δ u) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ u)) :=
    (contDiff_infty_iff_fderiv.mp (contDiff_infty_iff_fderiv.mp hu).2).2
  have h₁ := (hD.clm_apply (contDiff_const (c := (1 : ℂ)))).clm_apply
    (contDiff_const (c := (1 : ℂ)))
  have hI := (hD.clm_apply (contDiff_const (c := I))).clm_apply (contDiff_const (c := I))
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply]
  simpa using h₁.add hI

/-- The second iterated derivative on the diagonal is the iterated directional derivative. -/
theorem iteratedFDeriv_two_self {F : ℂ → ℝ} (hF : ContDiff ℝ 2 F) (x v : ℂ) :
    iteratedFDeriv ℝ 2 F x ![v, v] = fderiv ℝ (fun y => fderiv ℝ F y v) x v := by
  rw [iteratedFDeriv_two_apply]
  have hd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp

/-- `Δ F = ∂₁∂₁ F + ∂_I∂_I F` for `C²` functions on `ℂ`. -/
theorem laplacian_eq_fderiv_fderiv {F : ℂ → ℝ} (hF : ContDiff ℝ 2 F) (x : ℂ) :
    Δ F x = fderiv ℝ (fun y => fderiv ℝ F y 1) x 1 + fderiv ℝ (fun y => fderiv ℝ F y I) x I := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_self hF]

/-- **Derivative of a convolution.**  `∂_v (f ⋆ g) = f ⋆ ∂_v g` for `f` locally integrable and `g`
of class `C¹` with compact support. -/
theorem fderiv_convolution_right_apply {f g : ℂ → ℝ} (hf : LocallyIntegrable f)
    (hcg : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (x v : ℂ) :
    fderiv ℝ (f ⋆ g) x v = (f ⋆ fun a => fderiv ℝ g a v) x := by
  rw [(hcg.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hf hg x).fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hf (hcg.fderiv ℝ)
    (hg.continuous_fderiv one_ne_zero) x v

/-- The directional derivative of a smooth function is smooth. -/
theorem contDiff_fderiv_apply_const {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (v : ℂ) :
    ContDiff ℝ ∞ (fun a => fderiv ℝ g a v) :=
  (contDiff_infty_iff_fderiv.mp hg).2.clm_apply contDiff_const

/-- **The Laplacian of a convolution.**  `Δ (f ⋆ g) = f ⋆ Δ g` for `f` locally integrable and `g`
smooth with compact support. -/
theorem laplacian_convolution_right {f g : ℂ → ℝ} (hf : LocallyIntegrable f)
    (hcg : HasCompactSupport g) (hg : ContDiff ℝ ∞ g) (x : ℂ) :
    Δ (f ⋆ g) x = (f ⋆ Δ g) x := by
  have h1 : ContDiff ℝ 1 g := hg.of_le (by exact_mod_cast le_top)
  have hfg : ContDiff ℝ ∞ (f ⋆ g) :=
    hcg.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hf hg
  set D : ℂ → (ℂ → ℝ) → ℂ → ℝ := fun v k a => fderiv ℝ k a v with hD
  have hDs : ∀ v, ContDiff ℝ ∞ (D v g) := fun v => contDiff_fderiv_apply_const hg v
  have hDc : ∀ v, HasCompactSupport (D v g) := fun v => hcg.fderiv_apply ℝ v
  have hDDs : ∀ v, ContDiff ℝ ∞ (D v (D v g)) := fun v => contDiff_fderiv_apply_const (hDs v) v
  have hDDc : ∀ v, HasCompactSupport (D v (D v g)) := fun v => (hDc v).fderiv_apply ℝ v
  have hstep : ∀ v, fderiv ℝ (fun y => fderiv ℝ (f ⋆ g) y v) x v = (f ⋆ D v (D v g)) x := by
    intro v
    have hfun : (fun y => fderiv ℝ (f ⋆ g) y v) = f ⋆ D v g := by
      funext y
      exact fderiv_convolution_right_apply hf hcg h1 y v
    rw [hfun]
    exact fderiv_convolution_right_apply hf (hDc v) ((hDs v).of_le (by exact_mod_cast le_top)) x v
  rw [laplacian_eq_fderiv_fderiv (hfg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)), hstep, hstep]
  have hΔ : Δ g = D 1 (D 1 g) + D I (D I g) := by
    funext a
    rw [laplacian_eq_fderiv_fderiv (hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
    rfl
  rw [hΔ, ConvolutionExistsAt.distrib_add
    ((hDDc 1).convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ) hf (hDDs 1).continuous x)
    ((hDDc I).convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ) hf (hDDs I).continuous x)]

/-- The Laplacian commutes with the reflection `t ↦ -t`. -/
theorem laplacian_comp_neg {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) (y : ℂ) :
    Δ (fun t => f (-t)) y = Δ f (-y) := by
  have hcomp : (fun t => f (-t)) = f ∘ (-ContinuousLinearMap.id ℝ ℂ) := by
    funext t
    simp
  rw [hcomp, InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ hf _ le_rfl]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    neg_apply, ContinuousLinearMap.id_apply]
  have hneg : ∀ v : ℂ, (fun i : Fin 2 => -(![v, v] i)) = fun i => (-1 : ℝ) • ![v, v] i := by
    intro v
    funext i
    simp
  rw [hneg, hneg, ContinuousMultilinearMap.map_smul_univ, ContinuousMultilinearMap.map_smul_univ]
  simp

/-- The Laplacian commutes with the reflection `t ↦ a - t`. -/
theorem laplacian_comp_sub_left {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) (a y : ℂ) :
    Δ (fun t => f (a - t)) y = Δ f (a - y) := by
  set g : ℂ → ℝ := fun s => f (-s) with hg
  have hcomp : (fun t => f (a - t)) = fun t => g (t + -a) := by
    funext t
    simp only [hg]
    congr 1
    ring
  have htr : Δ (fun t => g (t + -a)) y = Δ g (y + -a) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
      InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
    simp only [iteratedFDeriv_comp_add_right (f := g)]
  rw [hcomp, htr, hg, laplacian_comp_neg hf, show -(y + -a) = a - y by ring]

end SGPT.Okounkov.TranscendentalWN.Lipschitz
