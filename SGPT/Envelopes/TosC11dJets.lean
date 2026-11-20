import SGPT.Envelopes.TosC11dLinear
import SGPT.Envelopes.TosC11cMetric
import SGPT.Envelopes.TosC11bCovariant

/-!
# Jets at the maximum point: lines, symmetric derivatives, the metric of a potential, the
covariant Hessian as a smooth field

Lane TOS-C11d (`claude-tos-c11d`, node `tos-c11d:jets`).  Source: Xia, *Foundations of
pluripotential theory*, `lem:penalized-real-hessian`, Steps 1–3, for SGPT `thm:Tos_C11` (Tosatti,
Chu–Zhou).

* `hasDerivAt_line`, `line_deriv_two` — derivatives of `t ↦ f(t v)` (all differentiations at the
  maximum point are along real lines through it).
* `d2_symm`, `d3_symm₁₂`, `d3_symm₂₃`, `d4_symm₁₂`, `d4_symm₂₃`, `d4_symm₃₄` — symmetry of the
  iterated derivatives of a smooth function (FPT: "the third coordinate derivatives of the scalar
  function `a` commute").
* `leviBil H (Y, Z) = ¼(H(Y, Z) + H(iY, iZ))` and `metricOf ψ x = leviBil (D²ψ(x))`: for a local
  potential `ψ` of the Kähler form, the Riemannian metric `ω(·, J·)` (up to the factor `π`);
  `leviForm ψ x v = metricOf ψ x v v` and `complexHessian f x = cHm (leviBil (D²f(x)))`.
* `grad ψ a`, `kosB`, `kerr ψ a`, `cov ψ a`, `sFun ψ a`, `quot ψ a` — the gradient vector of `a`, the
  Koszul term, the covariant Hessian `∇²a = D²a - K(·, ·, ∇a)` as a field of bilinear forms, the
  squared gradient length `s = Da(∇a)` and the quotient `∇²a(Y, Y)/g(Y, Y)`; `covHess_eq_cov`
  identifies `cov` with `TosC11b.covHess`, and `contDiffAt_grad` gives smoothness at a point where the
  metric is positive definite.
-/

set_option autoImplicit false
-- nested spaces of continuous multilinear maps (third and fourth derivatives) need deeper pending
-- instance synthesis, as in Mathlib's own build configuration
set_option maxSynthPendingDepth 3

noncomputable section

open Filter Set
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace

namespace SGPT.Envelopes.TosC11d

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere

/-! ### Lines and symmetric derivatives -/

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem fderiv_clm_apply_const {G : E → E →L[ℝ] F} {x : E} (hG : DifferentiableAt ℝ G x)
    (u w : E) : fderiv ℝ (fun y => G y u) x w = fderiv ℝ G x w u := by
  have h := hG.hasFDerivAt.clm_apply (hasFDerivAt_const u x)
  rw [h.fderiv]
  simp

/-- The derivative along a line through `0`. -/
theorem hasDerivAt_line {f : E → F} {t : ℝ} {v : E} (hf : DifferentiableAt ℝ f (t • v)) :
    HasDerivAt (fun s : ℝ => f (s • v)) (fderiv ℝ f (t • v) v) t := by
  have hl : HasDerivAt (fun s : ℝ => s • v) v t := by
    simpa using (hasDerivAt_id t).smul_const v
  exact hf.hasFDerivAt.comp_hasDerivAt t hl

/-- **First and second derivatives along a line** for a function of class `C²` at `0`. -/
theorem line_deriv_two {f : E → F} (hf : ContDiffAt ℝ 2 f 0) (v : E) :
    (∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (fun s : ℝ => f (s • v)) (fderiv ℝ f (t • v) v) t) ∧
      HasDerivAt (fun t : ℝ => fderiv ℝ f (t • v) v) (fderiv ℝ (fderiv ℝ f) 0 v v) 0 := by
  have hl : Continuous (fun t : ℝ => t • v) := continuous_id.smul continuous_const
  have hev : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt ℝ f x :=
    (hf.eventually (by simp)).mono fun x hx => hx.differentiableAt (by norm_num)
  have hev' : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ f (t • v) := by
    have := hl.continuousAt (x := 0) |>.tendsto
    rw [zero_smul] at this
    exact this.eventually hev
  refine ⟨hev'.mono fun t ht => hasDerivAt_line ht, ?_⟩
  have hd : DifferentiableAt ℝ (fderiv ℝ f) ((0 : ℝ) • v) := by
    rw [zero_smul]
    exact (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 := hasDerivAt_line (f := fderiv ℝ f) (t := 0) (v := v) hd
  have h2 := h1.clm_apply (hasDerivAt_const (0 : ℝ) v)
  rw [zero_smul] at h2
  simpa using h2

variable {f : E → ℝ}

theorem minSmoothness_two_le_infty : minSmoothness ℝ 2 ≤ ∞ := by
  simp only [minSmoothness_of_isRCLikeNormedField]
  exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2

theorem d2_symm (hf : ContDiff ℝ ∞ f) (x u v : E) :
    fderiv ℝ (fderiv ℝ f) x u v = fderiv ℝ (fderiv ℝ f) x v u :=
  hf.contDiffAt.isSymmSndFDerivAt minSmoothness_two_le_infty u v

theorem differentiable_fderiv_iter (hf : ContDiff ℝ ∞ f) :
    Differentiable ℝ (fderiv ℝ f) ∧ Differentiable ℝ (fderiv ℝ (fderiv ℝ f)) ∧
      Differentiable ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have h2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) := h1.fderiv_right (by simp)
  have h3 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) := h2.fderiv_right (by simp)
  exact ⟨h1.differentiable (by simp), h2.differentiable (by simp), h3.differentiable (by simp)⟩

theorem d3_symm₂₃ (hf : ContDiff ℝ ∞ f) (x w u v : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x w u v = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x w v u := by
  have hd := (differentiable_fderiv_iter hf).2.1 x
  have e1 := TosC11b.fderiv_apply_apply hd w u v
  have e2 := TosC11b.fderiv_apply_apply hd w v u
  rw [← e1, ← e2]
  congr 2
  funext y
  exact d2_symm hf y u v

theorem d3_symm₁₂ (hf : ContDiff ℝ ∞ f) (x u v w : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x u v w = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x v u w := by
  have h : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have := h.contDiffAt (x := x).isSymmSndFDerivAt minSmoothness_two_le_infty u v
  rw [this]

theorem fderiv_apply₃ {G : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hG : DifferentiableAt ℝ G x) (a b c d : E) :
    fderiv ℝ (fun y => G y b c d) x a = fderiv ℝ G x a b c d := by
  have h := ((hG.hasFDerivAt.clm_apply (hasFDerivAt_const b x)).clm_apply
    (hasFDerivAt_const c x)).clm_apply (hasFDerivAt_const d x)
  rw [h.fderiv]
  simp

theorem d4_symm₃₄ (hf : ContDiff ℝ ∞ f) (x a b c d : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) x a b c d =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) x a b d c := by
  have hd := (differentiable_fderiv_iter hf).2.2 x
  rw [← fderiv_apply₃ hd, ← fderiv_apply₃ hd]
  congr 2
  funext y
  exact d3_symm₂₃ hf y b c d

theorem d4_symm₂₃ (hf : ContDiff ℝ ∞ f) (x a b c d : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) x a b c d =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) x a c b d := by
  have hd := (differentiable_fderiv_iter hf).2.2 x
  rw [← fderiv_apply₃ hd, ← fderiv_apply₃ hd]
  congr 2
  funext y
  exact d3_symm₁₂ hf y b c d

theorem d4_symm₁₂ (hf : ContDiff ℝ ∞ f) (x a b c d : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) x a b c d =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) x b a c d := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have h : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) := h1.fderiv_right (by simp)
  have := h.contDiffAt (x := x).isSymmSndFDerivAt minSmoothness_two_le_infty a b
  rw [this]

/-- The two pairs of a fourth derivative can be exchanged. -/
theorem d4_pairs (hf : ContDiff ℝ ∞ f) (x a b c d : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) x a b c d =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) x c d a b := by
  rw [d4_symm₂₃ hf, d4_symm₁₂ hf, d4_symm₃₄ hf, d4_symm₂₃ hf]

/-- A third derivative is symmetric under the exchange of the first and last vectors. -/
theorem d3_symm₁₃ (hf : ContDiff ℝ ∞ f) (x u v w : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x u v w = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x w v u := by
  rw [d3_symm₂₃ hf, d3_symm₁₂ hf, d3_symm₂₃ hf]

end General

/-! ### The metric of a local potential and complex Hessians -/

section Model

variable {n : ℕ}

theorem coordinateVector_eq_stdVec (j : Fin n) :
    coordinateVector j = TosC11c.stdVec j := rfl

/-- Multiplication by `i` as a real linear map. -/
def Jr : ComplexModel n →L[ℝ] ComplexModel n := ContinuousLinearMap.lsmul ℝ ℂ Complex.I

@[simp] theorem Jr_apply (Y : ComplexModel n) : Jr Y = Complex.I • Y := rfl

/-- `H ↦ ¼(H + H(i·, i·))` as a linear map on bilinear forms. -/
def leviBilₗ : (ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) →ₗ[ℝ]
    (ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) where
  toFun H := (1 / 4 : ℝ) • (H + H.bilinearComp Jr Jr)
  map_add' H H' := by
    ext Y Z
    simp only [ContinuousLinearMap.bilinearComp_apply, add_apply, smul_apply, smul_eq_mul]
    ring
  map_smul' c H := by
    ext Y Z
    simp only [ContinuousLinearMap.bilinearComp_apply, add_apply, smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

/-- The Levi bilinear form `¼(H(Y, Z) + H(iY, iZ))` of a real bilinear form `H`. -/
def leviBil : (ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) →L[ℝ]
    (ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap leviBilₗ

theorem leviBil_apply (H : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) (Y Z : ComplexModel n) :
    leviBil H Y Z = (H Y Z + H (Complex.I • Y) (Complex.I • Z)) / 4 := by
  simp only [leviBil, LinearMap.coe_toContinuousLinearMap', leviBilₗ, LinearMap.coe_mk,
    AddHom.coe_mk, smul_apply, add_apply, ContinuousLinearMap.bilinearComp_apply, Jr_apply,
    smul_eq_mul]
  ring

/-- The metric attached to a potential `ψ`: `g(x)(Y, Z) = ¼(D²ψ(x)(Y, Z) + D²ψ(x)(iY, iZ))`. -/
def metricOf (ψ : ComplexModel n → ℝ) (x : ComplexModel n) :
    ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ :=
  leviBil (fderiv ℝ (fderiv ℝ ψ) x)

theorem metricOf_apply (ψ : ComplexModel n → ℝ) (x Y Z : ComplexModel n) :
    metricOf ψ x Y Z = (fderiv ℝ (fderiv ℝ ψ) x Y Z +
      fderiv ℝ (fderiv ℝ ψ) x (Complex.I • Y) (Complex.I • Z)) / 4 :=
  leviBil_apply _ _ _

theorem leviForm_eq_metricOf (ψ : ComplexModel n → ℝ) (x v : ComplexModel n) :
    leviForm ψ x v = metricOf ψ x v v := by
  rw [metricOf_apply, leviForm, realHessian_eq_fderiv, realHessian_eq_fderiv]

theorem contDiff_metricOf {ψ : ComplexModel n → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (metricOf ψ) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
  have h2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ ψ)) := h1.fderiv_right (by simp)
  exact leviBil.contDiff.comp h2

/-- The metric of a smooth potential is symmetric. -/
theorem metricOf_symm {ψ : ComplexModel n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (x Y Z : ComplexModel n) :
    metricOf ψ x Y Z = metricOf ψ x Z Y := by
  rw [metricOf_apply, metricOf_apply, d2_symm hψ x Y Z, d2_symm hψ x (Complex.I • Y)]

/-- The derivatives of the metric. -/
theorem fderiv_metricOf {ψ : ComplexModel n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (x v : ComplexModel n) :
    fderiv ℝ (metricOf ψ) x v = leviBil (fderiv ℝ (fderiv ℝ (fderiv ℝ ψ)) x v) := by
  have h2 : Differentiable ℝ (fderiv ℝ (fderiv ℝ ψ)) := (differentiable_fderiv_iter hψ).2.1
  have h := (leviBil.hasFDerivAt (x := fderiv ℝ (fderiv ℝ ψ) x)).comp x (h2 x).hasFDerivAt
  rw [show metricOf ψ = ⇑leviBil ∘ fderiv ℝ (fderiv ℝ ψ) from rfl, h.fderiv]
  rfl

theorem fderiv_fderiv_metricOf {ψ : ComplexModel n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (x v w : ComplexModel n) :
    fderiv ℝ (fderiv ℝ (metricOf ψ)) x v w =
      leviBil (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ ψ))) x v w) := by
  have h3 : Differentiable ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ ψ))) := (differentiable_fderiv_iter hψ).2.2
  have hfun : fderiv ℝ (metricOf ψ) =
      fun y => (leviBil : _ →L[ℝ] _).comp (fderiv ℝ (fderiv ℝ (fderiv ℝ ψ)) y) := by
    funext y
    ext v
    rw [fderiv_metricOf hψ]
    rfl
  have h := (h3 x).hasFDerivAt
  have hc : HasFDerivAt (fun y => (leviBil : _ →L[ℝ] _).comp (fderiv ℝ (fderiv ℝ (fderiv ℝ ψ)) y))
      ((ContinuousLinearMap.compL ℝ (ComplexModel n) _ _ leviBil).comp
        (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ ψ))) x)) x :=
    ((ContinuousLinearMap.compL ℝ (ComplexModel n) _ _ leviBil).hasFDerivAt).comp x h
  rw [hfun, hc.fderiv]
  rfl

/-- The entries `g(eⱼ, eₖ) + i g(eⱼ, i eₖ)` of the Hermitian matrix of a real bilinear form. -/
def cHm (g : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) (j k : Fin n) : ℂ :=
  (g (coordinateVector j) (coordinateVector k) : ℂ) +
    Complex.I * (g (coordinateVector j) (Complex.I • coordinateVector k) : ℂ)

/-- The complex Hessian through the Levi bilinear form of the real Hessian. -/
theorem complexHessian_eq_cHm (f : ComplexModel n → ℝ) (x : ComplexModel n) (j k : Fin n) :
    complexHessian f x j k = cHm (leviBil (fderiv ℝ (fderiv ℝ f) x)) j k := by
  simp only [complexHessian, cHm, leviBil_apply, realHessian_eq_fderiv, smul_smul,
    Complex.I_mul_I, neg_one_smul, map_neg]
  push_cast
  ring

/-- `cHm` is linear in the form. -/
def cHmL (j k : Fin n) : (ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => cHm g j k
      map_add' := fun g g' => by simp only [cHm, add_apply]; push_cast; ring
      map_smul' := fun c g => by
        simp only [cHm, smul_apply, smul_eq_mul, RingHom.id_apply, Complex.real_smul]
        push_cast; ring }

theorem cHmL_apply (g : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) (j k : Fin n) :
    cHmL j k g = cHm g j k := rfl

theorem cHm_re_diag (g : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) (j : Fin n) :
    (cHm g j j).re = g (coordinateVector j) (coordinateVector j) := by
  simp [cHm]

/-- The complex Hessian matrix of a smooth function along a line: entrywise first derivative. -/
theorem hasDerivAt_complexHessian_line {f : ComplexModel n → ℝ} (hf : ContDiff ℝ ∞ f)
    (b : ComplexModel n) (t : ℝ) (j k : Fin n) :
    HasDerivAt (fun s : ℝ => complexHessian f (s • b) j k)
      (cHm (leviBil (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (t • b) b)) j k) t := by
  have h3 := (differentiable_fderiv_iter hf).2.1
  have h := hasDerivAt_line (f := fderiv ℝ (fderiv ℝ f)) (t := t) (v := b) (h3 _)
  have h' := ((cHmL j k).comp leviBil).hasFDerivAt.comp_hasDerivAt t h
  simp only [complexHessian_eq_cHm]
  exact h'

/-- Entrywise second derivative at `0` of the complex Hessian matrix along a line. -/
theorem hasDerivAt_complexHessian_line_two {f : ComplexModel n → ℝ} (hf : ContDiff ℝ ∞ f)
    (b : ComplexModel n) (j k : Fin n) :
    HasDerivAt (fun s : ℝ => cHm (leviBil (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (s • b) b)) j k)
      (cHm (leviBil (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) 0 b b)) j k) 0 := by
  have h4 := (differentiable_fderiv_iter hf).2.2
  have h := hasDerivAt_line (f := fderiv ℝ (fderiv ℝ (fderiv ℝ f))) (t := 0) (v := b) (h4 _)
  have h2 := h.clm_apply (hasDerivAt_const (0 : ℝ) b)
  rw [zero_smul] at h2
  have h' := ((cHmL j k).comp leviBil).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  exact h'.congr_deriv (by simp [cHmL_apply])

end Model

/-! ### The covariant Hessian as a field of bilinear forms -/

section Covariant

variable {n : ℕ}

/-- The Koszul form `½(P(Y)(Z, G) + P(Z)(Y, G) - P(G)(Y, Z))` of a derivative `P = Dg` of a metric,
as a bilinear form in `(Y, Z)`. -/
def kosForm (P : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (G : ComplexModel n) : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun Y Z => (P Y Z G + P Z Y G - P G Y Z) / 2)
      (fun Y Y' Z => by simp only [map_add, add_apply]; ring)
      (fun c Y Z => by simp only [map_smul, smul_apply, smul_eq_mul]; ring)
      (fun Y Z Z' => by simp only [map_add, add_apply]; ring)
      (fun c Y Z => by simp only [map_smul, smul_apply, smul_eq_mul]; ring))
    (3 / 2 * ‖P‖ * ‖G‖) fun Y Z => by
      simp only [LinearMap.mk₂_apply, Real.norm_eq_abs]
      have b1 : |P Y Z G| ≤ ‖P‖ * ‖Y‖ * ‖Z‖ * ‖G‖ := by
        rw [← Real.norm_eq_abs]
        calc ‖P Y Z G‖ ≤ ‖P Y Z‖ * ‖G‖ := (P Y Z).le_opNorm G
          _ ≤ ‖P Y‖ * ‖Z‖ * ‖G‖ := by gcongr; exact (P Y).le_opNorm Z
          _ ≤ ‖P‖ * ‖Y‖ * ‖Z‖ * ‖G‖ := by gcongr; exact P.le_opNorm Y
      have b2 : |P Z Y G| ≤ ‖P‖ * ‖Z‖ * ‖Y‖ * ‖G‖ := by
        rw [← Real.norm_eq_abs]
        calc ‖P Z Y G‖ ≤ ‖P Z Y‖ * ‖G‖ := (P Z Y).le_opNorm G
          _ ≤ ‖P Z‖ * ‖Y‖ * ‖G‖ := by gcongr; exact (P Z).le_opNorm Y
          _ ≤ ‖P‖ * ‖Z‖ * ‖Y‖ * ‖G‖ := by gcongr; exact P.le_opNorm Z
      have b3 : |P G Y Z| ≤ ‖P‖ * ‖G‖ * ‖Y‖ * ‖Z‖ := by
        rw [← Real.norm_eq_abs]
        calc ‖P G Y Z‖ ≤ ‖P G Y‖ * ‖Z‖ := (P G Y).le_opNorm Z
          _ ≤ ‖P G‖ * ‖Y‖ * ‖Z‖ := by gcongr; exact (P G).le_opNorm Y
          _ ≤ ‖P‖ * ‖G‖ * ‖Y‖ * ‖Z‖ := by gcongr; exact P.le_opNorm G
      rw [abs_div, abs_two]
      have := abs_sub (P Y Z G + P Z Y G) (P G Y Z)
      have := abs_add_le (P Y Z G) (P Z Y G)
      have e : 3 / 2 * ‖P‖ * ‖G‖ * ‖Y‖ * ‖Z‖ =
          (‖P‖ * ‖Y‖ * ‖Z‖ * ‖G‖ + ‖P‖ * ‖Z‖ * ‖Y‖ * ‖G‖ + ‖P‖ * ‖G‖ * ‖Y‖ * ‖Z‖) / 2 := by ring
      rw [e]
      gcongr
      linarith

theorem kosForm_apply (P : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (G Y Z : ComplexModel n) : kosForm P G Y Z = (P Y Z G + P Z Y G - P G Y Z) / 2 := rfl

theorem abs_kosForm_le (P : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (G Y Z : ComplexModel n) : |kosForm P G Y Z| ≤ 3 / 2 * ‖P‖ * ‖G‖ * ‖Y‖ * ‖Z‖ := by
  rw [← Real.norm_eq_abs]
  have h0 : 0 ≤ 3 / 2 * ‖P‖ * ‖G‖ := by positivity
  calc ‖kosForm P G Y Z‖ ≤ ‖kosForm P G‖ * ‖Y‖ * ‖Z‖ := (kosForm P G).le_opNorm₂ Y Z
    _ ≤ 3 / 2 * ‖P‖ * ‖G‖ * ‖Y‖ * ‖Z‖ := by
        gcongr
        exact LinearMap.mkContinuous₂_norm_le _ h0 _

/-- The gradient vector of `a` for the metric of `ψ`. -/
def grad (ψ a : ComplexModel n → ℝ) (x : ComplexModel n) : ComplexModel n :=
  TosC11c.gradVec (metricOf ψ x) (fderiv ℝ a x)

/-- The Koszul term `K(·, ·, ∇a)` of the covariant Hessian. -/
def kerr (ψ a : ComplexModel n → ℝ) (x : ComplexModel n) :
    ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ :=
  kosForm (fderiv ℝ (metricOf ψ) x) (grad ψ a x)

/-- **The covariant Hessian** `∇²a = D²a - K(·, ·, ∇a)` of `a` for the metric of `ψ`. -/
def cov (ψ a : ComplexModel n → ℝ) (x : ComplexModel n) :
    ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ a) x - kerr ψ a x

/-- The squared length `s = Da(∇a)` of the gradient. -/
def sFun (ψ a : ComplexModel n → ℝ) (x : ComplexModel n) : ℝ :=
  fderiv ℝ a x (grad ψ a x)

/-- The quotient `∇²a(Y, Y)/g(Y, Y)`. -/
def quot (ψ a : ComplexModel n → ℝ) (x Y : ComplexModel n) : ℝ :=
  TosC11b.covHess (metricOf ψ) a x Y Y (grad ψ a x) / metricOf ψ x Y Y

theorem cov_apply (ψ a : ComplexModel n → ℝ) (x Y Z : ComplexModel n) :
    cov ψ a x Y Z = fderiv ℝ (fderiv ℝ a) x Y Z -
      (fderiv ℝ (metricOf ψ) x Y Z (grad ψ a x) + fderiv ℝ (metricOf ψ) x Z Y (grad ψ a x) -
        fderiv ℝ (metricOf ψ) x (grad ψ a x) Y Z) / 2 := rfl

theorem covHess_eq_cov {ψ : ComplexModel n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (a : ComplexModel n → ℝ)
    (x Y Z : ComplexModel n) :
    TosC11b.covHess (metricOf ψ) a x Y Z (grad ψ a x) = cov ψ a x Y Z := by
  have hg : DifferentiableAt ℝ (metricOf ψ) x :=
    (contDiff_metricOf hψ).contDiffAt.differentiableAt (by simp)
  rw [TosC11b.covHess, TosC11c.koszul_eq hg, cov_apply]

theorem quot_eq {ψ : ComplexModel n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (a : ComplexModel n → ℝ)
    (x Y : ComplexModel n) : quot ψ a x Y = cov ψ a x Y Y / metricOf ψ x Y Y := by
  rw [quot, covHess_eq_cov hψ]

/-- The gradient vector is smooth where the metric is positive definite. -/
theorem contDiffAt_grad {ψ a : ComplexModel n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (ha : ContDiff ℝ ∞ a)
    {x : ComplexModel n} (hpos : ∀ v, v ≠ 0 → 0 < metricOf ψ x v v) :
    ContDiffAt ℝ ∞ (grad ψ a) x := by
  have hflip : ContDiff ℝ ∞ (fun y => (metricOf ψ y).flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (ComplexModel n) (ComplexModel n) ℝ).toContinuousLinearEquiv.contDiff.comp
      (contDiff_metricOf hψ)
  have hinv : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse ((metricOf ψ x).flip) := by
    have h := contDiffAt_map_inverse (𝕜 := ℝ) (n := ∞) (TosC11c.flipEquiv (metricOf ψ x) hpos)
    rwa [TosC11c.coe_flipEquiv] at h
  have hcomp : ContDiffAt ℝ ∞
      (ContinuousLinearMap.inverse ∘ fun y => (metricOf ψ y).flip) x :=
    hinv.comp x hflip.contDiffAt
  have hDa : ContDiff ℝ ∞ (fderiv ℝ a) := ha.fderiv_right (by simp)
  exact hcomp.clm_apply hDa.contDiffAt

/-- The defining identity of the gradient vector. -/
theorem metricOf_grad {ψ a : ComplexModel n → ℝ} {x : ComplexModel n}
    (hpos : ∀ v, v ≠ 0 → 0 < metricOf ψ x v v) (V : ComplexModel n) :
    metricOf ψ x V (grad ψ a x) = fderiv ℝ a x V :=
  TosC11c.apply_gradVec hpos _ V

end Covariant

end SGPT.Envelopes.TosC11d
