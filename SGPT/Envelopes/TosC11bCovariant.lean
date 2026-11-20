import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# The covariant Hessian of a Riemannian metric in coordinates and its transformation law

Lane TOS-C11b (`claude-tos-c11b`, node `tos-c11b:covariant-hessian`).  Source: Xia, *Foundations of
pluripotential theory*, `sec:real-hessian-envelopes`, the paragraphs before
`lem:penalized-real-hessian` (Koszul formula, Christoffel symbols, the covariant Hessian
`∇²b(Y, Z) = Y(Zb) - (∇_Y Z)b` and its coordinate formula), for SGPT `thm:Tos_C11` (Tosatti,
Chu–Zhou).

For a field `g` of bilinear forms on an open set of a real normed space (the coordinate expression of
a Riemannian metric) and constant vector fields `Y, Z, W`, the **Koszul form**
`K_g(z)(Y, Z, W) = ½(D_Y g(Z, W) + D_Z g(Y, W) - D_W g(Y, Z))` is `g(∇_Y Z, W)`.  Instead of the
Christoffel symbols `∇_Y Z` (which need the inverse of `g`), we use a gradient vector `G` of the
function `a` (`g(V, G) = Da(V)` for all `V`): the **covariant Hessian** is
`∇²a(Y, Z) = D²a(Y, Z) - Da(∇_Y Z) = D²a(Y, Z) - K_g(Y, Z, G)` (`covHess`).

* `koszul_pullback` — for a `C²` map `φ` and the pulled back field
  `(φ^*g)(w)(Y, Z) = g(φ w)(Dφ Y, Dφ Z)` (`pullbackBilin`),
  `K_{φ^*g}(w)(Y, Z, W) = K_g(φ w)(Dφ Y, Dφ Z, Dφ W) + g(φ w)(D²φ(Y, Z), Dφ W)`
  (the transformation law of the Christoffel symbols, `Dφ Γ' = Γ(Dφ·, Dφ·) + D²φ`);
* `covHess_comp` — **the covariant Hessian is a tensor**: if `G` is a gradient of `a` for `g` at
  `φ w` and `Dφ(w) G' = G`, then `G'` is a gradient of `a ∘ φ` for `φ^*g` at `w` and
  `∇²_{φ^*g}(a ∘ φ)(w)(Y, Z) = ∇²_g a(φ w)(Dφ Y, Dφ Z)`;
* `covHess_of_fderiv_eq_zero` — where the first derivatives of `g` vanish (the centre of normal
  coordinates, `claude-tos-c11:normal-coordinates`), the covariant Hessian is the coordinate Hessian.

Hence the largest eigenvalue `ℓ` of `∇²a` relative to `g`, computed in any chart, is independent of
the chart (chart transitions map `φ^*g`-unit vectors to `g`-unit vectors), as FPT's Step 2 needs.
-/

set_option autoImplicit false

noncomputable section

open Filter
open scoped Topology

namespace SGPT.Envelopes.TosC11b

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **Koszul form** of a field `g` of bilinear forms, for constant vector fields:
`K_g(z)(Y, Z, W) = ½(D_Y g(Z, W) + D_Z g(Y, W) - D_W g(Y, Z))`. -/
def koszul (g : E → E →L[ℝ] E →L[ℝ] ℝ) (z Y Z W : E) : ℝ :=
  (fderiv ℝ (fun x => g x Z W) z Y + fderiv ℝ (fun x => g x Y W) z Z -
    fderiv ℝ (fun x => g x Y Z) z W) / 2

/-- The **pullback** of a field of bilinear forms by a map: `(φ^*g)(w)(Y, Z) = g(φ w)(Dφ Y, Dφ Z)`. -/
def pullbackBilin (g : E → E →L[ℝ] E →L[ℝ] ℝ) (φ : E → E) (w : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (g (φ w)).bilinearComp (fderiv ℝ φ w) (fderiv ℝ φ w)

@[simp] theorem pullbackBilin_apply (g : E → E →L[ℝ] E →L[ℝ] ℝ) (φ : E → E) (w Y Z : E) :
    pullbackBilin g φ w Y Z = g (φ w) (fderiv ℝ φ w Y) (fderiv ℝ φ w Z) := rfl

/-- The **covariant Hessian** `∇²a(Y, Z) = D²a(Y, Z) - K_g(Y, Z, G)`, for a gradient vector `G` of
`a` (`g(V, G) = Da(V)`). -/
def covHess (g : E → E →L[ℝ] E →L[ℝ] ℝ) (a : E → ℝ) (z Y Z G : E) : ℝ :=
  fderiv ℝ (fderiv ℝ a) z Y Z - koszul g z Y Z G

/-- Directional derivatives of the entries of a differentiable field of bilinear forms. -/
theorem fderiv_apply_apply {g : E → E →L[ℝ] E →L[ℝ] ℝ} {z : E} (hg : DifferentiableAt ℝ g z)
    (Y Z W : E) : fderiv ℝ (fun x => g x Z W) z Y = fderiv ℝ g z Y Z W := by
  have h1 := hg.hasFDerivAt.clm_apply (hasFDerivAt_const Z z)
  have h2 := h1.clm_apply (hasFDerivAt_const W z)
  rw [h2.fderiv]
  simp

/-- The derivative of an entry of the pulled back field. -/
theorem fderiv_pullbackBilin_apply {g : E → E →L[ℝ] E →L[ℝ] ℝ} {φ : E → E} {w : E}
    (hg : DifferentiableAt ℝ g (φ w)) (hφ : DifferentiableAt ℝ φ w)
    (hφ' : DifferentiableAt ℝ (fderiv ℝ φ) w) (Y Z W : E) :
    fderiv ℝ (fun x => pullbackBilin g φ x Z W) w Y =
      fderiv ℝ g (φ w) (fderiv ℝ φ w Y) (fderiv ℝ φ w Z) (fderiv ℝ φ w W) +
        g (φ w) (fderiv ℝ (fderiv ℝ φ) w Y Z) (fderiv ℝ φ w W) +
        g (φ w) (fderiv ℝ φ w Z) (fderiv ℝ (fderiv ℝ φ) w Y W) := by
  have hc : HasFDerivAt (fun x => g (φ x)) ((fderiv ℝ g (φ w)).comp (fderiv ℝ φ w)) w :=
    HasFDerivAt.comp (g := g) w hg.hasFDerivAt hφ.hasFDerivAt
  have hu : ∀ V : E, HasFDerivAt (fun x => fderiv ℝ φ x V)
      ((fderiv ℝ (fderiv ℝ φ) w).flip V) w := fun V => by
    have := hφ'.hasFDerivAt.clm_apply (hasFDerivAt_const V w)
    simpa using this
  have h := (hc.clm_apply (hu Z)).clm_apply (hu W)
  simp only [pullbackBilin_apply]
  rw [h.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  ring

/-- **Transformation law of the Koszul form** (of the Christoffel symbols): for `φ` of class `C²`
at `w` and `g` differentiable and symmetric at `φ w`,
`K_{φ^*g}(w)(Y, Z, W) = K_g(φ w)(Dφ Y, Dφ Z, Dφ W) + g(φ w)(D²φ(Y, Z), Dφ W)`. -/
theorem koszul_pullback {g : E → E →L[ℝ] E →L[ℝ] ℝ} {φ : E → E} {w : E}
    (hg : DifferentiableAt ℝ g (φ w)) (hsym : ∀ U V, g (φ w) U V = g (φ w) V U)
    (hφ : ContDiffAt ℝ 2 φ w) (Y Z W : E) :
    koszul (pullbackBilin g φ) w Y Z W =
      koszul g (φ w) (fderiv ℝ φ w Y) (fderiv ℝ φ w Z) (fderiv ℝ φ w W) +
        g (φ w) (fderiv ℝ (fderiv ℝ φ) w Y Z) (fderiv ℝ φ w W) := by
  have hφ1 : DifferentiableAt ℝ φ w := hφ.differentiableAt (by norm_num)
  have hφ' : DifferentiableAt ℝ (fderiv ℝ φ) w :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hS : ∀ U V, fderiv ℝ (fderiv ℝ φ) w U V = fderiv ℝ (fderiv ℝ φ) w V U :=
    hφ.isSymmSndFDerivAt (by simp)
  simp only [koszul, fderiv_pullbackBilin_apply hg hφ1 hφ', fderiv_apply_apply hg]
  rw [hS Z Y, hS W Y, hS W Z, hsym (fderiv ℝ φ w Z) (fderiv ℝ (fderiv ℝ φ) w Y W),
    hsym (fderiv ℝ φ w Y) (fderiv ℝ (fderiv ℝ φ) w Z W)]
  ring

/-- **Second-order chain rule**: `D²(a ∘ φ)(w)(Y, Z) = D²a(φ w)(Dφ Y, Dφ Z) + Da(φ w)(D²φ(Y, Z))`. -/
theorem fderiv_fderiv_comp {a : E → ℝ} {φ : E → E} {w : E} (ha : ContDiffAt ℝ 2 a (φ w))
    (hφ : ContDiffAt ℝ 2 φ w) (Y Z : E) :
    fderiv ℝ (fderiv ℝ (a ∘ φ)) w Y Z =
      fderiv ℝ (fderiv ℝ a) (φ w) (fderiv ℝ φ w Y) (fderiv ℝ φ w Z) +
        fderiv ℝ a (φ w) (fderiv ℝ (fderiv ℝ φ) w Y Z) := by
  -- the first derivatives near `w`
  have haev : ∀ᶠ x in 𝓝 w, DifferentiableAt ℝ a (φ x) := by
    have h1 : ∀ᶠ y in 𝓝 (φ w), ContDiffAt ℝ 2 a y := ha.eventually (by simp)
    have h2 := hφ.continuousAt.eventually h1
    exact h2.mono fun x hx => hx.differentiableAt (by norm_num)
  have hφev : ∀ᶠ x in 𝓝 w, DifferentiableAt ℝ φ x :=
    (hφ.eventually (by simp)).mono fun x hx => hx.differentiableAt (by norm_num)
  have heq : fderiv ℝ (a ∘ φ) =ᶠ[𝓝 w] fun x => (fderiv ℝ a (φ x)).comp (fderiv ℝ φ x) :=
    (haev.and hφev).mono fun x hx => fderiv_comp x hx.1 hx.2
  have ha' : DifferentiableAt ℝ (fderiv ℝ a) (φ w) :=
    (ha.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hφ' : DifferentiableAt ℝ (fderiv ℝ φ) w :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hA : HasFDerivAt (fun x => fderiv ℝ a (φ x))
      ((fderiv ℝ (fderiv ℝ a) (φ w)).comp (fderiv ℝ φ w)) w :=
    (ha'.hasFDerivAt.comp w (hφ.differentiableAt (by norm_num)).hasFDerivAt :)
  have h := hA.clm_comp hφ'.hasFDerivAt
  rw [heq.fderiv_eq, h.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply]
  simp only [ContinuousLinearMap.comp_apply]
  ring

/-- **The covariant Hessian is a tensor** (FPT, before `lem:penalized-real-hessian`): let `φ` be `C²`
at `w`, `a` be `C²` at `φ w`, `g` differentiable and symmetric at `φ w`, `G` a gradient of `a` for `g`
at `φ w` and `Dφ(w) G' = G`.  Then `G'` is a gradient of `a ∘ φ` for `φ^*g` at `w`, and
`∇²_{φ^*g}(a ∘ φ)(w)(Y, Z) = ∇²_g a(φ w)(Dφ Y, Dφ Z)`. -/
theorem covHess_comp {g : E → E →L[ℝ] E →L[ℝ] ℝ} {φ : E → E} {a : E → ℝ} {w G G' : E}
    (hg : DifferentiableAt ℝ g (φ w)) (hsym : ∀ U V, g (φ w) U V = g (φ w) V U)
    (hφ : ContDiffAt ℝ 2 φ w) (ha : ContDiffAt ℝ 2 a (φ w))
    (hG : ∀ V, g (φ w) V G = fderiv ℝ a (φ w) V) (hG' : fderiv ℝ φ w G' = G) :
    (∀ V, pullbackBilin g φ w V G' = fderiv ℝ (a ∘ φ) w V) ∧
      ∀ Y Z, covHess (pullbackBilin g φ) (a ∘ φ) w Y Z G' =
        covHess g a (φ w) (fderiv ℝ φ w Y) (fderiv ℝ φ w Z) G := by
  have hφ1 : DifferentiableAt ℝ φ w := hφ.differentiableAt (by norm_num)
  have ha1 : DifferentiableAt ℝ a (φ w) := ha.differentiableAt (by norm_num)
  refine ⟨fun V => ?_, fun Y Z => ?_⟩
  · rw [pullbackBilin_apply, hG', hG, fderiv_comp w ha1 hφ1, ContinuousLinearMap.comp_apply]
  · simp only [covHess]
    rw [koszul_pullback hg hsym hφ, hG', hG, fderiv_fderiv_comp ha hφ]
    ring

/-- At a point where the first derivatives of `g` vanish (the centre of normal coordinates), the
Koszul form vanishes and the covariant Hessian is the coordinate Hessian. -/
theorem covHess_of_fderiv_eq_zero {g : E → E →L[ℝ] E →L[ℝ] ℝ} {a : E → ℝ} {z : E}
    (hg : HasFDerivAt (𝕜 := ℝ) g 0 z) (Y Z G : E) :
    covHess g a z Y Z G = fderiv ℝ (fderiv ℝ a) z Y Z := by
  have h0 : ∀ Y Z W : E, fderiv ℝ (fun x => g x Z W) z Y = 0 := fun Y Z W => by
    rw [fderiv_apply_apply hg.differentiableAt, hg.fderiv]
    simp
  simp only [covHess, koszul, h0]
  simp

end SGPT.Envelopes.TosC11b
