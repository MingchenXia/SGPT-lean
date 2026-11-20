import SGPT.NPP.DN4Core
import SGPT.NPP.DN4Holo

/-!
# The curve family of the smoothing along a complex line

Lane DN4 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`, Steps 2–4).  Let
`F(z, ξ)` be a smooth map (`z` a base point near `0`, `ξ` a tangent vector), holomorphic in `ξ`
with `F(z, 0) = z`.  Along the complex line `τ ↦ (τ v, w₀ + τ η)` the integrand of the smoothing is
`p(c(τ, ζ))` with `c(τ, ζ) = F(τ v, (w₀ + τ η) ζ)` (`lineCurve`).  We compute the Wirtinger
derivatives of `c` at `τ = 0` (`curveDz`, `curveDzbar`, `curveLevi` of `SGPT.NPP.DN4Pointwise`):
with `ξ = w₀ ζ`,

* `∂_τ̄ c = b(ξ)`, `b = ∂̄_v F(0, ·)` (`dbarZ`; `curveDzbar_lineCurve`);
* `∂_τ c = y(ξ) + η DF₀(ξ) ζ`, `y = ∂_v F(0, ·)` (`dZ`; `curveDz_lineCurve`);
* `∂_τ ∂_τ̄ c = q(ξ) + Db(ξ)(η ζ)`, `q = L_v F(0, ·)` (`levZ`; `curveLevi_lineCurve`),

where `F₀ = F(0, ·)`; the terms quadratic in `η` cancel because `F₀` is holomorphic.  The functions
`b`, `y`, `q` are holomorphic (`differentiableOn_dbarZ`, …): derivatives in a real parameter of
holomorphic families.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric Complex
open scoped Topology ContDiff

namespace SGPT.NPP.DN4

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {n : ℕ}

/-! ### Derivatives along a complex line in a product -/

section Line

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

theorem hasFDerivAt_complexLine (x a : V) (τ : ℂ) :
    HasFDerivAt (fun τ : ℂ => x + τ • a) (complexLineLinear a) τ := by
  have := ((complexLineLinear a).hasFDerivAt (x := τ)).const_add x
  simpa using this

/-- `D(G ∘ ℓ)(0)(t) = DG(x)(t a)` along the line `ℓ(τ) = x + τ a`. -/
theorem fderiv_line_apply {G : V → W} (hG : Differentiable ℝ G) (x a : V) (t : ℂ) :
    fderiv ℝ (fun τ : ℂ => G (x + τ • a)) 0 t = fderiv ℝ G x (t • a) := by
  have h0 : HasFDerivAt G (fderiv ℝ G x) (x + (0 : ℂ) • a) := by
    simpa using (hG x).hasFDerivAt
  have h : HasFDerivAt (fun τ : ℂ => G (x + τ • a)) ((fderiv ℝ G x).comp (complexLineLinear a))
      0 := h0.comp (0 : ℂ) (hasFDerivAt_complexLine x a 0)
  rw [h.fderiv]
  rfl

/-- `D²(G ∘ ℓ)(0)(s, t) = D²G(x)(s a, t a)`. -/
theorem fderiv_fderiv_line_apply {G : V → W} (hG : ContDiff ℝ 2 G) (x a : V) (s t : ℂ) :
    fderiv ℝ (fderiv ℝ (fun τ : ℂ => G (x + τ • a))) 0 s t =
      fderiv ℝ (fderiv ℝ G) x (s • a) (t • a) := by
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hDGd : Differentiable ℝ (fderiv ℝ G) :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hfun : fderiv ℝ (fun τ : ℂ => G (x + τ • a)) =
      fun τ => (fderiv ℝ G (x + τ • a)).comp (complexLineLinear a) := by
    funext τ
    exact ((hGd _).hasFDerivAt.comp τ (hasFDerivAt_complexLine x a τ)).fderiv
  have h0 : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) (x + (0 : ℂ) • a) := by
    simpa using (hDGd x).hasFDerivAt
  have h1 : HasFDerivAt (fun τ : ℂ => fderiv ℝ G (x + τ • a))
      ((fderiv ℝ (fderiv ℝ G) x).comp (complexLineLinear a)) 0 :=
    h0.comp (0 : ℂ) (hasFDerivAt_complexLine x a 0)
  have h2 := ((ContinuousLinearMap.compL ℝ ℂ V W).flip (complexLineLinear a)).hasFDerivAt.comp
    (0 : ℂ) h1
  rw [hfun]
  rw [show (fun τ : ℂ => (fderiv ℝ G (x + τ • a)).comp (complexLineLinear a)) =
    ((ContinuousLinearMap.compL ℝ ℂ V W).flip (complexLineLinear a)) ∘
      (fun τ : ℂ => fderiv ℝ G (x + τ • a)) from rfl, h2.fderiv]
  rfl

end Line

/-! ### The partial derivatives of `F` -/

/-- `F` as a function on the product. -/
def uncurryF (F : ComplexModel n → ComplexModel n → ComplexModel n) :
    ComplexModel n × ComplexModel n → ComplexModel n :=
  fun q => F q.1 q.2

/-- `y(ξ) = ∂_v F(0, ξ)` (holomorphic part of the derivative in the base point). -/
def dZ (F : ComplexModel n → ComplexModel n → ComplexModel n) (v ξ : ComplexModel n) :
    ComplexModel n :=
  (2 : ℝ)⁻¹ • (fderiv ℝ (fun z => F z ξ) 0 v - I • fderiv ℝ (fun z => F z ξ) 0 (I • v))

/-- `b(ξ) = ∂̄_v F(0, ξ)` (antiholomorphic part of the derivative in the base point). -/
def dbarZ (F : ComplexModel n → ComplexModel n → ComplexModel n) (v ξ : ComplexModel n) :
    ComplexModel n :=
  (2 : ℝ)⁻¹ • (fderiv ℝ (fun z => F z ξ) 0 v + I • fderiv ℝ (fun z => F z ξ) 0 (I • v))

/-- `q(ξ) = ∂_v ∂̄_v F(0, ξ)`. -/
def levZ (F : ComplexModel n → ComplexModel n → ComplexModel n) (v ξ : ComplexModel n) :
    ComplexModel n :=
  (4 : ℝ)⁻¹ • (fderiv ℝ (fderiv ℝ (uncurryF F)) (0, ξ) (v, 0) (v, 0) +
    fderiv ℝ (fderiv ℝ (uncurryF F)) (0, ξ) (I • v, 0) (I • v, 0))

section Partials

variable {F : ComplexModel n → ComplexModel n → ComplexModel n}

theorem fderiv_partial_left (hF : Differentiable ℝ (uncurryF F)) (z ξ u : ComplexModel n) :
    fderiv ℝ (fun z => F z ξ) z u = fderiv ℝ (uncurryF F) (z, ξ) (u, 0) := by
  have h : HasFDerivAt (fun z => F z ξ)
      ((fderiv ℝ (uncurryF F) (z, ξ)).comp (ContinuousLinearMap.inl ℝ _ _)) z := by
    have := HasFDerivAt.comp (g := uncurryF F) z (hF (z, ξ)).hasFDerivAt
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) z ξ)
    exact this
  rw [h.fderiv]
  simp

theorem fderiv_partial_right (hF : Differentiable ℝ (uncurryF F)) (z ξ e : ComplexModel n) :
    fderiv ℝ (F z) ξ e = fderiv ℝ (uncurryF F) (z, ξ) (0, e) := by
  have h : HasFDerivAt (F z)
      ((fderiv ℝ (uncurryF F) (z, ξ)).comp (ContinuousLinearMap.inr ℝ _ _)) ξ := by
    have := HasFDerivAt.comp (g := uncurryF F) ξ (hF (z, ξ)).hasFDerivAt
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) z ξ)
    exact this
  rw [h.fderiv]
  simp

/-- The second partial derivative in `ξ`. -/
theorem fderiv_fderiv_partial_right (hF : ContDiff ℝ 2 (uncurryF F)) (z ξ e e' : ComplexModel n) :
    fderiv ℝ (fderiv ℝ (F z)) ξ e e' = fderiv ℝ (fderiv ℝ (uncurryF F)) (z, ξ) (0, e) (0, e') := by
  have hFd : Differentiable ℝ (uncurryF F) := hF.differentiable (by norm_num)
  have hDFd : Differentiable ℝ (fderiv ℝ (uncurryF F)) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hfun : fderiv ℝ (F z) = fun ξ =>
      (fderiv ℝ (uncurryF F) (z, ξ)).comp (ContinuousLinearMap.inr ℝ _ _) := by
    funext ξ
    have := HasFDerivAt.comp (g := uncurryF F) ξ (hFd (z, ξ)).hasFDerivAt
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) z ξ)
    exact this.fderiv
  have h1 : HasFDerivAt (fun ξ => fderiv ℝ (uncurryF F) (z, ξ))
      ((fderiv ℝ (fderiv ℝ (uncurryF F)) (z, ξ)).comp (ContinuousLinearMap.inr ℝ _ _)) ξ :=
    (hDFd (z, ξ)).hasFDerivAt.comp ξ (hasFDerivAt_prodMk_right (𝕜 := ℝ) z ξ)
  have h2 := ((ContinuousLinearMap.compL ℝ (ComplexModel n) (ComplexModel n × ComplexModel n)
    (ComplexModel n)).flip (ContinuousLinearMap.inr ℝ _ _)).hasFDerivAt.comp ξ h1
  rw [hfun]
  rw [show (fun ξ => (fderiv ℝ (uncurryF F) (z, ξ)).comp
      (ContinuousLinearMap.inr ℝ (ComplexModel n) (ComplexModel n))) =
    ((ContinuousLinearMap.compL ℝ (ComplexModel n) (ComplexModel n × ComplexModel n)
      (ComplexModel n)).flip (ContinuousLinearMap.inr ℝ _ _)) ∘
      (fun ξ => fderiv ℝ (uncurryF F) (z, ξ)) from rfl, h2.fderiv]
  rfl

/-- `D_ξ (D_z F(z, ξ) u)(e) = D²F(z, ξ)((u, 0), (0, e))`. -/
theorem fderiv_partial_left_apply_right (hF : ContDiff ℝ 2 (uncurryF F))
    (z ξ u e : ComplexModel n) :
    fderiv ℝ (fun ξ => fderiv ℝ (uncurryF F) (z, ξ) (u, 0)) ξ e =
      fderiv ℝ (fderiv ℝ (uncurryF F)) (z, ξ) (u, 0) (0, e) := by
  have hDFd : Differentiable ℝ (fderiv ℝ (uncurryF F)) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h1 : HasFDerivAt (fun ξ => fderiv ℝ (uncurryF F) (z, ξ))
      ((fderiv ℝ (fderiv ℝ (uncurryF F)) (z, ξ)).comp (ContinuousLinearMap.inr ℝ _ _)) ξ :=
    (hDFd (z, ξ)).hasFDerivAt.comp ξ (hasFDerivAt_prodMk_right (𝕜 := ℝ) z ξ)
  have h2 := h1.clm_apply (hasFDerivAt_const ((u, 0) : ComplexModel n × ComplexModel n) ξ)
  rw [h2.fderiv]
  have hs := (hF.contDiffAt (x := (z, ξ))).isSymmSndFDerivAt (by simp)
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, map_zero, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.inr_apply, zero_add]
  exact hs _ _

/-- `D_z (D_z F(z, ξ)(u, 0))(u') = D²F(z, ξ)((u, 0), (u', 0))` at `z`. -/
theorem fderiv_partial_left_apply_left (hF : ContDiff ℝ 2 (uncurryF F))
    (z ξ u u' : ComplexModel n) :
    fderiv ℝ (fun z => fderiv ℝ (uncurryF F) (z, ξ) (u, 0)) z u' =
      fderiv ℝ (fderiv ℝ (uncurryF F)) (z, ξ) (u', 0) (u, 0) := by
  have hDFd : Differentiable ℝ (fderiv ℝ (uncurryF F)) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h1 : HasFDerivAt (fun z => fderiv ℝ (uncurryF F) (z, ξ))
      ((fderiv ℝ (fderiv ℝ (uncurryF F)) (z, ξ)).comp (ContinuousLinearMap.inl ℝ _ _)) z :=
    (hDFd (z, ξ)).hasFDerivAt.comp z (hasFDerivAt_prodMk_left (𝕜 := ℝ) z ξ)
  have h2 := h1.clm_apply (hasFDerivAt_const ((u, 0) : ComplexModel n × ComplexModel n) z)
  rw [h2.fderiv]
  simp

end Partials

/-! ### Holomorphy of the coefficient functions -/

section Holo

variable {F : ComplexModel n → ComplexModel n → ComplexModel n} {δ r₁ : ℝ}

theorem differentiableOn_partial_left (hF : ContDiff ℝ 2 (uncurryF F))
    (hhol : ∀ z ∈ ball (0 : ComplexModel n) δ, DifferentiableOn ℂ (F z) (ball 0 r₁))
    {z₀ : ComplexModel n} (hz₀ : z₀ ∈ ball (0 : ComplexModel n) δ) (u : ComplexModel n) :
    DifferentiableOn ℂ (fun ξ => fderiv ℝ (fun z => F z ξ) z₀ u) (ball 0 r₁) :=
  differentiableOn_partial_param (G := uncurryF F) hF isOpen_ball isOpen_ball
    (fun τ hτ => hhol τ hτ) hz₀ u

theorem differentiableOn_dZ (hF : ContDiff ℝ 2 (uncurryF F))
    (hhol : ∀ z ∈ ball (0 : ComplexModel n) δ, DifferentiableOn ℂ (F z) (ball 0 r₁))
    (hδ : 0 < δ) (v : ComplexModel n) : DifferentiableOn ℂ (dZ F v) (ball 0 r₁) := by
  have h0 : (0 : ComplexModel n) ∈ ball (0 : ComplexModel n) δ := mem_ball_self hδ
  exact ((differentiableOn_partial_left hF hhol h0 v).sub
    ((differentiableOn_partial_left hF hhol h0 (I • v)).const_smul I)).const_smul (2 : ℝ)⁻¹

theorem differentiableOn_dbarZ (hF : ContDiff ℝ 2 (uncurryF F))
    (hhol : ∀ z ∈ ball (0 : ComplexModel n) δ, DifferentiableOn ℂ (F z) (ball 0 r₁))
    (hδ : 0 < δ) (v : ComplexModel n) : DifferentiableOn ℂ (dbarZ F v) (ball 0 r₁) := by
  have h0 : (0 : ComplexModel n) ∈ ball (0 : ComplexModel n) δ := mem_ball_self hδ
  exact ((differentiableOn_partial_left hF hhol h0 v).add
    ((differentiableOn_partial_left hF hhol h0 (I • v)).const_smul I)).const_smul (2 : ℝ)⁻¹

theorem differentiableOn_levZ (hF : ContDiff ℝ 3 (uncurryF F))
    (hhol : ∀ z ∈ ball (0 : ComplexModel n) δ, DifferentiableOn ℂ (F z) (ball 0 r₁))
    (hδ : 0 < δ) (v : ComplexModel n) : DifferentiableOn ℂ (levZ F v) (ball 0 r₁) := by
  have hF2 : ContDiff ℝ 2 (uncurryF F) := hF.of_le (by norm_num)
  have h0 : (0 : ComplexModel n) ∈ ball (0 : ComplexModel n) δ := mem_ball_self hδ
  have hu : ∀ u : ComplexModel n, DifferentiableOn ℂ
      (fun ξ => fderiv ℝ (fderiv ℝ (uncurryF F)) (0, ξ) (u, 0) (u, 0)) (ball 0 r₁) := by
    intro u
    set Gu : ComplexModel n × ComplexModel n → ComplexModel n :=
      fun q => fderiv ℝ (uncurryF F) q (u, 0) with hGu
    have hGu2 : ContDiff ℝ 2 Gu :=
      (hF.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
    have hholu : ∀ z ∈ ball (0 : ComplexModel n) δ,
        DifferentiableOn ℂ (fun ξ => Gu (z, ξ)) (ball 0 r₁) := by
      intro z hz
      have e : (fun ξ => Gu (z, ξ)) = fun ξ => fderiv ℝ (fun z => F z ξ) z u := by
        funext ξ
        rw [fderiv_partial_left (hF2.differentiable (by norm_num))]
      rw [e]
      exact differentiableOn_partial_left hF2 hhol hz u
    have h := differentiableOn_partial_param (G := Gu) hGu2 isOpen_ball isOpen_ball
      hholu h0 u
    have e2 : (fun ξ => fderiv ℝ (fun τ => Gu (τ, ξ)) 0 u) =
        fun ξ => fderiv ℝ (fderiv ℝ (uncurryF F)) (0, ξ) (u, 0) (u, 0) := by
      funext ξ
      exact fderiv_partial_left_apply_left hF2 0 ξ u u
    rwa [e2] at h
  exact ((hu v).add (hu (I • v))).const_smul (4 : ℝ)⁻¹

theorem fderiv_partial_left_zero (hz0 : ∀ z ∈ ball (0 : ComplexModel n) δ, F z 0 = z)
    {z : ComplexModel n} (hz : z ∈ ball (0 : ComplexModel n) δ) :
    fderiv ℝ (fun z => F z 0) z = ContinuousLinearMap.id ℝ (ComplexModel n) := by
  have hev : (fun z => F z 0) =ᶠ[𝓝 z] fun z => z := by
    filter_upwards [isOpen_ball.mem_nhds hz] with z' hz' using hz0 z' hz'
  rw [hev.fderiv_eq, fderiv_id']

theorem dbarZ_zero (hz0 : ∀ z ∈ ball (0 : ComplexModel n) δ, F z 0 = z) (hδ : 0 < δ)
    (v : ComplexModel n) : dbarZ F v 0 = 0 := by
  rw [dbarZ, fderiv_partial_left_zero hz0 (mem_ball_self hδ)]
  simp only [ContinuousLinearMap.id_apply, smul_smul, I_mul_I, neg_one_smul, add_neg_cancel,
    smul_zero]

theorem levZ_zero (hF : ContDiff ℝ 2 (uncurryF F))
    (hz0 : ∀ z ∈ ball (0 : ComplexModel n) δ, F z 0 = z) (hδ : 0 < δ)
    (v : ComplexModel n) : levZ F v 0 = 0 := by
  have hFd : Differentiable ℝ (uncurryF F) := hF.differentiable (by norm_num)
  have hu : ∀ u : ComplexModel n, fderiv ℝ (fderiv ℝ (uncurryF F)) (0, 0) (u, 0) (u, 0) = 0 := by
    intro u
    rw [← fderiv_partial_left_apply_left hF 0 0 u u]
    have hev : (fun z => fderiv ℝ (uncurryF F) (z, 0) (u, 0)) =ᶠ[𝓝 (0 : ComplexModel n)]
        fun _ => u := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hδ)] with z hz
      rw [← fderiv_partial_left hFd, fderiv_partial_left_zero hz0 hz]
      rfl
    rw [hev.fderiv_eq]
    simp
  simp [levZ, hu]

end Holo

/-! ### The curve family and its Wirtinger derivatives -/

/-- `c(τ, ζ) = F(τ v, (w₀ + τ η) ζ)`. -/
def lineCurve (F : ComplexModel n → ComplexModel n → ComplexModel n) (w₀ : ℂ) (v : ComplexModel n)
    (η : ℂ) : ℂ → ComplexModel n → ComplexModel n :=
  fun τ ζ => F (τ • v) ((w₀ + τ * η) • ζ)

/-- `mixZ(ξ)(e) = ½ (D²F((v,0),(0,e)) + D²F((iv,0),(0,ie)))` at `(0, ξ)`. -/
def mixZ (F : ComplexModel n → ComplexModel n → ComplexModel n) (v ξ e : ComplexModel n) :
    ComplexModel n :=
  (2 : ℝ)⁻¹ • (fderiv ℝ (fderiv ℝ (uncurryF F)) (0, ξ) (v, 0) (0, e) +
    fderiv ℝ (fderiv ℝ (uncurryF F)) (0, ξ) (I • v, 0) (0, I • e))

section LineCurve

variable {F : ComplexModel n → ComplexModel n → ComplexModel n} {w₀ η : ℂ} {v : ComplexModel n}

theorem lineCurve_eq_line (ζ : ComplexModel n) :
    (fun τ => lineCurve F w₀ v η τ ζ) =
      fun τ : ℂ => uncurryF F ((0, w₀ • ζ) + τ • (v, η • ζ)) := by
  funext τ
  simp only [lineCurve, uncurryF, Prod.smul_mk, Prod.mk_add_mk, zero_add, add_smul, mul_smul]

theorem pair_split (a b : ComplexModel n) :
    ((a, b) : ComplexModel n × ComplexModel n) = (a, 0) + (0, b) := by
  simp

theorem fderiv_lineCurve (hF : Differentiable ℝ (uncurryF F)) {ζ : ComplexModel n}
    (hξ : DifferentiableAt ℂ (F 0) (w₀ • ζ)) (t : ℂ) :
    fderiv ℝ (fun τ => lineCurve F w₀ v η τ ζ) 0 t =
      fderiv ℝ (fun z => F z (w₀ • ζ)) 0 (t • v) + (t * η) • fderiv ℂ (F 0) (w₀ • ζ) ζ := by
  rw [lineCurve_eq_line, fderiv_line_apply hF, Prod.smul_mk, pair_split (t • v), map_add,
    ← fderiv_partial_left hF, ← fderiv_partial_right hF,
    (hξ.hasFDerivAt.restrictScalars ℝ).fderiv]
  simp only [ContinuousLinearMap.coe_restrictScalars', smul_smul, map_smul]

theorem curveDzbar_lineCurve (hF : Differentiable ℝ (uncurryF F)) {ζ : ComplexModel n}
    (hξ : DifferentiableAt ℂ (F 0) (w₀ • ζ)) :
    curveDzbar (lineCurve F w₀ v η) ζ = dbarZ F v (w₀ • ζ) := by
  simp only [curveDzbar, dbarZ, fderiv_lineCurve hF hξ, one_smul, one_mul]
  congr 1
  rw [smul_add, smul_smul I (I * η), ← mul_assoc, I_mul_I, neg_one_mul, neg_smul]
  abel

theorem curveDz_lineCurve (hF : Differentiable ℝ (uncurryF F)) {ζ : ComplexModel n}
    (hξ : DifferentiableAt ℂ (F 0) (w₀ • ζ)) :
    curveDz (lineCurve F w₀ v η) ζ =
      dZ F v (w₀ • ζ) + η • fderiv ℂ (F 0) (w₀ • ζ) ζ := by
  simp only [curveDz, dZ, fderiv_lineCurve hF hξ, one_smul, one_mul]
  set A := fderiv ℝ (fun z => F z (w₀ • ζ)) 0 v
  set B := fderiv ℝ (fun z => F z (w₀ • ζ)) 0 (I • v)
  set w := fderiv ℂ (F 0) (w₀ • ζ) ζ
  have e1 : I • (B + (I * η) • w) = I • B - η • w := by
    rw [smul_add, smul_smul, ← mul_assoc, I_mul_I, neg_one_mul, neg_smul, sub_eq_add_neg]
  have e2 : A + η • w - (I • B - η • w) = (A - I • B) + (η • w + η • w) := by abel
  rw [e1, e2, smul_add, ← two_smul ℝ (η • w), smul_smul (2 : ℝ)⁻¹, inv_mul_cancel₀ two_ne_zero,
    one_smul]

theorem curveLevi_lineCurve (hF : ContDiff ℝ 2 (uncurryF F)) {ζ : ComplexModel n}
    (hξ : ContDiffAt ℂ 2 (F 0) (w₀ • ζ)) :
    curveLevi (lineCurve F w₀ v η) ζ = levZ F v (w₀ • ζ) + mixZ F v (w₀ • ζ) (η • ζ) := by
  have hs := (hF.contDiffAt (x := ((0 : ComplexModel n), w₀ • ζ))).isSymmSndFDerivAt (by simp)
  set D2 := fderiv ℝ (fderiv ℝ (uncurryF F)) ((0 : ComplexModel n), w₀ • ζ) with hD2
  have hξξ : ∀ e : ComplexModel n, D2 (0, e) (0, e) + D2 (0, I • e) (0, I • e) = 0 := by
    intro e
    rw [hD2, ← fderiv_fderiv_partial_right hF, ← fderiv_fderiv_partial_right hF,
      SGPT.NPP.DN2.fderiv2_real_I hξ, add_neg_cancel]
  simp only [curveLevi, levZ, mixZ]
  rw [lineCurve_eq_line, fderiv_fderiv_line_apply hF, fderiv_fderiv_line_apply hF]
  simp only [one_smul, Prod.smul_mk]
  rw [pair_split v (η • ζ), pair_split (I • v) (I • η • ζ)]
  simp only [map_add, add_apply]
  rw [← hD2]
  have h1 := hξξ (η • ζ)
  have h2 := hs (0, η • ζ) (v, 0)
  have h3 := hs (0, I • η • ζ) (I • v, 0)
  rw [← hD2] at h2 h3
  rw [h2, h3]
  have hx : D2 (0, I • η • ζ) (0, I • η • ζ) = -D2 (0, η • ζ) (0, η • ζ) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact h1
  rw [hx]
  module

end LineCurve

/-- **The mixed term is the derivative of `b`**: `mixZ(ξ)(e) = Db(ξ)(e)`, `b = ∂̄_v F(0, ·)`. -/
theorem mixZ_eq_fderiv {F : ComplexModel n → ComplexModel n → ComplexModel n} {δ r₁ : ℝ}
    (hF : ContDiff ℝ 2 (uncurryF F))
    (hhol : ∀ z ∈ ball (0 : ComplexModel n) δ, DifferentiableOn ℂ (F z) (ball 0 r₁))
    (hδ : 0 < δ) (v : ComplexModel n) {ξ : ComplexModel n} (hξ : ξ ∈ ball (0 : ComplexModel n) r₁)
    (e : ComplexModel n) : mixZ F v ξ e = fderiv ℂ (dbarZ F v) ξ e := by
  have hFd : Differentiable ℝ (uncurryF F) := hF.differentiable (by norm_num)
  have h0 : (0 : ComplexModel n) ∈ ball (0 : ComplexModel n) δ := mem_ball_self hδ
  set h₁ : ComplexModel n → ComplexModel n := fun ξ => fderiv ℝ (fun z => F z ξ) 0 v with hh₁
  set h₂ : ComplexModel n → ComplexModel n := fun ξ => fderiv ℝ (fun z => F z ξ) 0 (I • v)
    with hh₂
  have hd₁ : DifferentiableAt ℂ h₁ ξ :=
    (differentiableOn_partial_left hF hhol h0 v).differentiableAt (isOpen_ball.mem_nhds hξ)
  have hd₂ : DifferentiableAt ℂ h₂ ξ :=
    (differentiableOn_partial_left hF hhol h0 (I • v)).differentiableAt (isOpen_ball.mem_nhds hξ)
  have hb : dbarZ F v = fun ξ => (2 : ℝ)⁻¹ • (h₁ ξ + I • h₂ ξ) := rfl
  have hD : HasFDerivAt (dbarZ F v) ((2 : ℝ)⁻¹ • (fderiv ℂ h₁ ξ + I • fderiv ℂ h₂ ξ)) ξ := by
    rw [hb]
    exact (hd₁.hasFDerivAt.add (hd₂.hasFDerivAt.const_smul I)).const_smul (2 : ℝ)⁻¹
  have hR : ∀ (h : ComplexModel n → ComplexModel n) (u : ComplexModel n),
      (h = fun ξ => fderiv ℝ (fun z => F z ξ) 0 u) → DifferentiableAt ℂ h ξ → ∀ a,
      fderiv ℂ h ξ a = fderiv ℝ (fderiv ℝ (uncurryF F)) (0, ξ) (u, 0) (0, a) := by
    intro h u hu hd a
    have h1 : fderiv ℂ h ξ a = fderiv ℝ h ξ a := by
      rw [(hd.hasFDerivAt.restrictScalars ℝ).fderiv]; rfl
    rw [h1, ← fderiv_partial_left_apply_right hF]
    congr 2
    rw [hu]
    funext ξ'
    exact fderiv_partial_left hFd 0 ξ' u
  have hI : fderiv ℝ (fderiv ℝ (uncurryF F)) (0, ξ) (I • v, 0) (0, I • e) =
      I • fderiv ℝ (fderiv ℝ (uncurryF F)) (0, ξ) (I • v, 0) (0, e) := by
    rw [← hR h₂ (I • v) rfl hd₂ (I • e), ← hR h₂ (I • v) rfl hd₂ e, map_smul]
  rw [hD.fderiv]
  simp only [smul_apply, add_apply]
  rw [mixZ, hR h₁ v rfl hd₁ e, hR h₂ (I • v) rfl hd₂ e, hI]

end SGPT.NPP.DN4
