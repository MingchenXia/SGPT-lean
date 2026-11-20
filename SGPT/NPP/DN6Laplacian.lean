import SGPT.NPP.DN6Pairing
import SGPT.NPP.DN3RadialConvex
import SGPT.NPP.DN5Smoothing

/-!
# The second-order coefficient of the smoothing is the metric Laplacian

Lane DN6 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`, Step 7: "The first moments of the
radial weight vanish, and so do the moments `∫ ζ_i ζ_j χ(|ζ|²) dζ`, by the substitution
`ζ ↦ e^{it} ζ`; by symmetry, `∫ ζ_i ζ̄_j χ(|ζ|²) dζ = a_χ δ_{ij}`.  For smooth `g`, the
second-order Taylor expansion of `g(F(x, rζ))` … gives `Ψ_g(x, r) = g(x) + a_χ r² Σ h^{ij̄} g_{ij̄}(x)
+ O(r³)`").

For a map `G(z, η)` that is holomorphic in `η` near `0` with `G(z, 0) = z`, `D_η G(z, 0) = id`, and
the weight `k(z, ξ) = χ(|ξ|²_ω) / ∫ χ(|·|²_ω)` of lane DN5 (`SGPT.NPP.DN5.fibreWeight`), the
second-order coefficient of the weighted average of `h ∘ G` is `a Δ_ω h(z)` with
`a = ∫ -χ₁(‖ζ‖²) dζ > 0` (`weightSecondCoeff_eq_chartLaplacian`).  Steps:

* `fderiv2_line_eq`, `fderiv2_comp_apply`: second derivatives along lines and their chain rule;
* `fderiv2_I_smul`: holomorphy in `η` makes the quadratic part `Q(ξ) = D²_ηG(z, 0)(ξ, ξ)` satisfy
  `Q(iξ) = -Q(ξ)`, so its average against the rotation-invariant kernel vanishes;
* `integral_quad_mul_kernel`: second moments via the radial slope formula of lane DN3
  (`DN3.slope_integral_eq`) applied to the quadratic form;
* the normalizing frame of lane DN5 (`IsNormalizingFrame`) and the congruence invariance of
  `tr(H⁻¹ K)` (`KahlerLaplacianChart.trace_inv_mul_congr`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Matrix

namespace SGPT.NPP.DN6

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending KahlerLaplacianChart

/-! ### Second derivatives along lines -/

section Line

variable {P Q F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q]
  [NormedSpace ℝ Q] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasDerivAt_line_fderiv' {A : P → F} (hA : Differentiable ℝ (fderiv ℝ A)) (c v : P)
    (s : ℝ) :
    HasDerivAt (fun s : ℝ => fderiv ℝ A (c + s • v) v)
      (fderiv ℝ (fderiv ℝ A) (c + s • v) v v) s := by
  have h : HasDerivAt (fun s : ℝ => fderiv ℝ A (c + s • v))
      (fderiv ℝ (fderiv ℝ A) (c + s • v) v) s :=
    (hA (c + s • v)).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_lineMap c v s)
  exact (ContinuousLinearMap.apply ℝ F v).hasFDerivAt.comp_hasDerivAt s h

/-- **Second derivatives along lines**: if `f₁(c₁ + s v₁) = κ f₂(c₂ + s v₂)` for all `s`, then
`D²f₁(c₁)(v₁, v₁) = κ D²f₂(c₂)(v₂, v₂)`. -/
theorem fderiv2_line_eq {f₁ : P → ℝ} {f₂ : Q → ℝ} (h₁ : ContDiff ℝ 2 f₁) (h₂ : ContDiff ℝ 2 f₂)
    (c₁ v₁ : P) (c₂ v₂ : Q) (κ : ℝ) (h : ∀ s : ℝ, f₁ (c₁ + s • v₁) = κ * f₂ (c₂ + s • v₂)) :
    fderiv ℝ (fderiv ℝ f₁) c₁ v₁ v₁ = κ * fderiv ℝ (fderiv ℝ f₂) c₂ v₂ v₂ := by
  have hd1 : Differentiable ℝ f₁ := h₁.differentiable (by norm_num)
  have hd2 : Differentiable ℝ f₂ := h₂.differentiable (by norm_num)
  have hdd1 : Differentiable ℝ (fderiv ℝ f₁) :=
    (h₁.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hdd2 : Differentiable ℝ (fderiv ℝ f₂) :=
    (h₂.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hfun : (fun s : ℝ => f₁ (c₁ + s • v₁)) = fun s => κ * f₂ (c₂ + s • v₂) := funext h
  have hfirst : ∀ s : ℝ, fderiv ℝ f₁ (c₁ + s • v₁) v₁ = κ * fderiv ℝ f₂ (c₂ + s • v₂) v₂ := by
    intro s
    have e1 := hasDerivAt_line hd1 c₁ v₁ s
    have e2 := (hasDerivAt_line hd2 c₂ v₂ s).const_mul κ
    rw [hfun] at e1
    exact e1.unique e2
  have e1 := hasDerivAt_line_fderiv hdd1 c₁ v₁ 0
  have e2 := (hasDerivAt_line_fderiv hdd2 c₂ v₂ 0).const_mul κ
  have hfun' : (fun s : ℝ => fderiv ℝ f₁ (c₁ + s • v₁) v₁) =
      fun s => κ * fderiv ℝ f₂ (c₂ + s • v₂) v₂ := funext hfirst
  rw [hfun'] at e1
  simpa using e1.unique e2

/-- **The chain rule for second derivatives along a direction.** -/
theorem fderiv2_comp_apply {h : Q → ℝ} {G : P → Q} (hh : ContDiff ℝ 2 h) (hG : ContDiff ℝ 2 G)
    (c v : P) :
    fderiv ℝ (fderiv ℝ (h ∘ G)) c v v =
      fderiv ℝ (fderiv ℝ h) (G c) (fderiv ℝ G c v) (fderiv ℝ G c v) +
        fderiv ℝ h (G c) (fderiv ℝ (fderiv ℝ G) c v v) := by
  have hhd : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hhdd : Differentiable ℝ (fderiv ℝ h) :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hGdd : Differentiable ℝ (fderiv ℝ G) :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hhG : ContDiff ℝ 2 (h ∘ G) := hh.comp hG
  have hhGdd : Differentiable ℝ (fderiv ℝ (h ∘ G)) :=
    (hhG.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  -- the first derivative along the line, two ways
  have hfirst : (fun s : ℝ => fderiv ℝ (h ∘ G) (c + s • v) v) =
      fun s => fderiv ℝ h (G (c + s • v)) (fderiv ℝ G (c + s • v) v) := by
    funext s
    rw [fderiv_comp _ (hhd _) (hGd _)]
    rfl
  have e1 := hasDerivAt_line_fderiv hhGdd c v 0
  rw [hfirst] at e1
  have hγ : HasDerivAt (fun s : ℝ => G (c + s • v)) (fderiv ℝ G (c + (0 : ℝ) • v) v) 0 :=
    (hGd _).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_lineMap c v 0)
  have hL : HasDerivAt (fun s : ℝ => fderiv ℝ h (G (c + s • v)))
      (fderiv ℝ (fderiv ℝ h) (G (c + (0 : ℝ) • v)) (fderiv ℝ G (c + (0 : ℝ) • v) v)) 0 :=
    (hhdd _).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ
  have hw := hasDerivAt_line_fderiv' hGdd c v 0
  have e2 := hL.clm_apply hw
  simp only [zero_smul, add_zero] at e1 e2
  exact e1.unique e2

end Line

/-! ### Holomorphy kills the quadratic part -/

section Holo

variable {N : ℕ}

local notation "E" => ComplexModel N

/-- **Holomorphy in `η`**: `Q(iξ) = -Q(ξ)` for `Q(ξ) = D²G(z, 0)((0, ξ), (0, ξ))`. -/
theorem fderiv2_I_smul {G : E × E → E} (hG : ContDiff ℝ 2 G) {z : E}
    (hhol : ∀ᶠ η in 𝓝 (0 : E), DifferentiableAt ℂ (fun η => G (z, η)) η) (ξ : E) :
    fderiv ℝ (fderiv ℝ G) (z, 0) (0, Complex.I • ξ) (0, Complex.I • ξ) =
      -fderiv ℝ (fderiv ℝ G) (z, 0) (0, ξ) (0, ξ) := by
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hGdd : Differentiable ℝ (fderiv ℝ G) :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  set D2 := fderiv ℝ (fderiv ℝ G) (z, 0) with hD2
  -- `ℂ`-linearity of the partial derivative near `0`
  have hlin : ∀ u : E, (fun η : E => fderiv ℝ G (z, η) (0, Complex.I • u)) =ᶠ[𝓝 0]
      fun η => Complex.I • fderiv ℝ G (z, η) (0, u) := by
    intro u
    filter_upwards [hhol] with η hη
    have hpart : fderiv ℝ (fun η => G (z, η)) η =
        (fderiv ℝ G (z, η)).comp (ContinuousLinearMap.inr ℝ E E) :=
      ((hGd (z, η)).hasFDerivAt.comp η (hasFDerivAt_prodMk_right z η)).fderiv
    have hres := hη.fderiv_restrictScalars ℝ
    have h1 : fderiv ℝ (fun η => G (z, η)) η (Complex.I • u) =
        Complex.I • fderiv ℝ (fun η => G (z, η)) η u := by
      rw [hres]
      simp only [ContinuousLinearMap.coe_restrictScalars', map_smul]
    rw [hpart] at h1
    simpa using h1
  -- differentiate at `0`
  have hd : HasFDerivAt (fun η : E => fderiv ℝ G (z, η))
      (D2.comp (ContinuousLinearMap.inr ℝ E E)) 0 :=
    (hGdd (z, 0)).hasFDerivAt.comp (0 : E) (hasFDerivAt_prodMk_right z 0)
  have hw : ∀ w u : E, D2 (0, w) (0, Complex.I • u) = Complex.I • D2 (0, w) (0, u) := by
    intro w u
    have h1 : HasFDerivAt (fun η : E => fderiv ℝ G (z, η) (0, Complex.I • u))
        ((ContinuousLinearMap.apply ℝ E ((0 : E), Complex.I • u)).comp
          (D2.comp (ContinuousLinearMap.inr ℝ E E))) 0 :=
      (ContinuousLinearMap.apply ℝ E ((0 : E), Complex.I • u)).hasFDerivAt.comp 0 hd
    have h2 : HasFDerivAt (fun η : E => Complex.I • fderiv ℝ G (z, η) (0, u))
        (Complex.I • (ContinuousLinearMap.apply ℝ E ((0 : E), u)).comp
          (D2.comp (ContinuousLinearMap.inr ℝ E E))) 0 :=
      ((ContinuousLinearMap.apply ℝ E ((0 : E), u)).hasFDerivAt.comp 0 hd).const_smul
        Complex.I
    have h3 := (h2.congr_of_eventuallyEq (hlin u)).unique h1
    have h4 := congrArg (fun L => L w) h3
    simpa using h4.symm
  have hsymm : ∀ a b : E × E, D2 a b = D2 b a := by
    have h := (hG.contDiffAt (x := (z, 0))).isSymmSndFDerivAt (by simp)
    intro a b
    exact h a b
  calc D2 (0, Complex.I • ξ) (0, Complex.I • ξ)
      = Complex.I • D2 (0, Complex.I • ξ) (0, ξ) := hw _ _
    _ = Complex.I • D2 (0, ξ) (0, Complex.I • ξ) := by rw [hsymm (0, Complex.I • ξ) (0, ξ)]
    _ = Complex.I • Complex.I • D2 (0, ξ) (0, ξ) := by rw [hw]
    _ = -D2 (0, ξ) (0, ξ) := by rw [smul_smul, Complex.I_mul_I, neg_one_smul]

end Holo

/-! ### Second moments of the radial kernel -/

section Moments

variable {N : ℕ}

open SGPT.Envelopes.LapClass in
/-- **Second moments** (FPT: `∫ ζ_i ζ̄_j χ(|ζ|²) dζ = a_χ δ_{ij}`, `∫ ζ_i ζ_j χ = 0`), via the radial
slope formula of lane DN3 applied to the quadratic form `q(s) = ½ B(s, s)`:
`∫ B(s, s) χ(‖s‖²) ds = 2 c_B ∫ -χ₁(‖ζ‖²) dζ`, `c_B = Σ_p (B(e_p, e_p) + B(ie_p, ie_p))/4`. -/
theorem integral_quad_mul_kernel (B : ComplexModel N →L[ℝ] ComplexModel N →L[ℝ] ℝ) :
    ∫ s, B s s * DN3.kernel N s =
      2 * (∑ p, (B (coordinateVector p) (coordinateVector p) +
        B (Complex.I • coordinateVector p) (Complex.I • coordinateVector p)) / 4) *
        ∫ ζ : ComplexModel N, -DN3.chiOne N (‖ζ‖ ^ 2) := by
  set q : ComplexModel N → ℝ := fun y => (1 / 2 : ℝ) * B y y with hqdef
  set L : ComplexModel N →L[ℝ] ComplexModel N →L[ℝ] ℝ := (1 / 2 : ℝ) • (B + B.flip) with hLdef
  have hq : ∀ y, HasFDerivAt q (L y) y := by
    intro y
    have h := (B.hasFDerivAt_of_bilinear (hasFDerivAt_id y) (hasFDerivAt_id y)).const_mul
      (1 / 2 : ℝ)
    refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    simp [hLdef]
  have hfq : fderiv ℝ q = fun y => L y := funext fun y => (hq y).fderiv
  have hffq : ∀ y, fderiv ℝ (fderiv ℝ q) y = L := fun y => by
    rw [hfq]; exact L.fderiv
  have hqc : ContDiff ℝ 2 q := by
    have h : ContDiff ℝ 2 fun y : ComplexModel N => B y y :=
      B.isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id)
    exact contDiff_const.mul h
  have hslope := DN3.slope_integral_eq hqc 1
  have hLv : ∀ v, L v v = B v v := fun v => by simp [hLdef]; ring
  have hlev : ∀ y, levTr q y = ∑ p, (B (coordinateVector p) (coordinateVector p) +
      B (Complex.I • coordinateVector p) (Complex.I • coordinateVector p)) / 4 := by
    intro y
    simp only [levTr, leviForm, realHessian_eq_fderiv, hffq, hLv]
  simp only [one_smul, one_pow, mul_one, one_mul, hfq, hLv, hlev] at hslope
  rw [hslope, integral_const_mul]
  ring

end Moments

/-! ### The identification -/

section Ident

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

local notation "E" => ComplexModel N

open SGPT.Envelopes.LapClass HolomorphicMixedDensity in
/-- The flat trace of the pullback by a normalizing frame is the metric Laplacian. -/
theorem levTr_frame_eq_chartLaplacian (wY : KahlerBackground N Y) (e : ComplexChart N Y)
    {z : E} (hz : z ∈ e.val.target) {L : E ≃L[ℂ] E} (hL : DN5.IsNormalizingFrame wY e z L)
    {h : E → ℝ} (hh : ContDiff ℝ 2 h) :
    levTr (fun s => h (z + L s)) 0 = chartLaplacian wY.form.val e h z := by
  set F : E → E := fun s => z + L s with hFdef
  have hFc : ContDiff ℂ ∞ F := contDiff_const.add (L : E →L[ℂ] E).contDiff
  have hgL : ContDiff ℝ 2 (fun s => h (z + L s)) :=
    hh.comp (contDiff_const.add ((L : E →L[ℂ] E).restrictScalars ℝ).contDiff)
  set S : E →ₗ[ℂ] E := (L : E →L[ℂ] E).toLinearMap with hSdef
  have hJ : jacobianMatrix F 0 = standardMatrix S := by
    ext a j
    have hd : fderiv ℝ F 0 = (L : E →L[ℂ] E).restrictScalars ℝ := by
      rw [hFdef]
      rw [fderiv_const_add]
      exact ((L : E →L[ℂ] E).restrictScalars ℝ).fderiv
    simp [jacobianMatrix, hd, standardMatrix_apply, hSdef]
  have hHess : complexHessian (fun s => h (F s)) 0 =
      (standardMatrix S)ᵀ * complexHessian h z * (standardMatrix S).map (starRingEnd ℂ) := by
    have h1 := HolomorphicHessianTwo.complexHessian_comp_holomorphic_two (U := univ) (V := univ)
      isOpen_univ isOpen_univ hFc.contDiffOn hh.contDiffOn (mapsTo_univ _ _) (mem_univ (0 : E))
    rw [h1, hJ]
    simp [hFdef]
  have hA := (wY.isKahler.1 e z hz).1
  have hflat : compLinearMap (wY.form.val.coeff e z) S = SGPT.Analysis.KahlerNormal.flatForm N := by
    refine ContinuousAlternatingMap.ext fun v => ?_
    have hv : v = ![v 0, v 1] := by
      funext i; fin_cases i <;> rfl
    rw [hv, compLinearMap_apply]
    exact hL (v 0) (v 1)
  have hcong := normalizedHermitianMatrix_compLinearMap hA S
  rw [hflat, SGPT.Analysis.KahlerNormal.normalizedHermitianMatrix_flatForm] at hcong
  have hdet : IsUnit (standardMatrix S).det := by
    rw [det_standardMatrix]
    exact (L.toLinearEquiv).isUnit_det'
  have htr := trace_inv_mul_congr (H := normalizedHermitianMatrix (wY.form.val.coeff e z))
    (K := complexHessian h z) hdet
  rw [← hcong, inv_one, one_mul] at htr
  rw [← re_trace_complexHessian hgL.contDiffAt]
  change (complexHessian (fun s => h (F s)) 0).trace.re = _
  rw [hHess, htr]
  rfl

/-- **The second-order coefficient is the metric Laplacian** (FPT `lem:chern-joint-smoothing`,
Step 7): for `G` holomorphic in `η` near `(z, 0)` with `G(z, 0) = z`, `D_ηG(z, 0) = id`, and the
weight `k(z, ·) = χ(|·|²_ω) / ∫ χ(|·|²_ω)` at `z`,
`½ ∫ k(z, ξ) D²(h ∘ G)(z, 0)((0, ξ), (0, ξ)) dξ = a Δ_ω h(z)` with `a = ∫ -χ₁(‖ζ‖²) dζ`. -/
theorem weightSecondCoeff_eq_chartLaplacian (wY : KahlerBackground N Y) (e : ComplexChart N Y)
    {z : E} (hz : z ∈ e.val.target) {G : E × E → E} (hG : ContDiff ℝ 2 G) (hG0 : G (z, 0) = z)
    (hGη : fderiv ℝ (fun η => G (z, η)) 0 = ContinuousLinearMap.id ℝ E)
    (hhol : ∀ᶠ η in 𝓝 (0 : E), DifferentiableAt ℂ (fun η => G (z, η)) η)
    {k : E × E → ℝ} (hk : ContDiff ℝ 2 k)
    (hkz : ∀ ξ, k (z, ξ) = DN5.fibreWeight wY e z ξ / ∫ ξ, DN5.fibreWeight wY e z ξ)
    {h : E → ℝ} (hh : ContDiff ℝ 2 h) :
    weightSecondCoeff volume (compWeight G k h) z =
      (∫ ζ : E, -DN3.chiOne N (‖ζ‖ ^ 2)) * chartLaplacian wY.form.val e h z := by
  have hA : ContDiff ℝ 2 (compWeight G k h) :=
    (hh.comp (hG.comp contDiff_fst)).mul (hk.comp ((contDiff_fst.comp contDiff_fst).prodMk
      contDiff_snd))
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  -- the weighted second derivative
  have hpD2 : ∀ ξ : E, pD2 (compWeight G k h) (z, 0) ξ (0, ξ) (0, ξ) =
      k (z, ξ) * fderiv ℝ (fderiv ℝ (h ∘ G)) (z, 0) (0, ξ) (0, ξ) := by
    intro ξ
    refine fderiv2_line_eq (contDiff_slice hA ξ) (hh.comp hG) (z, 0) (0, ξ) (z, 0) (0, ξ) _
      fun s => ?_
    simp only [compWeight, Function.comp_apply, prod_add_smul, Prod.fst_add, smul_zero, add_zero]
    ring
  -- the chain rule
  have hDG : ∀ ξ : E, fderiv ℝ G (z, 0) (0, ξ) = ξ := by
    intro ξ
    have h1 : fderiv ℝ (fun η => G (z, η)) 0 =
        (fderiv ℝ G (z, 0)).comp (ContinuousLinearMap.inr ℝ E E) :=
      ((hGd (z, 0)).hasFDerivAt.comp (0 : E) (hasFDerivAt_prodMk_right z 0)).fderiv
    have h2 := congrArg (fun L => L ξ) h1
    simp only [hGη, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply] at h2
    exact h2.symm
  set Q : E → E := fun ξ => fderiv ℝ (fderiv ℝ G) (z, 0) (0, ξ) (0, ξ) with hQdef
  have hcomp : ∀ ξ : E, fderiv ℝ (fderiv ℝ (h ∘ G)) (z, 0) (0, ξ) (0, ξ) =
      fderiv ℝ (fderiv ℝ h) z ξ ξ + fderiv ℝ h z (Q ξ) := by
    intro ξ
    rw [fderiv2_comp_apply hh hG, hDG, hG0]
  have hQI : ∀ ξ : E, Q (Complex.I • ξ) = -Q ξ := fderiv2_I_smul hG hhol
  -- the normalizing frame
  obtain ⟨L, hL⟩ := DN5.exists_normalizingFrame wY hz
  set T : E ≃L[ℝ] E := L.restrictScalars ℝ with hTdef
  have hm : ∫ ξ, DN5.fibreWeight wY e z ξ =
      |LinearMap.det T.toLinearEquiv.toLinearMap| := DN5.integral_fibreWeight hL
  have hdet0 : 0 < |LinearMap.det T.toLinearEquiv.toLinearMap| := DN5.abs_det_pos T
  set F : E → ℝ := fun ξ => fderiv ℝ (fderiv ℝ h) z ξ ξ + fderiv ℝ h z (Q ξ) with hFdef
  have hsub : ∫ ξ, pD2 (compWeight G k h) (z, 0) ξ (0, ξ) (0, ξ) =
      ∫ s, DN3.kernel N s * F (L s) := by
    have e1 : (fun ξ => pD2 (compWeight G k h) (z, 0) ξ (0, ξ) (0, ξ)) =
        fun ξ => (∫ ξ, DN5.fibreWeight wY e z ξ)⁻¹ * (DN5.fibreWeight wY e z ξ * F ξ) := by
      funext ξ
      rw [hpD2, hcomp, hkz]
      simp only [hFdef]
      ring
    rw [e1, integral_const_mul,
      DN5.integral_eq_abs_det_mul_integral_comp T (fun ξ => DN5.fibreWeight wY e z ξ * F ξ), hm,
      ← mul_assoc, inv_mul_cancel₀ hdet0.ne', one_mul]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only
    have : T s = L s := rfl
    rw [this, DN5.fibreWeight_frame hL]
  -- the holomorphic quadratic part averages out
  have hQ0 : ∫ s, DN3.kernel N s * fderiv ℝ h z (Q (L s)) = 0 := by
    have hrot := DN3.integral_rotate_mul_kernel (fun s => fderiv ℝ h z (Q (L s))) Complex.I
      (by simp)
    have hodd : ∀ s : E, fderiv ℝ h z (Q (L (Complex.I • s))) = -fderiv ℝ h z (Q (L s)) := by
      intro s
      rw [L.map_smul, hQI, map_neg]
    simp only [hodd, neg_mul, integral_neg] at hrot
    have : ∫ s, fderiv ℝ h z (Q (L s)) * DN3.kernel N s =
        ∫ s, DN3.kernel N s * fderiv ℝ h z (Q (L s)) :=
      integral_congr_ae (Eventually.of_forall fun s => mul_comm _ _)
    rw [this] at hrot
    linarith
  -- integrability
  have hkc : Continuous (DN3.kernel N) := (DN3.contDiff_kernel N).continuous
  have hks : HasCompactSupport (DN3.kernel N) := DN3.hasCompactSupport_kernel
  have hD2c : Continuous fun s : E => fderiv ℝ (fderiv ℝ h) z (L s) (L s) :=
    ((continuous_const.clm_apply (L.continuous)).clm_apply L.continuous)
  have hQc : Continuous Q := by
    have hGdd : Continuous (fderiv ℝ (fderiv ℝ G)) :=
      (hG.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
    exact (continuous_const.clm_apply (continuous_const.prodMk continuous_id)).clm_apply
      (continuous_const.prodMk continuous_id)
  have hi1 : Integrable (fun s => DN3.kernel N s * fderiv ℝ (fderiv ℝ h) z (L s) (L s)) :=
    (hkc.mul hD2c).integrable_of_hasCompactSupport hks.mul_right
  have hi2 : Integrable (fun s => DN3.kernel N s * fderiv ℝ h z (Q (L s))) :=
    (hkc.mul ((continuous_const.clm_apply (hQc.comp L.continuous)))).integrable_of_hasCompactSupport
      hks.mul_right
  -- the second moments
  set B : E →L[ℝ] E →L[ℝ] ℝ := (fderiv ℝ (fderiv ℝ h) z).bilinearComp
    ((L : E →L[ℂ] E).restrictScalars ℝ) ((L : E →L[ℂ] E).restrictScalars ℝ) with hBdef
  have hmom := integral_quad_mul_kernel B
  have hgL : ContDiff ℝ 2 (fun s => h (z + L s)) :=
    hh.comp (contDiff_const.add ((L : E →L[ℂ] E).restrictScalars ℝ).contDiff)
  have hcB : (∑ p, (B (coordinateVector p) (coordinateVector p) +
        B (Complex.I • coordinateVector p) (Complex.I • coordinateVector p)) / 4) =
      SGPT.Envelopes.LapClass.levTr (fun s => h (z + L s)) 0 := by
    simp only [SGPT.Envelopes.LapClass.levTr, leviForm, realHessian_eq_fderiv]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hline : ∀ v : E, fderiv ℝ (fderiv ℝ (fun s => h (z + L s))) 0 v v = B v v := by
      intro v
      have := fderiv2_line_eq hgL hh 0 v z (L v) 1 fun s => by
        simp only [zero_add, one_mul]
        show h (z + (L : E →L[ℂ] E) (s • v)) = h (z + s • (L : E →L[ℂ] E) v)
        rw [ContinuousLinearMap.map_smul_of_tower]
      rw [this, one_mul]
      rfl
    rw [hline, hline]
  rw [weightSecondCoeff, hsub]
  have e2 : (fun s => DN3.kernel N s * F (L s)) = fun s =>
      DN3.kernel N s * fderiv ℝ (fderiv ℝ h) z (L s) (L s) +
        DN3.kernel N s * fderiv ℝ h z (Q (L s)) := by
    funext s; simp only [hFdef]; ring
  rw [e2, integral_add hi1 hi2, hQ0, add_zero]
  have e3 : ∫ s, DN3.kernel N s * fderiv ℝ (fderiv ℝ h) z (L s) (L s) =
      ∫ s, B s s * DN3.kernel N s :=
    integral_congr_ae (Eventually.of_forall fun s => by simp only [hBdef]; rw [mul_comm]; rfl)
  rw [e3, hmom, hcB, levTr_frame_eq_chartLaplacian wY e hz hL hh]
  ring

end Ident

end SGPT.NPP.DN6
