import Mathlib.Analysis.Distribution.FourierMultiplier
import SGPT.Foundations.Analysis.Pending.EllipticMeanValue
import SGPT.Foundations.Analysis.Pending.HolderInterpolation

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Solving `Δu - μu = f` for Schwartz data

Let `E` be a finite-dimensional real inner product space and `μ > 0`.  For every real Schwartz
function `f` there is a real Schwartz function `u` with `Δu - μu = f`
(`exists_laplacian_sub_eq`), where `Δu(x) = ∑ᵢ D²u(x)(bᵢ, bᵢ) = hessTrace b 1 (D²u x)` for any
orthonormal basis `b`.

The solution is the Fourier multiplier with the symbol `-(μ + 4π²|ξ|²)⁻¹` applied to `f`
(mathlib's `SchwartzMap.fourierMultiplierCLM`, `SchwartzMap.laplacian_eq_fourierMultiplierCLM`),
computed in `𝓢(E, ℂ)`; its real part is the real solution.

This is the constant-coefficient existence step L2.10 of the linear track for Yau's theorem: it starts the method of continuity that
solves `L u - μ u = f` on the whole space for the variable-coefficient operators of
`SchauderWholeSpace`, used by the parametrix on the compact manifold (blueprint
`bou:kahler-laplacian-solvability`).
-/

noncomputable section

open Set Filter Topology
open scoped SchwartzMap Real Laplacian LineDeriv ContDiff

namespace SGPT.Foundations.Analysis.Pending.SchwartzHelmholtz

open EllipticMeanValue SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Postcomposition with a continuous linear map -/

section Postcomp

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- `L ∘ f` for a Schwartz map `f` and a continuous linear map `L`. -/
def postcomp (L : F →L[ℝ] G) (f : 𝓢(E, F)) : 𝓢(E, G) where
  toFun := L ∘ f
  smooth' := L.contDiff.comp (f.smooth ⊤)
  decay' k n := by
    obtain ⟨C, -, hC⟩ := f.decay k n
    refine ⟨‖L‖ * C, fun x => ?_⟩
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (L ∘ f) x‖
        ≤ ‖x‖ ^ k * (‖L‖ * ‖iteratedFDeriv ℝ n f x‖) := by
          gcongr
          exact L.norm_iteratedFDeriv_comp_left ((f.smooth ⊤).contDiffAt)
            (by exact_mod_cast le_top)
      _ = ‖L‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by ring
      _ ≤ ‖L‖ * C := by gcongr; exact hC x

@[simp]
theorem postcomp_apply (L : F →L[ℝ] G) (f : 𝓢(E, F)) (x : E) : postcomp L f x = L (f x) := rfl

end Postcomp

/-! ### The symbol -/

/-- `ξ ↦ (1 + ‖s ξ‖²)⁻¹` has temperate growth. -/
theorem hasTemperateGrowth_inv_one_add (s : ℝ) :
    (fun ξ : E => (1 + ‖s • ξ‖ ^ 2) ^ (-1 : ℝ)).HasTemperateGrowth :=
  (Function.hasTemperateGrowth_one_add_norm_sq_rpow (H := E) (-1)).comp
    ((s • ContinuousLinearMap.id ℝ E).hasTemperateGrowth)

theorem fourierMultiplierCLM_add_apply [MeasurableSpace E] [BorelSpace E] {g₁ g₂ : E → ℝ}
    (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢(E, ℂ)) :
    fourierMultiplierCLM ℂ (g₁ + g₂) f =
      fourierMultiplierCLM ℂ g₁ f + fourierMultiplierCLM ℂ g₂ f := by
  simp only [fourierMultiplierCLM, smulLeftCLM_add hg₁ hg₂, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.add_comp, add_apply]

/-! ### The equation -/

/-- `Δv(x) = ∑ᵢ D²v(x)(bᵢ, bᵢ)` for a Schwartz map. -/
theorem laplacian_apply_eq_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (v : 𝓢(E, F)) (x : E) :
    (Δ v) x = ∑ i, fderiv ℝ (fderiv ℝ v) x (b i) (b i) := by
  rw [laplacian_eq_sum b, sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lineDerivOp_apply_eq_fderiv]
  have hfun : ((∂_{b i} v : 𝓢(E, F)) : E → F) = fun y => fderiv ℝ v y (b i) :=
    funext fun y => lineDerivOp_apply_eq_fderiv (b i) v y
  rw [hfun]
  have hd : DifferentiableAt ℝ (fderiv ℝ v) x :=
    ((v.smooth 2).fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- `D²(L ∘ w) = L ∘ D²w` for a continuous linear map `L`. -/
theorem fderiv_fderiv_comp_left {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : F →L[ℝ] G) {w : E → F} (hw : ContDiff ℝ 2 w)
    (x h k : E) :
    fderiv ℝ (fderiv ℝ (L ∘ w)) x h k = L (fderiv ℝ (fderiv ℝ w) x h k) := by
  have h1 := HolderInterpolation.iteratedFDeriv_two_apply_eq (L ∘ w) x ![h, k]
  have h2 := HolderInterpolation.iteratedFDeriv_two_apply_eq w x ![h, k]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
  rw [← h1, ← h2, L.iteratedFDeriv_comp_left hw.contDiffAt le_rfl]
  rfl

/-- **`Δ - μ` is onto on real Schwartz functions** (`μ > 0`): for every `f ∈ 𝓢(E, ℝ)` there is
`u ∈ 𝓢(E, ℝ)` with `∑ᵢ D²u(x)(bᵢ, bᵢ) - μ u(x) = f(x)`. -/
theorem exists_laplacian_sub_eq [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {μ : ℝ} (hμ : 0 < μ) (f : 𝓢(E, ℝ)) :
    ∃ u : 𝓢(E, ℝ), ∀ x, ∑ i, fderiv ℝ (fderiv ℝ u) x (b i) (b i) - μ * u x = f x := by
  set s : ℝ := 2 * π / Real.sqrt μ with hs
  set g : E → ℝ := fun ξ => (1 + ‖s • ξ‖ ^ 2) ^ (-1 : ℝ) with hg_def
  have hg : g.HasTemperateGrowth := hasTemperateGrowth_inv_one_add s
  have hsq : (fun ξ : E => ‖ξ‖ ^ 2).HasTemperateGrowth := Function.hasTemperateGrowth_norm_sq E
  set fC : 𝓢(E, ℂ) := postcomp Complex.ofRealCLM f with hfC
  set v : 𝓢(E, ℂ) := fourierMultiplierCLM ℂ g fC with hv
  -- the symbol identity `(4π²|ξ|² + μ) g(ξ) = μ`
  have hsym : ((2 * π) ^ 2 • ((fun ξ : E => ‖ξ‖ ^ 2) * g) + μ • g) = fun _ => μ := by
    funext ξ
    simp only [hg_def, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    have hsμ : s ^ 2 * μ = (2 * π) ^ 2 := by
      rw [hs, div_pow, Real.sq_sqrt hμ.le]; field_simp
    simp only [Real.rpow_neg_one, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hpos : 0 < 1 + s ^ 2 * ‖ξ‖ ^ 2 := by positivity
    field_simp
    nlinarith [hsμ]
  have hgsq : ((fun ξ : E => ‖ξ‖ ^ 2) * g).HasTemperateGrowth := hsq.mul hg
  -- `Δ v - μ v = -μ fC`
  have key : Δ v - μ • v = -(μ • fC) := by
    rw [laplacian_eq_fourierMultiplierCLM, hv,
      fourierMultiplierCLM_fourierMultiplierCLM_apply hsq hg]
    have h1 : (((2 * π) ^ 2 : ℝ) • ((fun ξ : E => ‖ξ‖ ^ 2) * g)).HasTemperateGrowth := by
      fun_prop
    have h2 : (μ • g).HasTemperateGrowth := by fun_prop
    have hadd := fourierMultiplierCLM_add_apply h1 h2 fC
    rw [hsym, fourierMultiplierCLM_const, fourierMultiplierCLM_smul hgsq,
      fourierMultiplierCLM_smul hg] at hadd
    simp only [smul_apply, ContinuousLinearMap.id_apply] at hadd
    rw [neg_smul, sub_eq_add_neg, ← neg_add, hadd]
  -- the real part of `w = -μ⁻¹ v`
  set w : 𝓢(E, ℂ) := (-μ⁻¹ : ℝ) • v with hw
  have hkey : Δ w - μ • w = fC := by
    have hΔ : Δ w = (-μ⁻¹ : ℝ) • Δ v := by
      rw [← laplacianCLM_eq', ← laplacianCLM_eq', hw, map_smul]
    rw [hΔ, hw, smul_comm μ (-μ⁻¹ : ℝ) v, ← smul_sub, key, smul_neg, smul_smul,
      neg_mul, inv_mul_cancel₀ hμ.ne', neg_smul, one_smul, neg_neg]
  refine ⟨postcomp Complex.reCLM w, fun x => ?_⟩
  have hw2 : ContDiff ℝ 2 (⇑w) := w.smooth 2
  have hcoe : (⇑(postcomp Complex.reCLM w) : E → ℝ) = Complex.reCLM ∘ ⇑w := rfl
  rw [hcoe, Finset.sum_congr rfl fun i _ => fderiv_fderiv_comp_left Complex.reCLM hw2 x (b i) (b i),
    ← map_sum, ← laplacian_apply_eq_sum b w x]
  have hx := congrArg (fun F : 𝓢(E, ℂ) => F x) hkey
  simp only [sub_apply, smul_apply, hfC, postcomp_apply] at hx
  have := congrArg Complex.re hx
  simpa [Complex.sub_re, Complex.smul_re] using this

/-- **`Δ - μ` on smooth compactly supported data** (`μ > 0`): the solution is smooth with all
derivatives bounded. -/
theorem exists_contDiff_laplacian_sub_eq [MeasurableSpace E] [BorelSpace E] {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι ℝ E) {μ : ℝ} (hμ : 0 < μ) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∃ u : E → ℝ, ContDiff ℝ ∞ u ∧ (∀ n : ℕ, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n u x‖ ≤ C) ∧
      ∀ x, hessTrace b (ContinuousLinearMap.id ℝ E) (fderiv ℝ (fderiv ℝ u) x) - μ * u x = f x := by
  obtain ⟨u, hu⟩ := exists_laplacian_sub_eq b hμ (hfc.toSchwartzMap hf)
  refine ⟨u, u.smooth ⊤, fun n => ?_, fun x => ?_⟩
  · obtain ⟨C, -, hC⟩ := u.decay 0 n
    exact ⟨C, fun x => by simpa using hC x⟩
  · simpa [hessTrace] using hu x

end SGPT.Foundations.Analysis.Pending.SchwartzHelmholtz
