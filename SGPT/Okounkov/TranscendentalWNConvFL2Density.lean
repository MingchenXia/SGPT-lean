import SGPT.Okounkov.TranscendentalWNConvFLStatement
import SGPT.Okounkov.TranscendentalWNKeyLSCSlice

/-!
# Fibre volumes through a parametrization

Blueprint `claude-tok-wn-fl2`, nodes `tok-wn-fl2:density-bound` and `tok-wn-fl2:param-bound`;
source D. Witt Nyström, arXiv:2103.03660 (WN21), §7, estimate (eqeq)
(`references/wn21-restricted-volume`).

Let `s : X → 𝒳` be holomorphic, `Θ` a closed real `(1,1)`-form on `𝒳` and `ω` a Kähler
background of the compact manifold `X` (dimension `n`).  The measure
`topFormMeasure ω (s^*Θ)ⁿ` (density of `(s^*Θ)ⁿ` against Lebesgue measure in charts, truncated
at `0`) is estimated through an arbitrary smooth parametrization `γ : ℂⁿ ⊇ O → X` of a piece of
`X`, with `s ∘ γ = g`:

* `abs_topDensity_formPower_comp_le` (`tok-wn-fl2:density-bound`): for a real two-form `a` on
  `ℂᴺ` and a real-linear `L : ℂⁿ → ℂᴺ`,
  `|density of (L^*a)ⁿ| ≤ ‖aⁿ‖ · ‖L‖^{2n}` (`aⁿ` the exterior power, as a `2n`-form on `ℂᴺ`);
* `topFormMeasure_image_le` (`tok-wn-fl2:param-bound`): if
  `‖(Θⁿ)_d(d(g y))‖ · ‖D(d ∘ g)(y)‖^{2n} ≤ M` on a measurable `Y ⊆ O` on which `γ` is injective,
  then `topFormMeasure ω (s^*Θ)ⁿ (γ(Y)) ≤ M · vol(Y)`.  The proof is the chart formula of
  `topFormMeasure`, the change of variables `ζ = e(γ(y))` and the Jacobian law of the
  top-degree density.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.Okounkov.TranscendentalWN.FL2

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.TopDegreeDensity
open SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
open SGPT.Foundations.Analysis.Pending.ProductTestForms
open SGPT.Okounkov.TranscendentalWN

/-! ### The pointwise density bound -/

section Pointwise

variable {n N : ℕ}

/-- Pullback along a real-linear map commutes with powers of a two-form. -/
theorem formPower_comp (L : ComplexModel n →L[ℝ] ComplexModel N) (β : RealForm N 2) :
    ∀ q, (formPower β q).compContinuousLinearMap L = formPower (β.compContinuousLinearMap L) q
  | 0 => by
    rw [formPower_zero, formPower_zero, coordinateWedgeUnit_compContinuousLinearMap]
  | q + 1 => by
    rw [formPower_succ, formPower_succ, MongeAmpere.coordinateWedge_compContinuousLinearMap,
      formPower_comp L β q]

/-- The standard real frame consists of unit vectors. -/
theorem norm_coordinateRealFrame_le (i : Fin (n * 2)) : ‖coordinateRealFrame (n := n) i‖ ≤ 1 := by
  unfold coordinateRealFrame
  dsimp only
  split_ifs
  · simp [coordinateVector]
  · rw [norm_smul]
    simp [coordinateVector]

/-- **`tok-wn-fl2:density-bound`**: `|density of (L^*a)ⁿ| ≤ ‖aⁿ‖ ‖L‖^{2n}`. -/
theorem abs_topDensity_formPower_comp_le (a : RealForm N 2)
    (L : ComplexModel n →L[ℝ] ComplexModel N) :
    |topDensity (formPower (a.compContinuousLinearMap L) n)| ≤
      ‖formPower a n‖ * ‖L‖ ^ (2 * n) := by
  rw [← formPower_comp, topDensity, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ← Real.norm_eq_abs]
  refine ContinuousAlternatingMap.le_opNorm_mul_pow_of_le _ ?_
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg L)).mpr fun i => ?_
  calc ‖L (topBasis n i)‖ ≤ ‖L‖ * ‖topBasis n i‖ := L.le_opNorm _
    _ ≤ ‖L‖ * 1 := by
        gcongr
        rw [topBasis_apply]
        exact norm_coordinateRealFrame_le _
    _ = ‖L‖ := mul_one _

end Pointwise

/-! ### The fibre volume through a parametrization -/

section Param

variable {n N : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  {𝒳 : Type*} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel N) 𝒳] [IsComplexManifold N 𝒳]

/-- **`tok-wn-fl2:param-bound`**: the measure of `(s^*Θ)ⁿ` on the image of a parametrization
`γ` with `s ∘ γ = g` is at most `M · vol(Y)` when
`‖(Θⁿ)_d(d(g y))‖ · ‖D(d ∘ g)(y)‖^{2n} ≤ M` on `Y`. -/
theorem topFormMeasure_image_le (w : KahlerBackground n X) {s : X → 𝒳}
    (hs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ s)
    (Θ : ClosedRealOneOneForm N 𝒳) (e : ComplexChart n X) (d : ComplexChart N 𝒳)
    {O : Set (ComplexModel n)} (hO : IsOpen O) {γ : ComplexModel n → X}
    {g : ComplexModel n → 𝒳}
    (hγ : ∀ y ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ γ y)
    (hγe : ∀ y ∈ O, γ y ∈ e.val.source) (hsγ : ∀ y ∈ O, s (γ y) = g y)
    (hgd : ∀ y ∈ O, g y ∈ d.val.source)
    {Y : Set (ComplexModel n)} (hYm : MeasurableSet Y) (hYO : Y ⊆ O) (hinj : InjOn γ Y)
    {M : ℝ} (hM : ∀ y ∈ Y, ‖(formPow Θ.val n).coeff d (d.val (g y))‖ *
      ‖fderiv ℝ (fun y => d.val (g y)) y‖ ^ (2 * n) ≤ M) :
    topFormMeasure w (formPow (ClosedRealOneOneForm.pullback hs Θ).val n) (γ '' Y) ≤
      ENNReal.ofReal M * volume Y := by
  set σ : ComplexModel n → ComplexModel n := fun y => e.val (γ y) with hσ
  -- `σ` is smooth on `O`
  have hσd : ∀ y ∈ O, ContDiffAt ℝ ∞ σ y := fun y hy =>
    (LSC.contDiffAt_chart_comp (hγ y hy) e (hγe y hy)).restrict_scalars ℝ
  have hσD : ∀ y ∈ O, HasFDerivAt σ (fderiv ℝ σ y) y := fun y hy =>
    ((hσd y hy).differentiableAt (by simp)).hasFDerivAt
  have hσW : ∀ y ∈ Y, HasFDerivWithinAt σ (fderiv ℝ σ y) Y y := fun y hy =>
    (hσD y (hYO hy)).hasFDerivWithinAt
  have hσinj : InjOn σ Y := by
    intro y hy y' hy' h
    apply hinj hy hy'
    have h1 := congrArg e.val.symm h
    simp only [hσ] at h1
    rwa [e.val.left_inv (hγe y (hYO hy)), e.val.left_inv (hγe y' (hYO hy'))] at h1
  have hσt : σ '' Y ⊆ e.val.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact e.val.map_source (hγe y (hYO hy))
  have hσm : MeasurableSet (σ '' Y) := measurable_image_of_fderivWithin hYm hσW hσinj
  have himg : γ '' Y = e.val.symm '' (σ '' Y) := by
    rw [image_image]
    exact (image_congr fun y hy => e.val.left_inv (hγe y (hYO hy))).symm
  rw [himg, topFormMeasure_image_eq w _ e hσm hσt,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hYm hσW hσinj]
  calc ∫⁻ y in Y, ENNReal.ofReal |(fderiv ℝ σ y).det| *
        ENNReal.ofReal (topDensity
          ((formPow (ClosedRealOneOneForm.pullback hs Θ).val n).coeff e (σ y)))
      ≤ ∫⁻ _ in Y, ENNReal.ofReal M := by
        refine setLIntegral_mono measurable_const fun y hy => ?_
        have hyO := hYO hy
        -- the coordinate representative of `s` and the chain rule
        have hdom : σ y ∈ coordinateDomain s e d := by
          refine ⟨e.val.map_source (hγe y hyO), ?_⟩
          show s (e.val.symm (e.val (γ y))) ∈ d.val.source
          rw [e.val.left_inv (hγe y hyO), hsγ y hyO]
          exact hgd y hyO
        have hcm : coordinateMap s e d (σ y) = d.val (g y) := by
          show d.val (s (e.val.symm (e.val (γ y)))) = _
          rw [e.val.left_inv (hγe y hyO), hsγ y hyO]
        have hcmD : HasFDerivAt (coordinateMap s e d)
            (fderiv ℝ (coordinateMap s e d) (σ y)) (σ y) :=
          (((coordinateMap_contDiffOn_real hs e d).contDiffAt
            ((coordinateDomain_isOpen hs e d).mem_nhds hdom)).differentiableAt
            (by simp)).hasFDerivAt
        have heq : (fun y => coordinateMap s e d (σ y)) =ᶠ[𝓝 y] fun y => d.val (g y) := by
          filter_upwards [hO.mem_nhds hyO] with y' hy'
          show d.val (s (e.val.symm (e.val (γ y')))) = _
          rw [e.val.left_inv (hγe y' hy'), hsγ y' hy']
        have hchain : fderiv ℝ (fun y => d.val (g y)) y =
            (fderiv ℝ (coordinateMap s e d) (σ y)).comp (fderiv ℝ σ y) := by
          rw [← heq.fderiv_eq]
          exact (hcmD.comp y (hσD y hyO)).fderiv
        rw [formPow_coeff, ClosedRealOneOneForm.pullback_val, SmoothRealForm.pullback_coeff hs
          Θ.val e d hdom, hcm, ← ENNReal.ofReal_mul (abs_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        set a := Θ.val.coeff d (d.val (g y))
        set L₁ := fderiv ℝ (coordinateMap s e d) (σ y)
        set L₂ := fderiv ℝ σ y
        have hdet : (L₂.det) * topDensity (formPower (a.compContinuousLinearMap L₁) n) =
            topDensity (formPower (a.compContinuousLinearMap (L₁.comp L₂)) n) := by
          have hcomp : (a.compContinuousLinearMap L₁).compContinuousLinearMap L₂ =
              a.compContinuousLinearMap (L₁.comp L₂) := by
            ext v
            rfl
          rw [← hcomp, ← formPower_comp L₂ (a.compContinuousLinearMap L₁),
            topDensity_compContinuousLinearMap]
        calc |L₂.det| * topDensity (formPower (a.compContinuousLinearMap L₁) n)
            ≤ |L₂.det * topDensity (formPower (a.compContinuousLinearMap L₁) n)| := by
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (le_abs_self _) (abs_nonneg _)
          _ = |topDensity (formPower (a.compContinuousLinearMap (L₁.comp L₂)) n)| := by rw [hdet]
          _ ≤ ‖formPower a n‖ * ‖L₁.comp L₂‖ ^ (2 * n) :=
              abs_topDensity_formPower_comp_le a _
          _ = ‖(formPow Θ.val n).coeff d (d.val (g y))‖ *
                ‖fderiv ℝ (fun y => d.val (g y)) y‖ ^ (2 * n) := by
              rw [hchain, formPow_coeff]
          _ ≤ M := hM y hy
    _ = ENNReal.ofReal M * volume Y := setLIntegral_const Y _

end Param

end SGPT.Okounkov.TranscendentalWN.FL2
