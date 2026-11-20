import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.UniformSpace.HeineCantor
import SGPT.NPP.DN3ParamIntegral

/-!
# Uniform second-order expansion of even weighted averages

Lane DN6 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`, Step 7, proof of
`eq:chern-smoothing-generator`: "the integrand is a smooth function of `(rζ, y)` … so Taylor's
formula in `rζ` gives `Ψ_r^*φ = φ + rφ₁ + r²φ₂ + O(r³)` … uniformly in `y`").

For a `C²` function `A((y, η), ξ)` (the weight is part of `A`), even in `ξ` and vanishing for
`‖ξ‖ > R`, the average `∫ A((y, tξ), ξ) dξ` satisfies, uniformly for `y` in compact sets,
`∫ A((y, tξ), ξ) dξ = ∫ A((y, 0), ξ) dξ + t² Q_A(y) + o(t²)` as `t → 0⁺`, where
`Q_A(y) = ½ ∫ D²_p A((y, 0), ξ)((0, ξ), (0, ξ)) dξ` (`tendstoUniformlyOn_weightAverage`).  The
first-order term vanishes because `A` is even in `ξ`.

* `abs_taylor_two_le`: the one-variable Taylor bound
  `|f t - f 0 - t f'(0) - t²/2 f''(0)| ≤ M t²` when `|f'' - f''(0)| ≤ M` on `[0, t]`;
* `hasDerivAt_line`, `hasDerivAt_line_fderiv`: derivatives along a line;
* `weightAverage`, `pD1`, `pD2`, `weightSecondCoeff`, `continuous_weightSecondCoeff`,
  `tendstoUniformlyOn_weightAverage`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace SGPT.NPP.DN6

/-! ### The one-variable Taylor bound -/

/-- **Taylor's bound of order two.**  If `f' = f'` and `f'' = (f')'` on `[0, t]` and
`|f''(s) - f''(0)| ≤ M` there, then `|f t - f 0 - t f'(0) - t²/2 f''(0)| ≤ M t²`. -/
theorem abs_taylor_two_le {f f' f'' : ℝ → ℝ} {t M : ℝ} (ht : 0 ≤ t)
    (hf : ∀ s ∈ Icc 0 t, HasDerivAt f (f' s) s)
    (hf' : ∀ s ∈ Icc 0 t, HasDerivAt f' (f'' s) s)
    (hM : ∀ s ∈ Icc 0 t, |f'' s - f'' 0| ≤ M) :
    |f t - f 0 - t * f' 0 - t ^ 2 / 2 * f'' 0| ≤ M * t ^ 2 := by
  -- the first derivative of the remainder
  set g' : ℝ → ℝ := fun s => f' s - f' 0 - s * f'' 0 with hg'
  have hg'd : ∀ s ∈ Icc 0 t, HasDerivAt g' (f'' s - f'' 0) s := by
    intro s hs
    have h := ((hf' s hs).sub_const (f' 0)).fun_sub ((hasDerivAt_id' s).mul_const (f'' 0))
    simp only [one_mul] at h
    exact h
  have hg'b : ∀ s ∈ Icc 0 t, |g' s| ≤ M * t := by
    intro s hs
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := g') (a := 0) (b := t)
      (f' := fun s => f'' s - f'' 0) (C := M)
      (fun x hx => (hg'd x hx).hasDerivWithinAt) (fun x hx => hM x (Ico_subset_Icc_self hx)) s hs
    have h0 : g' 0 = 0 := by simp [hg']
    rw [h0, sub_zero, Real.norm_eq_abs] at h
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, ht⟩)
    calc |g' s| ≤ M * (s - 0) := h
      _ ≤ M * t := mul_le_mul_of_nonneg_left (by linarith [hs.2]) hM0
  -- the remainder
  set g : ℝ → ℝ := fun s => f s - f 0 - s * f' 0 - s ^ 2 / 2 * f'' 0 with hg
  have hgd : ∀ s ∈ Icc 0 t, HasDerivAt g (g' s) s := by
    intro s hs
    have h2 : HasDerivAt (fun s : ℝ => s ^ 2 / 2 * f'' 0) (s * f'' 0) s := by
      have := ((hasDerivAt_pow 2 s).div_const 2).mul_const (f'' 0)
      exact this.congr_deriv (by rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]; push_cast; ring)
    have h := (((hf s hs).sub_const (f 0)).fun_sub
      ((hasDerivAt_id' s).mul_const (f' 0))).fun_sub h2
    simp only [one_mul] at h
    exact h
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := g) (a := 0) (b := t)
    (f' := g') (C := M * t) (fun x hx => (hgd x hx).hasDerivWithinAt)
    (fun x hx => by rw [Real.norm_eq_abs]; exact hg'b x (Ico_subset_Icc_self hx)) t
    ⟨ht, le_rfl⟩
  have h0 : g 0 = 0 := by simp [hg]
  rw [h0, sub_zero, Real.norm_eq_abs] at h
  calc |f t - f 0 - t * f' 0 - t ^ 2 / 2 * f'' 0| = |g t| := rfl
    _ ≤ M * t * (t - 0) := h
    _ = M * t ^ 2 := by ring

/-! ### Derivatives along a line -/

section Line

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem hasDerivAt_lineMap (c v : P) (s : ℝ) :
    HasDerivAt (fun s : ℝ => c + s • v) v s := by
  simpa using ((hasDerivAt_id s).smul_const v).const_add c

/-- The derivative of `s ↦ A(c + s v)`. -/
theorem hasDerivAt_line {A : P → ℝ} (hA : Differentiable ℝ A) (c v : P) (s : ℝ) :
    HasDerivAt (fun s : ℝ => A (c + s • v)) (fderiv ℝ A (c + s • v) v) s :=
  (hA (c + s • v)).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_lineMap c v s)

/-- The derivative of `s ↦ DA(c + s v) v`. -/
theorem hasDerivAt_line_fderiv {A : P → ℝ} (hA : Differentiable ℝ (fderiv ℝ A)) (c v : P)
    (s : ℝ) :
    HasDerivAt (fun s : ℝ => fderiv ℝ A (c + s • v) v)
      (fderiv ℝ (fderiv ℝ A) (c + s • v) v v) s := by
  have h : HasDerivAt (fun s : ℝ => fderiv ℝ A (c + s • v))
      (fderiv ℝ (fderiv ℝ A) (c + s • v) v) s :=
    (hA (c + s • v)).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_lineMap c v s)
  exact (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt s h

end Line

theorem prod_add_smul {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (y : X) (ξ : E) (s : ℝ) :
    ((y, 0) : X × E) + s • ((0 : X), ξ) = (y, s • ξ) := by
  ext <;> simp

/-! ### Averages with a weight depending on the base point -/

section Weighted

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E)

/-- The weighted average `∫ A((y, tξ), ξ) dξ` (the weight is part of `A`). -/
def weightAverage (A : (X × E) × E → ℝ) (y : X) (t : ℝ) : ℝ :=
  ∫ ξ, A ((y, t • ξ), ξ) ∂μ

/-- The first partial derivative of `A` in the first slot. -/
def pD1 (A : (X × E) × E → ℝ) (p : X × E) (ξ : E) : X × E →L[ℝ] ℝ :=
  fderiv ℝ (fun p => A (p, ξ)) p

/-- The second partial derivative of `A` in the first slot. -/
def pD2 (A : (X × E) × E → ℝ) (p : X × E) (ξ : E) : X × E →L[ℝ] X × E →L[ℝ] ℝ :=
  fderiv ℝ (fun p => fderiv ℝ (fun p => A (p, ξ)) p) p

/-- The second-order coefficient `½ ∫ D²_p A((y, 0), ξ)((0, ξ), (0, ξ)) dξ`. -/
def weightSecondCoeff (A : (X × E) × E → ℝ) (y : X) : ℝ :=
  (1 / 2 : ℝ) * ∫ ξ, pD2 A (y, 0) ξ (0, ξ) (0, ξ) ∂μ

variable {μ}

omit [MeasurableSpace E] [BorelSpace E] in
theorem continuous_pD1 {A : (X × E) × E → ℝ} (hA : ContDiff ℝ 2 A) :
    Continuous fun q : (X × E) × E => pD1 A q.1 q.2 := by
  have hA' : ContDiffOn ℝ (1 + 1) (fun q : (X × E) × E => A (q.1, q.2)) (univ ×ˢ univ) := by
    rw [univ_prod_univ]; exact (hA.of_le (by norm_num)).contDiffOn
  have h := DN3.contDiffOn_fderiv_param (F := fun p ξ => A (p, ξ)) (U := univ) (m := 1)
    isOpen_univ hA'
  rw [univ_prod_univ] at h
  exact continuousOn_univ.mp h.continuousOn

omit [MeasurableSpace E] [BorelSpace E] in
theorem continuous_pD2 {A : (X × E) × E → ℝ} (hA : ContDiff ℝ 2 A) :
    Continuous fun q : (X × E) × E => pD2 A q.1 q.2 := by
  have hA' : ContDiffOn ℝ 2 (fun q : (X × E) × E => A (q.1, q.2)) (univ ×ˢ univ) := by
    rw [univ_prod_univ]; exact hA.contDiffOn
  have h := DN3.continuousOn_fderiv2_param (F := fun p ξ => A (p, ξ)) (U := univ)
    isOpen_univ hA'
  rw [univ_prod_univ] at h
  exact continuousOn_univ.mp h

omit [MeasurableSpace E] [BorelSpace E] in
theorem contDiff_slice {A : (X × E) × E → ℝ} (hA : ContDiff ℝ 2 A) (ξ : E) :
    ContDiff ℝ 2 fun p => A (p, ξ) :=
  hA.comp (contDiff_id.prodMk contDiff_const)

omit [MeasurableSpace E] [BorelSpace E] in
theorem pD_eq_zero_of_norm {A : (X × E) × E → ℝ} {R : ℝ}
    (hAs : ∀ p ξ, R < ‖ξ‖ → A (p, ξ) = 0) {ξ : E} (hξ : R < ‖ξ‖) (p : X × E) :
    pD1 A p ξ = 0 ∧ pD2 A p ξ = 0 := by
  have h0 : (fun p => A (p, ξ)) = fun _ => 0 := funext fun p => hAs p ξ hξ
  simp [pD1, pD2, h0]

omit [MeasurableSpace E] [BorelSpace E] in
theorem hasCompactSupport_of_norm [ProperSpace E] {F : E → ℝ} {R : ℝ}
    (hF : ∀ ξ, R < ‖ξ‖ → F ξ = 0) : HasCompactSupport F :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E) R) fun ξ hξ => by
    simp only [mem_closedBall, dist_zero_right, not_le] at hξ
    exact hF ξ hξ

variable [IsFiniteMeasureOnCompacts μ]

theorem integrable_of_norm {F : E → ℝ} (hF : Continuous F) {R : ℝ}
    (hFs : ∀ ξ, R < ‖ξ‖ → F ξ = 0) : Integrable F μ := by
  have : ProperSpace E := FiniteDimensional.proper ℝ E
  exact hF.integrable_of_hasCompactSupport (hasCompactSupport_of_norm hFs)

/-- The weighted second-order coefficient is continuous. -/
theorem continuous_weightSecondCoeff {A : (X × E) × E → ℝ} (hA : ContDiff ℝ 2 A) {R : ℝ}
    (hAs : ∀ p ξ, R < ‖ξ‖ → A (p, ξ) = 0) : Continuous (weightSecondCoeff μ A) := by
  have : ProperSpace E := FiniteDimensional.proper ℝ E
  have hD2 := continuous_pD2 hA
  refine continuous_const.mul ?_
  have hset : (fun y => ∫ ξ, pD2 A (y, 0) ξ (0, ξ) (0, ξ) ∂μ) =
      fun y => ∫ ξ in closedBall (0 : E) R, pD2 A (y, 0) ξ (0, ξ) (0, ξ) ∂μ := by
    funext y
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun ξ hξ => ?_).symm
    simp only [mem_closedBall, dist_zero_right, not_le] at hξ
    rw [(pD_eq_zero_of_norm hAs hξ _).2]
    simp
  rw [hset]
  refine continuous_parametric_integral_of_continuous ?_ (isCompact_closedBall 0 R)
  exact ((hD2.comp ((continuous_fst.prodMk continuous_const).prodMk continuous_snd)).clm_apply
    (continuous_const.prodMk continuous_snd)).clm_apply (continuous_const.prodMk continuous_snd)

/-- **Uniform second-order expansion of weighted averages.**  For a `C²` function `A(p, ξ)`,
even in `ξ` and vanishing for `‖ξ‖ > R`,
`(∫ A((y, tξ), ξ) dξ - ∫ A((y, 0), ξ) dξ)/t² → ½ ∫ D²_p A((y, 0), ξ)((0, ξ), (0, ξ)) dξ`
uniformly on compact sets of `y`. -/
theorem tendstoUniformlyOn_weightAverage [μ.IsNegInvariant] {A : (X × E) × E → ℝ}
    (hA : ContDiff ℝ 2 A) {R : ℝ} (hR : 0 < R) (hAs : ∀ p ξ, R < ‖ξ‖ → A (p, ξ) = 0)
    (hAe : ∀ p ξ, A (p, -ξ) = A (p, ξ)) {K : Set X} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun t y => (weightAverage μ A y t - ∫ ξ, A ((y, 0), ξ) ∂μ) / t ^ 2)
      (weightSecondCoeff μ A) (𝓝[>] 0) K := by
  have : ProperSpace E := FiniteDimensional.proper ℝ E
  have hD1 := continuous_pD1 hA
  have hD2 := continuous_pD2 hA
  set S : Set ((X × E) × E) := (K ×ˢ closedBall (0 : E) 1) ×ˢ closedBall (0 : E) R with hS
  have hSc : IsCompact S := (hK.prod (isCompact_closedBall 0 1)).prod (isCompact_closedBall 0 R)
  set H : ((X × E) × E) × (X × E) → ℝ := fun w => pD2 A w.1.1 w.1.2 w.2 w.2 with hH
  have hHc : Continuous H :=
    ((hD2.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
  have hSc' : IsCompact (S ×ˢ closedBall (0 : X × E) R) := hSc.prod (isCompact_closedBall 0 R)
  have huc := Metric.uniformContinuousOn_iff.mp
    (hSc'.uniformContinuousOn_of_continuous hHc.continuousOn)
  set I : ℝ := μ.real (closedBall (0 : E) R) with hI
  have hI0 : 0 ≤ I := measureReal_nonneg
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδu⟩ := huc (ε / (2 * (I + 1))) (by positivity)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < min (δ / R) (1 / R) :=
    Ioo_mem_nhdsGT (lt_min (div_pos hδ hR) (div_pos one_pos hR))
  filter_upwards [hev] with t ⟨ht0, ht1⟩ y hy
  have htδ : t * R < δ := by
    have := ht1.trans_le (min_le_left _ _); rwa [lt_div_iff₀ hR] at this
  have ht1' : t * R < 1 := by
    have := ht1.trans_le (min_le_right _ _); rwa [lt_div_iff₀ hR] at this
  -- the pointwise Taylor bound
  have hpt : ∀ ξ : E, ‖ξ‖ ≤ R →
      |A ((y, t • ξ), ξ) - A ((y, 0), ξ) - t * pD1 A (y, 0) ξ (0, ξ) -
        t ^ 2 / 2 * pD2 A (y, 0) ξ (0, ξ) (0, ξ)| ≤ ε / (2 * (I + 1)) * t ^ 2 := by
    intro ξ hξ
    have hA1 : Differentiable ℝ fun p => A (p, ξ) :=
      (contDiff_slice hA ξ).differentiable (by norm_num)
    have hA2 : Differentiable ℝ (fderiv ℝ fun p => A (p, ξ)) :=
      ((contDiff_slice hA ξ).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    have h := abs_taylor_two_le (f := fun s => A ((y, 0) + s • ((0 : X), ξ), ξ))
      (f' := fun s => pD1 A ((y, 0) + s • ((0 : X), ξ)) ξ (0, ξ))
      (f'' := fun s => pD2 A ((y, 0) + s • ((0 : X), ξ)) ξ (0, ξ) (0, ξ))
      (M := ε / (2 * (I + 1))) ht0.le (fun s _ => hasDerivAt_line hA1 _ _ s)
      (fun s _ => hasDerivAt_line_fderiv hA2 _ _ s) ?_
    · simpa only [prod_add_smul, zero_smul, add_zero] using h
    · intro s hs
      simp only [prod_add_smul, zero_smul, add_zero]
      have hsξ : ‖s • ξ‖ ≤ t * R := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
        exact mul_le_mul hs.2 hξ (norm_nonneg _) ht0.le
      have hmems : (((y, s • ξ), ξ) : (X × E) × E) ∈ S :=
        ⟨⟨hy, by simpa using hsξ.trans ht1'.le⟩, by simpa using hξ⟩
      have hmem0 : (((y, 0), ξ) : (X × E) × E) ∈ S := ⟨⟨hy, by simp⟩, by simpa using hξ⟩
      have hv : ((0 : X), ξ) ∈ closedBall (0 : X × E) R := by
        simpa [Prod.norm_def] using hξ
      have hdist : dist ((((y, s • ξ), ξ) : (X × E) × E), ((0 : X), ξ))
          ((((y, 0), ξ) : (X × E) × E), ((0 : X), ξ)) < δ := by
        rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Prod.dist_eq, dist_self,
          max_eq_left dist_nonneg, Prod.dist_eq, dist_self, dist_zero_right,
          max_eq_right (norm_nonneg _)]
        exact hsξ.trans_lt htδ
      have hd := hδu _ ⟨hmems, hv⟩ _ ⟨hmem0, hv⟩ hdist
      rw [Real.dist_eq] at hd
      exact hd.le
  -- integrability of the pieces
  have hc1 : Continuous fun ξ : E => A ((y, t • ξ), ξ) :=
    hA.continuous.comp ((continuous_const.prodMk (continuous_const.smul continuous_id)).prodMk
      continuous_id)
  have hc2 : Continuous fun ξ : E => A ((y, 0), ξ) :=
    hA.continuous.comp (continuous_const.prodMk continuous_id)
  have hc3 : Continuous fun ξ : E => pD1 A (y, 0) ξ (0, ξ) :=
    (hD1.comp (continuous_const.prodMk continuous_id)).clm_apply
      (continuous_const.prodMk continuous_id)
  have hc4 : Continuous fun ξ : E => pD2 A (y, 0) ξ (0, ξ) (0, ξ) :=
    ((hD2.comp (continuous_const.prodMk continuous_id)).clm_apply
      (continuous_const.prodMk continuous_id)).clm_apply (continuous_const.prodMk continuous_id)
  have hi1 := integrable_of_norm (μ := μ) (R := R) hc1 fun ξ hξ => hAs _ ξ hξ
  have hi2 := integrable_of_norm (μ := μ) (R := R) hc2 fun ξ hξ => hAs _ ξ hξ
  have hi3 := integrable_of_norm (μ := μ) (R := R) hc3 fun ξ hξ => by
    simp [(pD_eq_zero_of_norm hAs hξ _).1]
  have hi4 := integrable_of_norm (μ := μ) (R := R) hc4 fun ξ hξ => by
    simp [(pD_eq_zero_of_norm hAs hξ _).2]
  -- the first-order term vanishes
  have hlin : ∫ ξ, pD1 A (y, 0) ξ (0, ξ) ∂μ = 0 := by
    have hodd : ∀ ξ : E, pD1 A (y, 0) (-ξ) (0, -ξ) = -pD1 A (y, 0) ξ (0, ξ) := by
      intro ξ
      have he : (fun p => A (p, -ξ)) = fun p => A (p, ξ) := funext fun p => hAe p ξ
      have h0 : ((0 : X), -ξ) = -((0 : X), ξ) := by simp
      simp only [pD1, he, h0, map_neg]
    have h := integral_neg_eq_self (fun ξ => pD1 A (y, 0) ξ (0, ξ)) μ
    simp only [hodd, integral_neg] at h
    linarith
  -- the remainder identity
  set Rm : E → ℝ := fun ξ => A ((y, t • ξ), ξ) - A ((y, 0), ξ) - t * pD1 A (y, 0) ξ (0, ξ) -
    t ^ 2 / 2 * pD2 A (y, 0) ξ (0, ξ) (0, ξ) with hRm
  have hRint : ∫ ξ, Rm ξ ∂μ = weightAverage μ A y t - (∫ ξ, A ((y, 0), ξ) ∂μ) -
      t ^ 2 * weightSecondCoeff μ A y := by
    have hiA : Integrable (fun ξ => A ((y, t • ξ), ξ) - A ((y, 0), ξ)) μ := hi1.sub hi2
    have hiB : Integrable (fun ξ => A ((y, t • ξ), ξ) - A ((y, 0), ξ) -
        t * pD1 A (y, 0) ξ (0, ξ)) μ := hiA.sub (hi3.const_mul _)
    rw [hRm, integral_sub hiB (hi4.const_mul _), integral_sub hiA (hi3.const_mul _),
      integral_sub hi1 hi2, integral_const_mul, integral_const_mul, hlin, weightAverage,
      weightSecondCoeff]
    ring
  have hRbd : |∫ ξ, Rm ξ ∂μ| ≤ ε / (2 * (I + 1)) * t ^ 2 * I := by
    have hbi : Integrable ((closedBall (0 : E) R).indicator fun _ => ε / (2 * (I + 1)) * t ^ 2)
        μ := (integrable_indicator_iff measurableSet_closedBall).mpr
          (integrableOn_const (isCompact_closedBall (0 : E) R).measure_lt_top.ne)
    calc |∫ ξ, Rm ξ ∂μ| = ‖∫ ξ, Rm ξ ∂μ‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ ξ, (closedBall (0 : E) R).indicator (fun _ => ε / (2 * (I + 1)) * t ^ 2) ξ ∂μ := by
          refine norm_integral_le_of_norm_le hbi (Eventually.of_forall fun ξ => ?_)
          rw [Real.norm_eq_abs]
          by_cases hξ : ‖ξ‖ ≤ R
          · rw [indicator_of_mem (by simpa using hξ)]
            exact hpt ξ hξ
          · rw [indicator_of_notMem (by simpa using hξ)]
            have hξ' : R < ‖ξ‖ := not_le.mp hξ
            have htξ : R < ‖t • ξ‖ ∨ True := Or.inr trivial
            simp only [hRm, hAs _ ξ hξ', (pD_eq_zero_of_norm hAs hξ' _).1,
              (pD_eq_zero_of_norm hAs hξ' _).2]
            simp
      _ = ε / (2 * (I + 1)) * t ^ 2 * I := by
          rw [integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul,
            hI]
          ring
  -- conclusion
  have ht2 : 0 < t ^ 2 := by positivity
  rw [Real.dist_eq]
  have key : weightSecondCoeff μ A y -
      (weightAverage μ A y t - ∫ ξ, A ((y, 0), ξ) ∂μ) / t ^ 2 = -(∫ ξ, Rm ξ ∂μ) / t ^ 2 := by
    rw [hRint]; field_simp; ring
  rw [key, abs_div, abs_neg, abs_of_pos ht2, div_lt_iff₀ ht2]
  calc |∫ ξ, Rm ξ ∂μ| ≤ ε / (2 * (I + 1)) * t ^ 2 * I := hRbd
    _ < ε * t ^ 2 := by
      have h1 : ε / (2 * (I + 1)) * I ≤ ε / 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      nlinarith

end Weighted

end SGPT.NPP.DN6
