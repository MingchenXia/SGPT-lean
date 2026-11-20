import SGPT.NPP.DN4Core
import SGPT.Foundations.Analysis.Pending.ConcentrationPotentialLevi

/-!
# The core estimate with a variable weight

Lane DN4 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`, Step 3: "the weight `W` carries the
nonholomorphic dependence on the base point"; the curvature term `C^v` of Step 4).

In a chart, the smoothing at base points near a centre is an integral against a weight
`ω(τ, ζ)` (the Kähler weight `χ(|ζ|²_{h(z)})`, normalised, read in a frame that is holomorphic in the
base point).  If at the centre `ω(0, ·) = χ(|·|²)`, `D_τ ω(0, ·) = 0`, and the Levi form of the
weight is a double divergence,
`L_τ ω(0, ζ) = Re ∑_{a,b} M_{ab} ∂_a ∂̄_b χ₁(|ζ|²)`, then (`leviForm_integral_weight_ge`)

  `L_τ ∫ p(c(τ, ζ)) ω(τ, ζ) dζ ≥ (core bound of leviForm_integral_ge) - 2 (∑ |M_{ab}|) ∫ (-χ₁) T`.

The extra term is FPT's curvature contribution `-r² ∫ P[Da(C^v)] χ₁`: two integrations by parts
move `∂_a ∂̄_b` onto `p ∘ Φ` and the complex Hessian is bounded by its trace.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff ComplexConjugate

namespace SGPT.NPP.DN4

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.CauchyGreen
open SGPT.NPP.DN3 SGPT.Envelopes.LapClass

variable {n : ℕ}

/-- `χ̂₁(ζ) = χ₁(|ζ|²)` as a complex function. -/
def chiOneC (n : ℕ) : ComplexModel n → ℂ := fun y => ((chiOne n (‖y‖ ^ 2) : ℝ) : ℂ)

theorem contDiff_chiOneC : ContDiff ℝ ∞ (chiOneC n) :=
  contDiff_ofReal_comp contDiff_chiOne_normSq

theorem hasCompactSupport_chiOneC : HasCompactSupport (chiOneC n) :=
  hasCompactSupport_of_unitBall fun _ hy => by
    simp [chiOneC, chiOne_normSq_eq_zero hy.le]

/-- Differentiation under the integral sign for the unweighted integral (step 1 of the core). -/
theorem leviForm_integral_chi_eq {c : ℂ → ComplexModel n → ComplexModel n}
    {p : ComplexModel n → ℝ} (hp : ContDiff ℝ 2 p)
    (hc : ContDiff ℝ 2 (fun q : ℂ × ComplexModel n => c q.1 q.2)) :
    leviForm (fun τ => ∫ ζ, p (c τ ζ) * chi n (‖ζ‖ ^ 2)) 0 1 =
      ∫ ζ, chi n (‖ζ‖ ^ 2) * leviForm (fun τ => p (c τ ζ)) 0 1 := by
  have hcτ : ∀ ζ : ComplexModel n, ContDiff ℝ 2 (fun τ => c τ ζ) := fun ζ =>
    hc.comp (contDiff_id.prodMk contDiff_const)
  have hF : ContDiffOn ℝ 2 (fun q : ℂ × ComplexModel n => p (c q.1 q.2) * chi n (‖q.2‖ ^ 2))
      (univ ×ˢ univ) :=
    ((hp.comp hc).mul (((contDiff_chi_normSq (n := n)).of_le (by norm_cast)).comp
      contDiff_snd)).contDiffOn
  have hsupp : ∀ τ ∈ (univ : Set ℂ), ∀ ζ : ComplexModel n, 1 < ‖ζ‖ →
      p (c τ ζ) * chi n (‖ζ‖ ^ 2) = 0 := fun τ _ ζ hζ => by
    rw [chi_normSq_eq_zero hζ.le, mul_zero]
  rw [leviForm_integral_of_contDiffOn (μ := volume)
    (F := fun τ ζ => p (c τ ζ) * chi n (‖ζ‖ ^ 2)) isOpen_univ hF hsupp (mem_univ (0 : ℂ)) 1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
  have e : (fun τ => p (c τ ζ) * chi n (‖ζ‖ ^ 2)) =
      (chi n (‖ζ‖ ^ 2)) • (fun τ => p (c τ ζ)) := by
    funext τ; simp [mul_comm]
  simp only
  rw [e, leviForm_smul (show ContDiffAt ℝ 2 (fun τ => p (c τ ζ)) 0 from
    (hp.comp (hcτ ζ)).contDiffAt)]

theorem continuous_dDir_dbarDir_chiOneC (a b : Fin n) :
    Continuous (dDir (coordinateVector a) (dbarDir (coordinateVector b) (chiOneC n))) :=
  (contDiff_dDir (k := 0) (contDiff_dbarDir (k := 1)
    ((contDiff_chiOneC (n := n)).of_le (by norm_cast)))).continuous

theorem dDir_dbarDir_chiOneC_eq_zero (a b : Fin n) {ζ : ComplexModel n} (hζ : 1 < ‖ζ‖) :
    dDir (coordinateVector a) (dbarDir (coordinateVector b) (chiOneC n)) ζ = 0 := by
  refine image_eq_zero_of_notMem_tsupport fun h => ?_
  have hsub : tsupport (chiOneC n) ⊆ closedBall (0 : ComplexModel n) 1 :=
    tsupport_chiOne_normSq_subset
  have := hsub (OTChen.tsupport_dbarDir_subset _ _ (tsupport_dDir_subset _ _ h))
  rw [mem_closedBall, dist_zero_right] at this
  linarith

/-- **The weight term**: `∫ g Re ∑ M_{ab} ∂_a ∂̄_b χ̂₁ ≥ -2 (∑|M_{ab}|) ∫ (-χ₁) levTr g` for `g` of
class `C²` and plurisubharmonic on the closed unit ball. -/
theorem integral_mul_weightLevi_ge {g : ComplexModel n → ℝ} (hg : ContDiff ℝ 2 g)
    (hpsh : ∀ ζ ∈ closedBall (0 : ComplexModel n) 1, ∀ v, 0 ≤ leviForm g ζ v)
    (M : Fin n → Fin n → ℂ) :
    -(2 * (∑ a, ∑ b, ‖M a b‖) * ∫ ζ, -chiOne n (‖ζ‖ ^ 2) * levTr g ζ) ≤
      ∫ ζ, g ζ * (∑ a, ∑ b, M a b *
        dDir (coordinateVector a) (dbarDir (coordinateVector b) (chiOneC n)) ζ).re := by
  have hgc : ContDiff ℝ 2 (fun y => (g y : ℂ)) := contDiff_ofReal_comp hg
  have hN2 : ContDiff ℝ 2 (chiOneC n) := (contDiff_chiOneC (n := n)).of_le (by norm_cast)
  -- integrability of the pieces
  have hddc : ∀ a b : Fin n, Continuous
      (dDir (coordinateVector a) (dbarDir (coordinateVector b) (chiOneC n))) := fun a b =>
    (contDiff_dDir (k := 0) (contDiff_dbarDir (k := 1) hN2)).continuous
  have hsuppdd : ∀ a b : Fin n, ∀ ζ : ComplexModel n, 1 < ‖ζ‖ →
      dDir (coordinateVector a) (dbarDir (coordinateVector b) (chiOneC n)) ζ = 0 := by
    intro a b ζ hζ
    have hc : HasCompactSupport (dDir (coordinateVector a)
        (dbarDir (coordinateVector b) (chiOneC n))) :=
      hasCompactSupport_dDir (hasCompactSupport_dbarDir hasCompactSupport_chiOneC _) _
    refine image_eq_zero_of_notMem_tsupport fun h => ?_
    have hsub : tsupport (chiOneC n) ⊆ closedBall (0 : ComplexModel n) 1 :=
      tsupport_chiOne_normSq_subset
    have := hsub (OTChen.tsupport_dbarDir_subset _ _ (tsupport_dDir_subset _ _ h))
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  have hI : ∀ a b : Fin n, Integrable (fun ζ => (g ζ : ℂ) *
      dDir (coordinateVector a) (dbarDir (coordinateVector b) (chiOneC n)) ζ) := fun a b =>
    ((continuous_ofReal.comp hg.continuous).mul (hddc a b)).integrable_of_hasCompactSupport
      (hasCompactSupport_of_unitBall fun ζ hζ => by simp [hsuppdd a b ζ hζ])
  have hJ : ∀ a b : Fin n, Integrable (fun ζ => dbarDir (coordinateVector b)
      (dDir (coordinateVector a) (fun y => (g y : ℂ))) ζ * chiOneC n ζ) := fun a b =>
    ((contDiff_dbarDir (k := 0) (contDiff_dDir (k := 1) hgc)).continuous.mul
      (contDiff_chiOneC (n := n)).continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_of_unitBall fun ζ hζ => by
        simp [chiOneC, chiOne_normSq_eq_zero hζ.le])
  -- the identity after two integrations by parts
  have hIBP : ∫ ζ, g ζ * (∑ a, ∑ b, M a b *
      dDir (coordinateVector a) (dbarDir (coordinateVector b) (chiOneC n)) ζ).re =
      (∑ a, ∑ b, M a b * ∫ ζ, dbarDir (coordinateVector b)
        (dDir (coordinateVector a) (fun y => (g y : ℂ))) ζ * chiOneC n ζ).re := by
    have e1 : ∀ ζ, g ζ * (∑ a, ∑ b, M a b *
        dDir (coordinateVector a) (dbarDir (coordinateVector b) (chiOneC n)) ζ).re =
        (∑ a, ∑ b, M a b * ((g ζ : ℂ) *
          dDir (coordinateVector a) (dbarDir (coordinateVector b) (chiOneC n)) ζ)).re := by
      intro ζ
      rw [← Complex.re_ofReal_mul, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    simp_rw [e1]
    have hint : Integrable (fun ζ => ∑ a, ∑ b, M a b * ((g ζ : ℂ) *
        dDir (coordinateVector a) (dbarDir (coordinateVector b) (chiOneC n)) ζ)) :=
      integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hI a b).const_mul _
    have hre : ∫ ζ, (∑ a, ∑ b, M a b * ((g ζ : ℂ) *
        dDir (coordinateVector a) (dbarDir (coordinateVector b) (chiOneC n)) ζ)).re =
        (∫ ζ, ∑ a, ∑ b, M a b * ((g ζ : ℂ) *
        dDir (coordinateVector a) (dbarDir (coordinateVector b) (chiOneC n)) ζ)).re :=
      integral_re hint
    rw [hre]
    congr 1
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hI a b).const_mul _]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => (hI a b).const_mul _]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul, integral_mul_dDir_dbarDir hgc hN2 hasCompactSupport_chiOneC]
  rw [hIBP]
  -- the bound
  have hpt : ∀ a b : Fin n, ∀ ζ : ComplexModel n, ‖dbarDir (coordinateVector b)
      (dDir (coordinateVector a) (fun y => (g y : ℂ))) ζ * chiOneC n ζ‖ ≤
      2 * (-chiOne n (‖ζ‖ ^ 2) * levTr g ζ) := by
    intro a b ζ
    by_cases hζ : ‖ζ‖ ≤ 1
    · have hζ' : ζ ∈ closedBall (0 : ComplexModel n) 1 := by
        rw [mem_closedBall, dist_zero_right]; exact hζ
      have h1 := norm_dbarDir_dDir_ofReal_le hg.contDiffAt (hpsh ζ hζ') (coordinateVector a)
        (coordinateVector b)
      have ha := leviForm_coord_le_levTr (hpsh ζ hζ') a
      have hb := leviForm_coord_le_levTr (hpsh ζ hζ') b
      rw [norm_mul, chiOneC, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (chiOne_nonpos n _)]
      have hχ₁ : 0 ≤ -chiOne n (‖ζ‖ ^ 2) := neg_nonneg.mpr (chiOne_nonpos n _)
      nlinarith
    · push Not at hζ
      simp [chiOneC, chiOne_normSq_eq_zero hζ.le]
  have hT : Integrable (fun ζ : ComplexModel n => -chiOne n (‖ζ‖ ^ 2) * levTr g ζ) :=
    (((contDiff_chiOne_normSq (n := n)).continuous.neg).mul
      (continuous_levTr hg)).integrable_of_hasCompactSupport
      (hasCompactSupport_of_unitBall_real fun ζ hζ => by simp [chiOne_normSq_eq_zero hζ.le])
  have hnorm : ‖∑ a, ∑ b, M a b * ∫ ζ, dbarDir (coordinateVector b)
      (dDir (coordinateVector a) (fun y => (g y : ℂ))) ζ * chiOneC n ζ‖ ≤
      ∑ a, ∑ b, ‖M a b‖ * (2 * ∫ ζ, -chiOne n (‖ζ‖ ^ 2) * levTr g ζ) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_))
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_const_mul]
    exact integral_mono (hJ a b).norm (hT.const_mul 2) (hpt a b)
  set S := ∑ a, ∑ b, M a b * ∫ ζ, dbarDir (coordinateVector b)
      (dDir (coordinateVector a) (fun y => (g y : ℂ))) ζ * chiOneC n ζ with hS
  set J := ∫ ζ, -chiOne n (‖ζ‖ ^ 2) * levTr g ζ with hJdef
  have h1 : -‖S‖ ≤ S.re := by
    have := Complex.abs_re_le_norm S
    linarith [neg_abs_le S.re]
  have e : ∑ a, ∑ b, ‖M a b‖ * (2 * J) = 2 * (∑ a, ∑ b, ‖M a b‖) * J := by
    simp only [← Finset.sum_mul]
    ring
  rw [e] at hnorm
  linarith

/-- Continuity (hence integrability against `χ`) of the pointwise Levi form along the curves. -/
theorem integrable_chi_mul_leviForm_curve {c : ℂ → ComplexModel n → ComplexModel n}
    {p : ComplexModel n → ℝ} (hp : ContDiff ℝ 2 p)
    (hc : ContDiff ℝ 2 (fun q : ℂ × ComplexModel n => c q.1 q.2)) :
    Integrable (fun ζ : ComplexModel n => chi n (‖ζ‖ ^ 2) * leviForm (fun τ => p (c τ ζ)) 0 1) := by
  have hF2 : ContDiffOn ℝ 2 (fun q : ℂ × ComplexModel n => p (c q.1 q.2)) (univ ×ˢ univ) :=
    (hp.comp hc).contDiffOn
  have hD : Continuous (fun ζ : ComplexModel n => fderiv ℝ (fderiv ℝ (fun τ => p (c τ ζ))) 0) := by
    have h1 := continuousOn_fderiv2_param (F := fun τ ζ => p (c τ ζ)) isOpen_univ hF2
    rw [univ_prod_univ, continuousOn_univ] at h1
    exact h1.comp (continuous_const.prodMk continuous_id)
  have hLc : Continuous (fun ζ : ComplexModel n => leviForm (fun τ => p (c τ ζ)) 0 1) := by
    simp only [leviForm, realHessian_eq_fderiv]
    exact (((hD.clm_apply continuous_const).clm_apply continuous_const).add
      ((hD.clm_apply continuous_const).clm_apply continuous_const)).div_const 4
  exact (((contDiff_chi_normSq (n := n)).continuous).mul hLc).integrable_of_hasCompactSupport
    (hasCompactSupport_of_unitBall_real fun ζ hζ => by simp [chi_normSq_eq_zero hζ.le])

/-- **The core estimate with a weight** (see the module docstring). -/
theorem leviForm_integral_weight_ge {c : ℂ → ComplexModel n → ComplexModel n}
    {p : ComplexModel n → ℝ} {X R : ComplexModel n → ComplexModel n} {ρ a₁ a₂ b₁ : ℝ}
    (hρ : 1 < ρ) (hp : ContDiff ℝ 2 p)
    (hc : ContDiff ℝ 2 (fun q : ℂ × ComplexModel n => c q.1 q.2))
    (hΦ : DifferentiableOn ℂ (c 0) (ball 0 ρ)) (hY : DifferentiableOn ℂ (curveDz c) (ball 0 ρ))
    (hXh : DifferentiableOn ℂ X (ball 0 ρ)) (hRh : DifferentiableOn ℂ R (ball 0 ρ))
    (hX0 : X 0 = 0) (hR0 : R 0 = 0)
    (hX : ∀ ζ ∈ ball (0 : ComplexModel n) ρ, fderiv ℂ (c 0) ζ (X ζ) = curveDzbar c ζ)
    (hR : ∀ ζ ∈ ball (0 : ComplexModel n) ρ,
      fderiv ℂ (c 0) ζ (R ζ) = curveLevi c ζ - fderiv ℂ (curveDz c) ζ (X ζ))
    (hpsh : ∀ ζ ∈ closedBall (0 : ComplexModel n) 1, ∀ v, 0 ≤ leviForm p (c 0 ζ) v)
    (ha₁ : ∀ m, ∀ ζ ∈ closedBall (0 : ComplexModel n) 1, ‖fderiv ℂ (fun s => X s m) ζ‖ ≤ a₁)
    (ha₂ : ∀ m, ∀ ζ ∈ closedBall (0 : ComplexModel n) 1,
      ‖fderiv ℂ (fderiv ℂ (fun s => X s m)) ζ‖ ≤ a₂)
    (hb₁ : ∀ m, ∀ ζ ∈ closedBall (0 : ComplexModel n) 1, ‖fderiv ℂ (fun s => R s m) ζ‖ ≤ b₁)
    {wt : ℂ → ComplexModel n → ℝ} {δ R₀ : ℝ} (hδ : 0 < δ)
    (hwt : ContDiff ℝ 2 (fun q : ℂ × ComplexModel n => wt q.1 q.2))
    (hwts : ∀ τ ∈ ball (0 : ℂ) δ, ∀ ζ : ComplexModel n, R₀ < ‖ζ‖ → wt τ ζ = 0)
    (hwt0 : ∀ ζ, wt 0 ζ = chi n (‖ζ‖ ^ 2)) (hDwt : ∀ ζ, fderiv ℝ (fun τ => wt τ ζ) 0 = 0)
    (M : Fin n → Fin n → ℂ)
    (hLwt : ∀ ζ, leviForm (fun τ => wt τ ζ) 0 1 = (∑ a, ∑ b, M a b *
      dDir (coordinateVector a) (dbarDir (coordinateVector b) (chiOneC n)) ζ).re) :
    -(((n : ℝ) ^ 2 * (a₁ + a₂)) ^ 2 *
        ∫ ζ, chi n (‖ζ‖ ^ 2) * levTr (fun s => p (c 0 s)) ζ) -
      4 * (n : ℝ) ^ 2 * b₁ * (∫ ζ, -chiOne n (‖ζ‖ ^ 2) * levTr (fun s => p (c 0 s)) ζ) -
      2 * (∑ a, ∑ b, ‖M a b‖) * ∫ ζ, -chiOne n (‖ζ‖ ^ 2) * levTr (fun s => p (c 0 s)) ζ ≤
    leviForm (fun τ => ∫ ζ, p (c τ ζ) * wt τ ζ) 0 1 := by
  have hc0 : ContDiff ℝ 2 (c 0) := hc.comp (contDiff_const.prodMk contDiff_id)
  have hg2 : ContDiff ℝ 2 (fun s => p (c 0 s)) := hp.comp hc0
  have hcτ : ∀ ζ : ComplexModel n, ContDiff ℝ 2 (fun τ => c τ ζ) := fun ζ =>
    hc.comp (contDiff_id.prodMk contDiff_const)
  have hwtτ : ∀ ζ : ComplexModel n, ContDiff ℝ 2 (fun τ => wt τ ζ) := fun ζ =>
    hwt.comp (contDiff_id.prodMk contDiff_const)
  -- differentiation under the integral sign
  have hF : ContDiffOn ℝ 2 (fun q : ℂ × ComplexModel n => p (c q.1 q.2) * wt q.1 q.2)
      (ball (0 : ℂ) δ ×ˢ univ) := ((hp.comp hc).mul hwt).contDiffOn
  have hsupp : ∀ τ ∈ ball (0 : ℂ) δ, ∀ ζ : ComplexModel n, R₀ < ‖ζ‖ →
      p (c τ ζ) * wt τ ζ = 0 := fun τ hτ ζ hζ => by rw [hwts τ hτ ζ hζ, mul_zero]
  have step : leviForm (fun τ => ∫ ζ, p (c τ ζ) * wt τ ζ) 0 1 =
      ∫ ζ, (chi n (‖ζ‖ ^ 2) * leviForm (fun τ => p (c τ ζ)) 0 1 +
        p (c 0 ζ) * leviForm (fun τ => wt τ ζ) 0 1) := by
    rw [leviForm_integral_of_contDiffOn (μ := volume) (F := fun τ ζ => p (c τ ζ) * wt τ ζ)
      isOpen_ball hF hsupp (mem_ball_self hδ) 1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    simp only
    have hu : ContDiffAt ℝ 2 (fun τ => p (c τ ζ)) 0 := (hp.comp (hcτ ζ)).contDiffAt
    have hv : ContDiffAt ℝ 2 (fun τ => wt τ ζ) 0 := (hwtτ ζ).contDiffAt
    simp only [leviForm, ConcentrationPotentialLevi.realHessian_mul hu hv, hDwt ζ, hwt0 ζ,
      zero_apply, mul_zero, zero_mul, add_zero]
    ring
  -- the two pieces
  have hI1 := integrable_chi_mul_leviForm_curve (n := n) hp hc
  have hpshg : ∀ ζ ∈ closedBall (0 : ComplexModel n) 1, ∀ v,
      0 ≤ leviForm (fun s => p (c 0 s)) ζ v := by
    intro ζ hζ v
    have hζρ := closedBall_subset_ball hρ hζ
    have hΦ2 : ContDiffAt ℂ 2 (c 0) ζ :=
      (contDiffAt_of_differentiableOn_complex hΦ isOpen_ball hζρ).of_le (by norm_cast)
    rw [SGPT.NPP.DN2.leviForm_comp_holomorphic hΦ2 hp.contDiffAt]
    exact hpsh ζ hζ _
  have hW := integral_mul_weightLevi_ge hg2 hpshg M
  have hI2 : Integrable (fun ζ : ComplexModel n => p (c 0 ζ) * leviForm (fun τ => wt τ ζ) 0 1) := by
    simp_rw [hLwt]
    have hcont : Continuous (fun ζ : ComplexModel n => (∑ a, ∑ b, M a b *
        dDir (coordinateVector a) (dbarDir (coordinateVector b) (chiOneC n)) ζ).re) :=
      Complex.continuous_re.comp (continuous_finsetSum _ fun a _ => continuous_finsetSum _
        fun b _ => continuous_const.mul (continuous_dDir_dbarDir_chiOneC a b))
    exact (hg2.continuous.mul hcont).integrable_of_hasCompactSupport
      (hasCompactSupport_of_unitBall_real fun ζ hζ => by
        simp [dDir_dbarDir_chiOneC_eq_zero _ _ hζ])
  have hcore := leviForm_integral_ge hρ hp hc hΦ hY hXh hRh hX0 hR0 hX hR hpsh ha₁ ha₂ hb₁
  rw [leviForm_integral_chi_eq hp hc] at hcore
  have hLwt' : ∫ ζ, p (c 0 ζ) * leviForm (fun τ => wt τ ζ) 0 1 =
      ∫ ζ, p (c 0 ζ) * (∑ a, ∑ b, M a b *
        dDir (coordinateVector a) (dbarDir (coordinateVector b) (chiOneC n)) ζ).re :=
    integral_congr_ae (Filter.Eventually.of_forall fun ζ => by simp only [hLwt])
  rw [step, integral_add hI1 hI2, hLwt']
  linarith

/-! ### The double divergences `∂_a ∂̄_b χ₁(|ζ|²)` -/

/-- `∂_a ∂̄_b χ₁(|ζ|²) = χ'(|ζ|²) ζ̄_a ζ_b + χ(|ζ|²) δ_{ab}`: the Levi form of a radial weight
`χ(Q_τ(ζ))` with `Q_0 = |·|²`, `D_τQ_0 = 0` is `χ' L_τQ`, and these identities write it as a double
divergence up to `χ tr` (FPT Step 3, the curvature term). -/
theorem dDir_dbarDir_chiOneC (a b : Fin n) (ζ : ComplexModel n) :
    dDir (coordinateVector a) (dbarDir (coordinateVector b) (chiOneC n)) ζ =
      deriv (chi n) (‖ζ‖ ^ 2) * conj (ζ a) * ζ b + (chi n (‖ζ‖ ^ 2) : ℂ) * (if a = b then 1 else 0) := by
  have h1 : dbarDir (coordinateVector b) (chiOneC n) = fun y =>
      ((chi n (‖y‖ ^ 2) : ℝ) : ℂ) * y b := by
    funext y
    exact dbarDir_chiOne_normSq y b
  rw [h1]
  have hχd : DifferentiableAt ℝ (fun y : ComplexModel n => ((chi n (‖y‖ ^ 2) : ℝ) : ℂ)) ζ :=
    ((contDiff_ofReal_comp (contDiff_chi_normSq (n := n))).differentiable (by simp)) ζ
  have hcd : DifferentiableAt ℝ (fun y : ComplexModel n => y b) ζ :=
    ((EuclideanSpace.proj (𝕜 := ℂ) b).restrictScalars ℝ).differentiableAt
  rw [dDir_mul hχd hcd]
  have hχ' : HasDerivAt (chi n) (deriv (chi n) (‖ζ‖ ^ 2)) (‖ζ‖ ^ 2) :=
    ((contDiff_chi n).differentiable (by simp) _).hasDerivAt
  rw [dDir_radial hχ' a]
  have hcoord : dDir (coordinateVector a) (fun y : ComplexModel n => y b) ζ =
      if a = b then 1 else 0 := by
    have hd : DifferentiableAt ℂ (fun y : ComplexModel n => y b) ζ :=
      (EuclideanSpace.proj (𝕜 := ℂ) b).differentiableAt
    rw [dDir_eq_fderiv_of_differentiableAt hd]
    have : fderiv ℂ (fun y : ComplexModel n => y b) ζ = EuclideanSpace.proj (𝕜 := ℂ) b :=
      (EuclideanSpace.proj (𝕜 := ℂ) b).fderiv
    rw [this]
    simp [coordinateVector, Pi.single_apply, eq_comm]
  rw [hcoord]

/-- `∫ ∂_a ∂̄_b χ₁(|ζ|²) dζ = 0`. -/
theorem integral_dDir_dbarDir_chiOneC (a b : Fin n) :
    ∫ ζ, dDir (coordinateVector a) (dbarDir (coordinateVector b) (chiOneC n)) ζ = 0 := by
  have hN2 : ContDiff ℝ 2 (chiOneC n) := (contDiff_chiOneC (n := n)).of_le (by norm_cast)
  have hdb : ContDiff ℝ 1 (dbarDir (coordinateVector b) (chiOneC n)) :=
    contDiff_dbarDir (k := 1) hN2
  have h := integral_mul_dDir_eq_neg (μ := volume) (f := fun _ : ComplexModel n => (1 : ℂ))
    (g := dbarDir (coordinateVector b) (chiOneC n)) contDiff_const hdb
    (Or.inr (hasCompactSupport_dbarDir hasCompactSupport_chiOneC _)) (coordinateVector a)
  simp only [one_mul] at h
  rw [h]
  have h0 : dDir (coordinateVector a) (fun _ : ComplexModel n => (1 : ℂ)) = fun _ => 0 := by
    funext y; simp [dDir]
  simp [h0]

end SGPT.NPP.DN4
