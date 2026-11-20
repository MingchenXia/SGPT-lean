import SGPT.PSH.HermitianComparisonOneFactor
import SGPT.PSH.HermitianComparisonPositivePart

/-!
# Strict comparison sets in bounded one-factor integration by parts

The cutoff derivatives converge to the literal strict-set indicator,
including on the coincidence set. All weighted currents are multiplied
through their actual positive coefficient measures.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonStrict

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
  SGPT.Foundations.Analysis.Pending.LocalProductCurrents
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorForms
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmooth
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorContinuity
  SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue
open SGPT.PSH.HermitianComparisonOneFactor SGPT.PSH.HermitianComparisonCutoff
  SGPT.PSH.HermitianComparisonPositivePart
  SGPT.PSH.HermitianComparisonDensity
open scoped Distributions ContDiff Topology

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {n q : ℕ} {U : Opens (ComplexModel n)}

/-- Pointwise bounded Borel convergence against a fixed genuine positive
current is actual coefficient-measure dominated convergence. -/
theorem weakTendsto_mulBorel_bounded {T : LocalProductCurrent n U q} (hT : IsPositive T)
    {f : ℕ → ComplexModel n → ℝ} {f₀ : ComplexModel n → ℝ}
    (hf : ∀ j, Measurable (f j)) (hf₀ : Measurable f₀)
    (hlim : ∀ x ∈ U, Tendsto (fun j => f j x) atTop (𝓝 (f₀ x)))
    {M : ℝ} (_hM : 0 ≤ M) (hbound : ∀ j x, x ∈ U → |f j x| ≤ M) :
    WeakTendsto (fun j => mulBorel T (f j)) (mulBorel T f₀) := by
  have hb : ∀ j, IsLocallyBoundedOn (f j) U :=
    fun j K _ hKU => ⟨M, fun x hx => hbound j x (hKU hx)⟩
  have hb₀ : IsLocallyBoundedOn f₀ U := by
    intro K _ hKU
    exact ⟨M, fun x hx => le_of_tendsto' (hlim x (hKU hx)).abs
      (fun j => hbound j x (hKU hx))⟩
  intro γ φ
  simp only [mulBorel_apply hT (hf _) (hb _), mulBorel_apply hT hf₀ hb₀]
  have hbase : Integrable (fun x => φ x * hT.density γ x) hT.traceMeasure := by
    simpa only [one_mul] using hT.integrable_mul_density (u := fun _ => 1)
      measurable_const (fun _ _ _ => ⟨1, fun _ _ => by norm_num⟩) γ φ
  apply tendsto_integral_of_dominated_convergence
    (fun x => M * |φ x * hT.density γ x|)
  · intro j
    exact (φ.continuous.measurable.mul ((hf j).mul (hT.measurable_density γ))).aestronglyMeasurable
  · exact hbase.abs.const_mul M
  · intro j
    filter_upwards [] with x
    by_cases hx : x ∈ U
    · simp only [Real.norm_eq_abs, abs_mul]
      have h := mul_le_mul_of_nonneg_right (hbound j x hx)
        (mul_nonneg (abs_nonneg (φ x)) (abs_nonneg (hT.density γ x)))
      nlinarith only [h]
    · have hφ : φ x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hs => hx (φ.tsupport_subset hs))
      simp only [hφ, zero_mul, norm_zero, abs_zero, mul_zero, le_refl]
  · filter_upwards [] with x
    by_cases hx : x ∈ U
    · exact tendsto_const_nhds.mul ((hlim x hx).mul tendsto_const_nhds)
    · have hφ : φ x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hs => hx (φ.tsupport_subset hs))
      simpa only [hφ, zero_mul] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem measurable_indicator_difference_comp {a b : ComplexModel n → ℝ}
    (ha : Measurable ((U : Set (ComplexModel n)).indicator a))
    (hb : Measurable ((U : Set (ComplexModel n)).indicator b))
    {H : ℝ → ℝ} (hH : Measurable H) :
    Measurable ((U : Set (ComplexModel n)).indicator (fun z => H (b z - a z))) := by
  have he : (U : Set (ComplexModel n)).indicator (fun z => H (b z - a z)) =
      (U : Set (ComplexModel n)).indicator (fun z => H
        ((U : Set (ComplexModel n)).indicator b z -
          (U : Set (ComplexModel n)).indicator a z)) := by
    funext z
    by_cases hz : z ∈ U
    · rw [indicator_of_mem hz, indicator_of_mem hz, indicator_of_mem hz, indicator_of_mem hz]
    · rw [indicator_of_notMem hz, indicator_of_notMem hz]
  rw [he]
  exact (hH.comp (hb.sub ha)).indicator U.isOpen.measurableSet

/-- The literal strict positive-set indicator, with value zero at zero. -/
def strictIndicator (t : ℝ) : ℝ := if 0 < t then 1 else 0

theorem measurable_strictIndicator : Measurable strictIndicator :=
  Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const measurable_const

theorem weightedDdcResidual_cutoff_tendsto {k : ℕ}
    (R : LocalProductCurrent n U (k + 1)) (hR : IsPositive R)
    (hRc : IsClosedCurrent R)
    {α : ComplexModel n → RealForm n (2 * k)} (hα : ContDiffOn ℝ ∞ α U)
    {u a b : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn U u) (ha : IsLocallyBoundedPshOn U a)
    (hb : IsLocallyBoundedPshOn U b) :
    WeakTendsto (fun j => weightedDdcResidual R hα u a b (deriv (cutoff (scale j))))
      (weightedDdcResidual R hα u a b strictIndicator) := by
  have ham := measurable_indicator_of_isLocallyBoundedPshOn ha
  have hbm := measurable_indicator_of_isLocallyBoundedPshOn hb
  apply SGPT.PSH.HermitianProducts.weakTendsto_wedgeForm
  refine weakTendsto_mulBorel_bounded (isPositive_ddcMul hR hRc hu).1
    (M := 1) ?_ ?_ ?_ zero_le_one ?_
  · intro j
    exact measurable_indicator_difference_comp ham hbm
      ((contDiff_infty_iff_deriv.mp (contDiff_cutoff (scale j))).2.continuous.measurable)
  · exact measurable_indicator_difference_comp ham hbm measurable_strictIndicator
  · intro x hx
    simpa only [indicator_of_mem hx, strictIndicator] using deriv_cutoff_tendsto (b x - a x)
  · intro j x hx
    rw [indicator_of_mem hx]
    exact abs_le.mpr ⟨by linarith [(deriv_cutoff_mem_Icc (scale_pos j) (b x - a x)).1],
      (deriv_cutoff_mem_Icc (scale_pos j) (b x - a x)).2⟩

theorem weightedDifference_cutoff_tendsto {ι : Type*} [Fintype ι]
    (D : ι → Residual n U) {a b : ComplexModel n → ℝ}
    (ha : IsLocallyBoundedPshOn U a) (hb : IsLocallyBoundedPshOn U b) :
    WeakTendsto (fun j => weightedDifference D a b (deriv (cutoff (scale j))))
      (weightedDifference D a b strictIndicator) := by
  intro γ φ
  simp only [weightedDifference, LinearMap.sum_apply, _root_.sum_apply,
    LinearMap.sub_apply, _root_.sub_apply]
  apply tendsto_finsetSum
  intro i _
  exact ((weightedDdcResidual_cutoff_tendsto (D i).current (D i).positive
    (D i).closed (D i).smooth hb ha hb) γ φ).sub
    ((weightedDdcResidual_cutoff_tendsto (D i).current (D i).positive
      (D i).closed (D i).smooth ha ha hb) γ φ)

theorem ddcWedgePairing_congr_on {r k m : ℕ} (h' : r + k = m)
    {R : LocalProductCurrent n U (m + 1)} (hR : IsPositive R)
    (α : ComplexModel n → RealForm n (2 * k)) (γ : formSpan n r) (φ : 𝓓(U, ℝ))
    {f g : ComplexModel n → ℝ} (hfg : ∀ x ∈ U, f x = g x) :
    ddcWedgePairing h' hR α γ φ f = ddcWedgePairing h' hR α γ φ g := by
  unfold ddcWedgePairing
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ U
  · rw [hfg x hx]
  · have hφ : φ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun hs => hx (φ.tsupport_subset hs))
    simp only [hφ, zero_mul, mul_zero]

theorem localizedDerivativeWeight_congr_on {ι : Type*} [Fintype ι]
    (D : ι → Residual n U) (χ η : 𝓓(U, ℝ)) {f g : ComplexModel n → ℝ}
    (hfg : ∀ x ∈ U, f x = g x) :
    localizedDerivativeWeight D χ η f = localizedDerivativeWeight D χ η g := by
  unfold localizedDerivativeWeight
  exact Finset.sum_congr rfl (fun i _ => ddcWedgePairing_congr_on _
    (D i).positive _ scalarUnit η hfg)

theorem localizedDerivativeWeight_cutoff_tendsto {ι : Type*} [Fintype ι]
    (D : ι → Residual n U) (χ η : 𝓓(U, ℝ))
    {a b : ComplexModel n → ℝ} (ha : IsLocallyBoundedPshOn U a)
    (hb : IsLocallyBoundedPshOn U b)
    {M : ℝ} (haM : ∀ x ∈ U, |a x| ≤ M) (hbM : ∀ x ∈ U, |b x| ≤ M) :
    Tendsto (fun j => localizedDerivativeWeight D χ η
        (fun x => cutoff (scale j) (b x - a x))) atTop
      (𝓝 (localizedDerivativeWeight D χ η (fun x => max (b x - a x) 0))) := by
  let a' := (U : Set (ComplexModel n)).indicator a
  let b' := (U : Set (ComplexModel n)).indicator b
  have ham : Measurable a' := measurable_indicator_of_isLocallyBoundedPshOn ha
  have hbm : Measurable b' := measurable_indicator_of_isLocallyBoundedPshOn hb
  have hlim := localizedDerivativeWeight_tendsto D χ η
    (f := fun j x => cutoff (scale j) (b' x - a' x))
    (f₀ := fun x => max (b x - a x) 0)
    (fun j => (contDiff_cutoff (scale j)).continuous.measurable.comp (hbm.sub ham))
    (fun x hx => by simpa only [a', b', indicator_of_mem hx] using cutoff_tendsto (b x - a x))
  have hbound : ∃ B : ℝ, 0 ≤ B ∧ ∀ j x, x ∈ tsupport η →
      |cutoff (scale j) (b' x - a' x)| ≤ B := by
    refine ⟨2 * |M| + 1, by positivity, fun j x hx => ?_⟩
    have hxU := η.tsupport_subset hx
    have hsub := abs_sub_le (b x) 0 (a x)
    simp only [sub_zero, zero_sub, abs_neg] at hsub
    have hw : |b x - a x| ≤ 2 * |M| := by
      linarith [haM x hxU, hbM x hxU, le_abs_self M]
    have hs : scale j ≤ 1 := by
      unfold scale
      apply (div_le_one (by positivity : 0 < (j : ℝ) + 1)).mpr
      exact le_add_of_nonneg_left (Nat.cast_nonneg j)
    have hc := cutoff_bounds (scale_pos j) (b x - a x)
    have hm : max (b x - a x) 0 ≤ 2 * |M| :=
      max_le ((le_abs_self _).trans hw) (by positivity)
    simp only [a', b', indicator_of_mem hxU]
    exact abs_le.mpr ⟨by linarith [le_max_right (b x - a x) 0], by linarith⟩
  have heq : ∀ j, localizedDerivativeWeight D χ η
      (fun x => cutoff (scale j) (b x - a x)) =
      localizedDerivativeWeight D χ η (fun x => cutoff (scale j) (b' x - a' x)) := by
    intro j
    apply localizedDerivativeWeight_congr_on
    intro x hx
    simp only [a', b', indicator_of_mem hx]
  simp only [heq]
  exact hlim hbound

/-- One-factor integration by parts on the literal strict comparison set.
The left side uses the indicator `a<b`; the right side is the genuine
bounded-density extension of `ddᶜ(χS)` weighted by `(b-a)⁺`. Both the bounded
potential passage and the convex-cutoff passage are proved internally. -/
theorem strict_local_onefactor {ι : Type*} [Fintype ι]
    (D : ι → Residual n U) (hS : IsPositive (mixedCurrent D))
    (χ : 𝓓(U, ℝ)) (hχ : ∀ z, 0 ≤ χ z) (η : 𝓓(U, ℝ))
    (hη : ∀ᶠ z in 𝓝ˢ (tsupport χ), η z = 1)
    (a b : ℕ → ComplexModel n → ℝ) (a₀ b₀ : ComplexModel n → ℝ)
    (has : ∀ j, ContDiff ℝ ∞ (a j)) (hbs : ∀ j, ContDiff ℝ ∞ (b j))
    (hap : ∀ j, PlurisubharmonicOn (fun z => (a j z : EReal)) U)
    (hbp : ∀ j, PlurisubharmonicOn (fun z => (b j z : EReal)) U)
    (ha₀ : IsLocallyBoundedPshOn U a₀) (hb₀ : IsLocallyBoundedPshOn U b₀)
    (hanti_a : ∀ z ∈ U, Antitone fun j => a j z)
    (hanti_b : ∀ z ∈ U, Antitone fun j => b j z)
    (hlim_a : ∀ z ∈ U, Tendsto (fun j => a j z) atTop (𝓝 (a₀ z)))
    (hlim_b : ∀ z ∈ U, Tendsto (fun j => b j z) atTop (𝓝 (b₀ z)))
    {M : ℝ} (hbound_a : ∀ j z, z ∈ U → |a j z| ≤ M)
    (hbound_b : ∀ j z, z ∈ U → |b j z| ≤ M) :
    weightedDifference D a₀ b₀ strictIndicator scalarUnit χ ≤
      localizedDerivativeWeight D χ η (fun z => max (b₀ z - a₀ z) 0) := by
  have hleft := weightedDifference_cutoff_tendsto D ha₀ hb₀ scalarUnit χ
  have hright := localizedDerivativeWeight_cutoff_tendsto D χ η ha₀ hb₀
    (fun x hx => le_of_tendsto' (hlim_a x hx).abs (fun j => hbound_a j x hx))
    (fun x hx => le_of_tendsto' (hlim_b x hx).abs (fun j => hbound_b j x hx))
  exact le_of_tendsto_of_tendsto' hleft hright (fun j =>
    bounded_local_onefactor D hS χ hχ η hη a b a₀ b₀ has hbs hap hbp ha₀ hb₀
      hanti_a hanti_b hlim_a hlim_b (contDiff_cutoff (scale j))
      (cutoff_secondDeriv_nonneg (scale_pos j)) hbound_a hbound_b)

/-- The strict comparison-set one-factor estimate for the existing actual
nonclosed-background product expansion. Its finite residual presentation
is constructed from the selected ordinary Bedford--Taylor factors. -/
theorem strict_background_onefactor (p : ℕ) (T : LocalProductCurrent n U (1 + p))
    (hT : IsPositive T) (hTc : IsClosedAny (1 + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hS : IsPositive (SGPT.PSH.HermitianProducts.backgroundExpansion p 1 v hσ T))
    (χ : 𝓓(U, ℝ)) (hχ : ∀ z, 0 ≤ χ z) (η : 𝓓(U, ℝ))
    (hη : ∀ᶠ z in 𝓝ˢ (tsupport χ), η z = 1)
    (a b : ℕ → ComplexModel n → ℝ) (a₀ b₀ : ComplexModel n → ℝ)
    (has : ∀ j, ContDiff ℝ ∞ (a j)) (hbs : ∀ j, ContDiff ℝ ∞ (b j))
    (hap : ∀ j, PlurisubharmonicOn (fun z => (a j z : EReal)) U)
    (hbp : ∀ j, PlurisubharmonicOn (fun z => (b j z : EReal)) U)
    (ha₀ : IsLocallyBoundedPshOn U a₀) (hb₀ : IsLocallyBoundedPshOn U b₀)
    (hanti_a : ∀ z ∈ U, Antitone fun j => a j z)
    (hanti_b : ∀ z ∈ U, Antitone fun j => b j z)
    (hlim_a : ∀ z ∈ U, Tendsto (fun j => a j z) atTop (𝓝 (a₀ z)))
    (hlim_b : ∀ z ∈ U, Tendsto (fun j => b j z) atTop (𝓝 (b₀ z)))
    {M : ℝ} (hbound_a : ∀ j z, z ∈ U → |a j z| ≤ M)
    (hbound_b : ∀ j z, z ∈ U → |b j z| ≤ M) :
    weightedDifference (backgroundResidual p T hT hTc v hv hσ) a₀ b₀ strictIndicator scalarUnit χ ≤
      localizedDerivativeWeight (backgroundResidual p T hT hTc v hv hσ) χ η
        (fun z => max (b₀ z - a₀ z) 0) := by
  classical
  apply strict_local_onefactor _ _ χ hχ η hη a b a₀ b₀ has hbs hap hbp ha₀ hb₀
    hanti_a hanti_b hlim_a hlim_b hbound_a hbound_b
  rw [mixedCurrent_backgroundResidual]
  exact hS

end SGPT.PSH.HermitianComparisonStrict
