import SGPT.Envelopes.MADirichlet6Approximants

/-!
# The generalized Hölder inequality for the common measure, and constants in mixed products

Xia, *Foundations of pluripotential theory* (FPT), proof of `thm:bounded-multifactor-common-measure`:
for a positive measure `ν`, a measurable set `A` and nonnegative measurable `gᵢ`,
`∫_A ∏ᵢ gᵢ^{1/n} dν ≤ ∏ᵢ (∫_A gᵢ dν)^{1/n}` (FPT `eq:generalized-holder-geometric-mean`).

* `lintegral_withDensity_prod_rpow_le`: if `(fᵢ μ)|_K ≤ αᵢ` for all `i`, then for every measurable
  `g ≥ 0`, `∫ g d(λ|_K) ≤ ∏ᵢ (∫ g dαᵢ)^{1/n}` where `λ = (∏ᵢ fᵢ^{1/n}) μ` (Mathlib's
  `ENNReal.lintegral_prod_norm_pow_le` applied to `gᵢ = g fᵢ`).
* `ofReal_convDensity_le_prod`: the convolution form used in Step 2 (FPT
  `eq:common-measure-grid-holder`, with the kernel `ρⱼ(x - ·)` in place of the indicator of a
  cube): `λ ∗ ρⱼ ≤ ∏ᵢ (αᵢ ∗ ρⱼ)^{1/n}` pointwise.
* `prod_rpow_inv_le_sum`: `∏ᵢ aᵢ^{1/n} ≤ ∑ᵢ aᵢ` in `[0, ∞]`.
* `canonicalMixedBedfordTaylorMeasure_add_const`: adding constants to the potentials does not
  change the mixed Bedford–Taylor measure (TN's gauge invariance `IsBTLimit.add_pluriharmonic`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.HolomorphicPullback

variable {n : ℕ}

/-- `∏ᵢ a^{1/n} = a` over `Fin n`, `n > 0`. -/
theorem prod_rpow_inv_const (hn : 0 < n) (a : ℝ≥0∞) : ∏ _i : Fin n, a ^ ((n : ℝ)⁻¹) = a := by
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.rpow_inv_natCast_pow hn.ne']

/-- `∏ᵢ aᵢ^{1/n} ≤ ∑ᵢ aᵢ` in `[0, ∞]`. -/
theorem prod_rpow_inv_le_sum (hn : 0 < n) (a : Fin n → ℝ≥0∞) :
    ∏ i, a i ^ ((n : ℝ)⁻¹) ≤ ∑ i, a i := by
  have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  calc ∏ i, a i ^ ((n : ℝ)⁻¹) ≤ ∏ _i : Fin n, (∑ k, a k) ^ ((n : ℝ)⁻¹) :=
        Finset.prod_le_prod (fun _ _ => zero_le) fun i _ =>
          ENNReal.rpow_le_rpow (Finset.single_le_sum (fun k _ => zero_le)
            (Finset.mem_univ i)) hninv
    _ = ∑ k, a k := prod_rpow_inv_const hn _

/-- `c ∏ᵢ (gᵢ/c)^{1/n} = ∏ᵢ gᵢ^{1/n}` for `c > 0`, `gᵢ ≥ 0` (the exponents `1/n` sum to one). -/
theorem mul_prod_div_rpow_inv (hn : 0 < n) {c : ℝ} (hc : 0 < c) {g : Fin n → ℝ}
    (hg : ∀ i, 0 ≤ g i) :
    c * ∏ i, (g i / c) ^ ((n : ℝ)⁻¹) = ∏ i, g i ^ ((n : ℝ)⁻¹) := by
  simp_rw [Real.div_rpow (hg _) hc.le]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Real.rpow_inv_natCast_pow hc.le hn.ne']
  field_simp

/-- **The generalized Hölder inequality for the common measure** (FPT
`eq:generalized-holder-geometric-mean`): if `(fᵢ μ)|_K ≤ αᵢ` for every `i`, then
`∫ g d((∏ᵢ fᵢ^{1/n}) μ)|_K ≤ ∏ᵢ (∫ g dαᵢ)^{1/n}` for every measurable `g ≥ 0`. -/
theorem lintegral_withDensity_prod_rpow_le {X : Type*} [MeasurableSpace X] (hn : 0 < n)
    (μ : Measure X) {K : Set X} (hK : MeasurableSet K) {f : Fin n → X → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) {α : Fin n → Measure X}
    (hfα : ∀ i, (μ.withDensity (f i)).restrict K ≤ α i) {g : X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂(μ.withDensity fun z => ∏ i, f i z ^ ((n : ℝ)⁻¹)).restrict K ≤
      ∏ i, (∫⁻ x, g x ∂α i) ^ ((n : ℝ)⁻¹) := by
  have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  have hsum : ∑ _i : Fin n, (n : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hΦ : Measurable fun z => ∏ i, f i z ^ ((n : ℝ)⁻¹) :=
    Finset.measurable_prod _ fun i _ => (hf i).pow_const _
  rw [restrict_withDensity hK, lintegral_withDensity_eq_lintegral_mul _ hΦ hg]
  have hpt : ∀ x, ((fun z => ∏ i, f i z ^ ((n : ℝ)⁻¹)) * g) x =
      ∏ i, (f i x * g x) ^ ((n : ℝ)⁻¹) := by
    intro x
    simp only [Pi.mul_apply, ENNReal.mul_rpow_of_nonneg _ _ hninv, Finset.prod_mul_distrib,
      prod_rpow_inv_const hn]
  calc ∫⁻ x, ((fun z => ∏ i, f i z ^ ((n : ℝ)⁻¹)) * g) x ∂μ.restrict K
      = ∫⁻ x, ∏ i, (f i x * g x) ^ ((n : ℝ)⁻¹) ∂μ.restrict K := lintegral_congr fun x => hpt x
    _ ≤ ∏ i, (∫⁻ x, f i x * g x ∂μ.restrict K) ^ ((n : ℝ)⁻¹) :=
        ENNReal.lintegral_prod_norm_pow_le Finset.univ
          (fun i _ => ((hf i).mul hg).aemeasurable) hsum (fun i _ => hninv)
    _ ≤ ∏ i, (∫⁻ x, g x ∂α i) ^ ((n : ℝ)⁻¹) := by
        refine Finset.prod_le_prod (fun _ _ => zero_le) fun i _ =>
          ENNReal.rpow_le_rpow ?_ hninv
        calc ∫⁻ x, f i x * g x ∂μ.restrict K
            = ∫⁻ x, g x ∂(μ.restrict K).withDensity (f i) :=
              (lintegral_withDensity_eq_lintegral_mul _ (hf i) hg).symm
          _ = ∫⁻ x, g x ∂(μ.withDensity (f i)).restrict K := by rw [restrict_withDensity hK]
          _ ≤ ∫⁻ x, g x ∂α i := lintegral_mono' (hfα i) le_rfl

/-- The density of `ν ∗ ρⱼ` as a lower integral. -/
theorem ofReal_convDensity_eq_lintegral (ν : Measure (ComplexModel n)) [IsFiniteMeasure ν]
    {r : ℝ} (hr : 0 < r) (j : ℕ) (x : ComplexModel n) :
    ENNReal.ofReal (convDensity ν r hr j x) =
      ∫⁻ t, ENNReal.ofReal (explicitRadialKernel r hr j (x - t)) ∂ν := by
  rw [convDensity, ofReal_integral_eq_lintegral_ofReal (integrable_explicitRadialKernel_sub ν hr j x)
    (Eventually.of_forall fun t => explicitRadialKernel_nonneg r hr j (x - t))]

/-- **Hölder's inequality for the convolutions** (FPT `eq:common-measure-grid-holder`, convolution
variant): if `∫ g dν ≤ ∏ᵢ (∫ g dαᵢ)^{1/n}` for every measurable `g ≥ 0`, then
`ν ∗ ρⱼ ≤ ∏ᵢ (αᵢ ∗ ρⱼ)^{1/n}` pointwise. -/
theorem ofReal_convDensity_le_prod {ν : Measure (ComplexModel n)} [IsFiniteMeasure ν]
    {α : Fin n → Measure (ComplexModel n)} [∀ i, IsFiniteMeasure (α i)]
    (hle : ∀ g : ComplexModel n → ℝ≥0∞, Measurable g →
      ∫⁻ x, g x ∂ν ≤ ∏ i, (∫⁻ x, g x ∂α i) ^ ((n : ℝ)⁻¹))
    {r : ℝ} (hr : 0 < r) (j : ℕ) (x : ComplexModel n) :
    ENNReal.ofReal (convDensity ν r hr j x) ≤
      ∏ i, ENNReal.ofReal (convDensity (α i) r hr j x) ^ ((n : ℝ)⁻¹) := by
  have hg : Measurable fun t => ENNReal.ofReal (explicitRadialKernel r hr j (x - t)) :=
    ENNReal.measurable_ofReal.comp ((explicitRadialKernel_contDiff r hr j).continuous.comp
      (continuous_const.sub continuous_id)).measurable
  rw [ofReal_convDensity_eq_lintegral]
  simp_rw [ofReal_convDensity_eq_lintegral]
  exact hle _ hg

/-- **Constants do not change mixed products**: `ddᶜ(u₁ + c₁) ∧ ⋯ ∧ ddᶜ(uₙ + cₙ) =
ddᶜu₁ ∧ ⋯ ∧ ddᶜuₙ` (TN's gauge invariance of Bedford–Taylor limits). -/
theorem canonicalMixedBedfordTaylorMeasure_add_const {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (hu : IsLocallyBoundedMixedPshOn Ω u) (c : Fin n → ℝ)
    (huc : IsLocallyBoundedMixedPshOn Ω fun i z => u i z + c i) :
    canonicalMixedBedfordTaylorMeasure Ω (fun i z => u i z + c i) huc =
      canonicalMixedBedfordTaylorMeasure Ω u hu := by
  have h1 := (BedfordTaylor.IsLocalMixedBedfordTaylorMeasure.isBTLimit
    (canonicalMixedBedfordTaylorMeasure_spec Ω u hu)).add_pluriharmonic
      (h := fun i _ => c i) fun i => BedfordTaylor.isSmoothPluriharmonicOn_const Ω (c i)
  have h2 := BedfordTaylor.IsLocalMixedBedfordTaylorMeasure.isBTLimit
    (canonicalMixedBedfordTaylorMeasure_spec Ω _ huc)
  exact h2.unique h1

end SGPT.Envelopes.MADirichlet
