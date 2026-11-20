import SGPT.Okounkov.LegendreEnergy

noncomputable section

namespace SGPT.Okounkov

open Set Filter MeasureTheory
open scoped Topology

/-- Actual finite positive and negative parts produce real integrability, retaining the original finite-AE premise. -/
theorem integrable_toReal_of_finite_parts {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (g : A → EReal) (hg : Measurable g)
    (hfin : ∀ᵐ x ∂μ, g x ≠ ⊤ ∧ g x ≠ ⊥)
    (hp : (∫⁻ x, (g x).toENNReal ∂μ) < ⊤)
    (hn : (∫⁻ x, (-g x).toENNReal ∂μ) < ⊤) :
    Integrable (fun x ↦ (g x).toReal) μ := by
  refine ⟨hg.ereal_toReal.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have hbound : ∀ᵐ x ∂μ, ENNReal.ofReal ‖(g x).toReal‖ ≤
      (g x).toENNReal + (-g x).toENNReal := by
    filter_upwards [hfin] with x hx
    rw [← EReal.coe_toReal hx.1 hx.2]
    simp only [EReal.toReal_coe, ← EReal.coe_neg, EReal.real_coe_toENNReal, Real.norm_eq_abs]
    by_cases h : 0 ≤ (g x).toReal
    · rw [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (neg_nonpos.mpr h), add_zero]
    · rw [abs_of_neg (lt_of_not_ge h), ENNReal.ofReal_of_nonpos (le_of_not_ge h), zero_add]
  apply lt_of_le_of_lt (lintegral_mono_ae hbound)
  rw [lintegral_add_left hg.ereal_toENNReal]
  exact ENNReal.add_lt_top.mpr ⟨hp, hn⟩

/-- The actual signed integral agrees with the produced real integral when its genuine parts are finite. -/
theorem signedIntegral_eq_coe_integral_of_finite_parts {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (g : A → EReal) (hg : Measurable g)
    (hfin : ∀ᵐ x ∂μ, g x ≠ ⊤ ∧ g x ≠ ⊥)
    (hp : (∫⁻ x, (g x).toENNReal ∂μ) < ⊤)
    (hn : (∫⁻ x, (-g x).toENNReal ∂μ) < ⊤) :
    SGPT.Convex.extendedSignedIntegral μ g = ((∫ x, (g x).toReal ∂μ : ℝ) : EReal) := by
  have hint := integrable_toReal_of_finite_parts μ g hg hfin hp hn
  have hpos : (∫⁻ x, ENNReal.ofReal (g x).toReal ∂μ) = ∫⁻ x, (g x).toENNReal ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hfin] with x hx
    rw [← EReal.coe_toReal hx.1 hx.2, EReal.toReal_coe, EReal.real_coe_toENNReal]
  have hneg : (∫⁻ x, ENNReal.ofReal (-(g x).toReal) ∂μ) = ∫⁻ x, (-g x).toENNReal ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hfin] with x hx
    rw [← EReal.coe_toReal hx.1 hx.2]
    simp only [EReal.toReal_coe, ← EReal.coe_neg, EReal.real_coe_toENNReal]
  rw [SGPT.Convex.extendedSignedIntegral,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint, hpos, hneg,
    ← EReal.coe_ennreal_toReal hp.ne, ← EReal.coe_ennreal_toReal hn.ne, ← EReal.coe_sub]

namespace TestFunction

variable {n : ℕ} {Δ : ConvexBody (EuclideanSpace ℝ (Fin n))} (G : TestFunction Δ)

/-- The original finite-energy condition genuinely produces integrability of the original real representative. -/
theorem integrable_toReal_of_hasFiniteEnergy (hE : G.HasFiniteEnergy) :
    Integrable (fun x ↦ (G.valueAt x).toReal)
      (volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n)))) :=
  integrable_toReal_of_finite_parts _ _ G.measurable_valueAt G.valueAt_finite_ae
    G.energy_positive_lintegral_lt_top (G.hasFiniteEnergy_iff_negative_part_lt_top.mp hE)

/-- Actual finite original energy is exactly its genuine factorial-normalized real integral. -/
theorem energy_eq_coe_integral_of_hasFiniteEnergy (hE : G.HasFiniteEnergy) :
    G.energy = (((n.factorial : ℝ) *
      ∫ x, (G.valueAt x).toReal ∂volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n))) : ℝ) : EReal) := by
  rw [energy, signedIntegral_eq_coe_integral_of_finite_parts _ _ G.measurable_valueAt
    G.valueAt_finite_ae G.energy_positive_lintegral_lt_top
      (G.hasFiniteEnergy_iff_negative_part_lt_top.mp hE), ← EReal.coe_natCast, ← EReal.coe_mul]

/-- Exact literal source energy values, including the original divergent negative-energy branch. -/
theorem inverseLegendre_energy_eq
    (hΔ : 0 < volume (Δ : Set (EuclideanSpace ℝ (Fin n)))) :
    (G.inverseLegendre hΔ).energy = G.energy := by
  by_cases hE : G.HasFiniteEnergy
  · let μ := volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n)))
    let : IsFiniteMeasure μ := ⟨by
      dsimp only [μ]
      rw [Measure.restrict_apply_univ]
      exact Δ.isCompact.measure_lt_top⟩
    have hg := G.integrable_toReal_of_hasFiniteEnergy hE
    have hgapInt : Integrable (fun x ↦ G.maxReal - (G.valueAt x).toReal) μ :=
      (integrable_const G.maxReal).sub hg
    have hnonneg := G.real_heightGap_nonnegative_ae
      (SGPT.AlmostSemigroup.ConvexIntersection.interior_nonempty_of_measure_pos volume Δ.convex hΔ)
    have hgapEq := G.heightGap_eq_real_ae
    have hD : (∫⁻ x, ((G.maxReal : EReal) - G.valueAt x).toENNReal ∂μ) =
        ENNReal.ofReal (G.maxReal * volume.real (Δ : Set (EuclideanSpace ℝ (Fin n))) -
          ∫ x, (G.valueAt x).toReal ∂μ) := by
      rw [lintegral_congr_ae hgapEq, ← ofReal_integral_eq_lintegral_ofReal hgapInt hnonneg,
        integral_sub (integrable_const G.maxReal) hg, integral_const, smul_eq_mul]
      have hμ : μ.real univ = volume.real (Δ : Set (EuclideanSpace ℝ (Fin n))) := by
        change ((volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n)))) univ).toReal = _
        rw [Measure.restrict_apply_univ]
        rfl
      rw [hμ, mul_comm]
    have hdiff : 0 ≤ G.maxReal * volume.real (Δ : Set (EuclideanSpace ℝ (Fin n))) -
        ∫ x, (G.valueAt x).toReal ∂μ := by
      have h := integral_nonneg_of_ae hnonneg
      rw [integral_sub (integrable_const G.maxReal) hg, integral_const, smul_eq_mul] at h
      change 0 ≤ μ.real univ * G.maxReal - ∫ x, (G.valueAt x).toReal ∂μ at h
      have hμ : μ.real univ = volume.real (Δ : Set (EuclideanSpace ℝ (Fin n))) := by
        change ((volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n)))) univ).toReal = _
        rw [Measure.restrict_apply_univ]
        rfl
      simpa only [hμ, mul_comm] using h
    rw [(G.inverseLegendre hΔ).energy_eq_deficit,
      ← G.lintegral_heightGap_eq_volume_deficit hΔ, hD,
      G.energy_eq_coe_integral_of_hasFiniteEnergy hE, EReal.coe_ennreal_ofReal, max_eq_left hdiff]
    change (((n.factorial : ℝ) * G.maxReal * volume.real (Δ : Set (EuclideanSpace ℝ (Fin n))) : ℝ) : EReal) -
      ((n.factorial : ℝ) : EReal) * ((G.maxReal * volume.real (Δ : Set (EuclideanSpace ℝ (Fin n))) -
        ∫ x, (G.valueAt x).toReal ∂μ : ℝ) : EReal) = _
    rw [← EReal.coe_mul, ← EReal.coe_sub]
    congr 1
    ring
  · have hGE : G.energy = ⊥ := le_antisymm (le_of_not_gt hE) bot_le
    have hCE : (G.inverseLegendre hΔ).energy = ⊥ := by
      apply le_antisymm _ bot_le
      apply le_of_not_gt
      exact fun h ↦ hE (G.inverseLegendre_hasFiniteEnergy_iff hΔ |>.mp h)
    rw [hCE, hGE]

end TestFunction

namespace TestCurve

variable {n : ℕ} {Δ : ConvexBody (EuclideanSpace ℝ (Fin n))} (K : SGPT.Okounkov.TestCurve Δ)

/-- Literal original curve/function energy equality in the genuine forward Legendre direction. -/
theorem toTestFunction_energy_eq
    (hΔ : 0 < volume (Δ : Set (EuclideanSpace ℝ (Fin n)))) :
    K.toTestFunction.energy = K.energy := by
  have hint := SGPT.AlmostSemigroup.ConvexIntersection.interior_nonempty_of_measure_pos volume Δ.convex hΔ
  have h := K.toTestFunction.inverseLegendre_energy_eq hΔ
  have hcurve : K.toTestFunction.inverseLegendre hΔ = K := K.inverse_forward hint
  rw [hcurve] at h
  exact h.symm

end TestCurve

end SGPT.Okounkov
