import SGPT.Okounkov.LegendreCorrespondence
import Mathlib.MeasureTheory.Integral.Layercake

noncomputable section

namespace SGPT.Okounkov

open Set Filter MeasureTheory
open scoped Topology

/-- Positive finite factorial scaling preserves actual extended-real nonbottom energy. -/
theorem bot_lt_pos_real_mul_iff (c : ℝ) (hc : 0 < c) (a : EReal) :
    (⊥ : EReal) < (c : EReal) * a ↔ ⊥ < a := by
  cases a using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos hc]
  | top => simp [EReal.coe_mul_top_of_pos hc]
  | coe r => simp only [← EReal.coe_mul, EReal.bot_lt_coe]

/-- With its genuinely finite positive part, actual signed energy is nonbottom exactly when its negative part is finite. -/
theorem bot_lt_signedIntegral_iff {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (g : A → EReal) (hp : (∫⁻ x, (g x).toENNReal ∂μ) < ⊤) :
    (⊥ : EReal) < SGPT.Convex.extendedSignedIntegral μ g ↔
      (∫⁻ x, (-g x).toENNReal ∂μ) < ⊤ := by
  unfold SGPT.Convex.extendedSignedIntegral
  rw [← EReal.coe_ennreal_toReal hp.ne]
  by_cases hn : (∫⁻ x, (-g x).toENNReal ∂μ) = ⊤
  · simp [hn]
  · rw [← EReal.coe_ennreal_toReal hn, ← EReal.coe_sub]
    simp only [EReal.bot_lt_coe, lt_top_iff_ne_top]
    exact iff_of_true trivial hn

/-- A finite change of height preserves finiteness of the actual nonnegative negative-part integral. -/
theorem lintegral_heightGap_lt_top_iff {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsFiniteMeasure μ] (g : A → EReal) (c : ℝ) :
    (∫⁻ x, ((c : EReal) - g x).toENNReal ∂μ) < ⊤ ↔
      (∫⁻ x, (-g x).toENNReal ∂μ) < ⊤ := by
  have hfinite (r : ℝ) : ((r : EReal).toENNReal * μ univ) < ⊤ := by
    rw [EReal.real_coe_toENNReal]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ univ)
  constructor
  · intro hgap
    have hle (x : A) : (-g x).toENNReal ≤
        ((-c : ℝ) : EReal).toENNReal + ((c : EReal) - g x).toENNReal := by
      have heq : -g x = ((-c : ℝ) : EReal) + ((c : EReal) - g x) := by
        cases g x using EReal.rec with
        | bot => simp
        | top => simp
        | coe r => rw [← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_neg]; congr 1; ring
      rw [heq]
      exact EReal.toENNReal_add_le
    apply lt_of_le_of_lt (lintegral_mono hle)
    rw [lintegral_add_left measurable_const, lintegral_const]
    exact ENNReal.add_lt_top.mpr ⟨hfinite (-c), hgap⟩
  · intro hneg
    have hle (x : A) : ((c : EReal) - g x).toENNReal ≤
        (c : EReal).toENNReal + (-g x).toENNReal := EReal.toENNReal_add_le
    apply lt_of_le_of_lt (lintegral_mono hle)
    rw [lintegral_add_left measurable_const, lintegral_const]
    exact ENNReal.add_lt_top.mpr ⟨hfinite c, hneg⟩

namespace TestFunction

variable {n : ℕ} {Δ : ConvexBody (EuclideanSpace ℝ (Fin n))} (G : TestFunction Δ)

/-- Original finite test-function energy has exactly its true finite negative-part criterion. -/
theorem hasFiniteEnergy_iff_negative_part_lt_top :
    G.HasFiniteEnergy ↔ (∫⁻ x, (-G.valueAt x).toENNReal
      ∂volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n)))) < ⊤ := by
  change (⊥ : EReal) < ((n.factorial : ℝ) : EReal) *
    SGPT.Convex.extendedSignedIntegral
      (volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n)))) G.valueAt ↔ _
  rw [bot_lt_pos_real_mul_iff _ (by exact_mod_cast Nat.factorial_pos n)]
  exact bot_lt_signedIntegral_iff _ _ G.energy_positive_lintegral_lt_top

/-- Genuine source USC gives actual Borel measurability of the integration representative. -/
theorem measurable_valueAt : Measurable G.valueAt := by
  classical
  exact G.upperSemicontinuous.measurable.dite measurable_const Δ.isCompact.measurableSet

/-- Null convex frontier and the original finite-interior condition give actual finite values almost everywhere on the source body. -/
theorem valueAt_finite_ae : ∀ᵐ x ∂volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n))),
    G.valueAt x ≠ ⊤ ∧ G.valueAt x ≠ ⊥ := by
  have hi := interior_ae_eq_of_null_frontier (Δ.convex.addHaar_frontier volume)
  filter_upwards [ae_restrict_mem Δ.isCompact.measurableSet, ae_restrict_of_ae hi]
    with x hx hxi
  rw [valueAt, dif_pos (show x ∈ Δ from hx)]
  exact ⟨G.ne_top ⟨x, hx⟩, G.finite_interior ⟨x, hx⟩ (hxi.mpr hx)⟩

/-- The actual extended height deficit agrees almost everywhere with the genuine real nonnegative deficit. -/
theorem heightGap_eq_real_ae : ∀ᵐ x ∂volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n))),
    ((G.maxReal : EReal) - G.valueAt x).toENNReal =
      ENNReal.ofReal (G.maxReal - (G.valueAt x).toReal) := by
  filter_upwards [G.valueAt_finite_ae] with x hx
  rw [← EReal.coe_toReal hx.1 hx.2, ← EReal.coe_sub, EReal.real_coe_toENNReal]
  rw [EReal.toReal_coe]

/-- The produced supremum bounds the original finite real values almost everywhere. -/
theorem real_heightGap_nonnegative_ae (hint : (interior (Δ : Set (EuclideanSpace ℝ (Fin n)))).Nonempty) :
    ∀ᵐ x ∂volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n))),
      0 ≤ G.maxReal - (G.valueAt x).toReal := by
  filter_upwards [G.valueAt_finite_ae, ae_restrict_mem Δ.isCompact.measurableSet] with x hx hxΔ
  have hle : G.valueAt x ≤ (G.maxReal : EReal) := by
    rw [valueAt, dif_pos (show x ∈ Δ from hxΔ), G.coe_maxReal hint]
    exact le_iSup G.value ⟨x, hxΔ⟩
  rw [← EReal.coe_toReal hx.1 hx.2] at hle
  exact sub_nonneg.mpr (EReal.coe_le_coe_iff.mp hle)

/-- Actual layer cake for the genuine original height deficit; bottom boundary values are retained by the proved AE identity. -/
theorem lintegral_heightGap_eq_tail_measure
    (hint : (interior (Δ : Set (EuclideanSpace ℝ (Fin n)))).Nonempty) :
    (∫⁻ x, ((G.maxReal : EReal) - G.valueAt x).toENNReal
      ∂volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n)))) =
      ∫⁻ r in Ioi (0 : ℝ), (volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n))))
        {x | r < G.maxReal - (G.valueAt x).toReal} := by
  rw [lintegral_congr_ae G.heightGap_eq_real_ae]
  exact lintegral_eq_lintegral_meas_lt _ (G.real_heightGap_nonnegative_ae hint)
    (measurable_const.sub G.measurable_valueAt.ereal_toReal).aemeasurable

/-- True original strict sublevels have the exact finite carrier-volume deficit. -/
theorem measure_strict_sublevel_eq (t : ℝ) :
    (volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n))))
      {x | G.valueAt x < (t : EReal)} =
      volume (Δ : Set (EuclideanSpace ℝ (Fin n))) - volume (G.superlevel t) := by
  have hmeas : MeasurableSet {x | G.valueAt x < (t : EReal)} :=
    measurableSet_Iio.preimage G.measurable_valueAt
  rw [Measure.restrict_apply hmeas]
  have heq : {x | G.valueAt x < (t : EReal)} ∩ (Δ : Set (EuclideanSpace ℝ (Fin n))) =
      (Δ : Set (EuclideanSpace ℝ (Fin n))) \ G.superlevel t := by
    ext x
    constructor
    · rintro ⟨ht, hx⟩
      change G.valueAt x < (t : EReal) at ht
      refine ⟨hx, ?_⟩
      rintro ⟨hx', hge⟩
      have ht' : G.value ⟨x, hx⟩ < (t : EReal) := by
        simpa only [valueAt, dif_pos (show x ∈ Δ from hx)] using ht
      exact not_le_of_gt ht' hge
    · rintro ⟨hx, hnot⟩
      refine ⟨?_, hx⟩
      change G.valueAt x < (t : EReal)
      rw [valueAt, dif_pos (show x ∈ Δ from hx)]
      exact lt_of_not_ge (fun hge ↦ hnot ⟨hx, hge⟩)
  rw [heq]
  exact measure_sdiff (G.superlevel_subset t)
    (G.superlevel_isClosed t).measurableSet.nullMeasurableSet
    (G.superlevel_isCompact t).measure_lt_top.ne

/-- Actual height reflection preserves Lebesgue measure and turns the true layer-cake tails into original strict sublevels. -/
theorem lintegral_heightGap_eq_sublevel_measure
    (hint : (interior (Δ : Set (EuclideanSpace ℝ (Fin n)))).Nonempty) :
    (∫⁻ x, ((G.maxReal : EReal) - G.valueAt x).toENNReal
      ∂volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n)))) =
      ∫⁻ t in Iio G.maxReal, (volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n))))
        {x | G.valueAt x < (t : EReal)} := by
  let F : ℝ → ENNReal := fun t ↦
    (volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n)))) {x | G.valueAt x < (t : EReal)}
  have hF : Measurable F := by
    apply Monotone.measurable
    intro s t hst
    exact measure_mono (fun x hx ↦ hx.trans_le (EReal.coe_le_coe hst))
  have hpre : (fun r : ℝ ↦ G.maxReal - r) ⁻¹' Iio G.maxReal = Ioi (0 : ℝ) := by
    ext r
    change G.maxReal - r < G.maxReal ↔ 0 < r
    constructor <;> intro hr <;> linarith
  rw [G.lintegral_heightGap_eq_tail_measure hint]
  calc
    _ = ∫⁻ r in Ioi (0 : ℝ), F (G.maxReal - r) := by
      apply lintegral_congr
      intro r
      apply measure_congr
      filter_upwards [G.valueAt_finite_ae] with x hx
      apply propext
      change r < G.maxReal - (G.valueAt x).toReal ↔ G.valueAt x < (G.maxReal - r : ℝ)
      rw [← EReal.coe_toReal hx.1 hx.2]
      simp only [EReal.toReal_coe, EReal.coe_lt_coe_iff]
      constructor <;> intro h <;> linarith
    _ = _ := by
      rw [← hpre]
      exact (volume.measurePreserving_sub_left G.maxReal).setLIntegral_comp_preimage
        measurableSet_Iio hF

/-- The genuine original curve-volume deficit integral equals the actual nonnegative function-height integral. -/
theorem lintegral_heightGap_eq_volume_deficit
    (hΔ : 0 < volume (Δ : Set (EuclideanSpace ℝ (Fin n)))) :
    (∫⁻ x, ((G.maxReal : EReal) - G.valueAt x).toENNReal
      ∂volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n)))) =
      ∫⁻ t in Iio (G.inverseLegendre hΔ).max,
        ENNReal.ofReal (volume.real (Δ : Set (EuclideanSpace ℝ (Fin n))) -
          volume.real ((G.inverseLegendre hΔ).bodyAt t : Set (EuclideanSpace ℝ (Fin n)))) := by
  rw [G.lintegral_heightGap_eq_sublevel_measure
    (SGPT.AlmostSemigroup.ConvexIntersection.interior_nonempty_of_measure_pos volume Δ.convex hΔ)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Iio] with t ht
  change t < G.maxReal at ht
  rw [G.measure_strict_sublevel_eq t]
  have hbody : ((G.inverseLegendre hΔ).bodyAt t : Set (EuclideanSpace ℝ (Fin n))) =
      G.superlevel t := by
    rw [TestCurve.bodyAt, dif_pos (show t < (G.inverseLegendre hΔ).max from ht)]
    rfl
  rw [hbody]
  change volume (Δ : Set (EuclideanSpace ℝ (Fin n))) - volume (G.superlevel t) =
    ENNReal.ofReal ((volume (Δ : Set (EuclideanSpace ℝ (Fin n)))).toReal -
      (volume (G.superlevel t)).toReal)
  rw [← ENNReal.toReal_sub_of_le (measure_mono (G.superlevel_subset t))
      Δ.isCompact.measure_lt_top.ne,
    ENNReal.ofReal_toReal (lt_of_le_of_lt tsub_le_self Δ.isCompact.measure_lt_top).ne]

end TestFunction

namespace TestCurve

variable {n : ℕ} {Δ : ConvexBody (EuclideanSpace ℝ (Fin n))} (K : SGPT.Okounkov.TestCurve Δ)

/-- Original finite curve energy has exactly its true finite volume-deficit integral criterion. -/
theorem hasFiniteEnergy_iff_deficit_lt_top :
    K.HasFiniteEnergy ↔
      (∫⁻ t in Iio K.max,
        ENNReal.ofReal (volume.real (Δ : Set (EuclideanSpace ℝ (Fin n))) -
          volume.real (K.bodyAt t : Set (EuclideanSpace ℝ (Fin n))))) < ⊤ := by
  unfold HasFiniteEnergy
  rw [K.energy_eq_deficit]
  let D : ENNReal := ∫⁻ t in Iio K.max,
    ENNReal.ofReal (volume.real (Δ : Set (EuclideanSpace ℝ (Fin n))) -
      volume.real (K.bodyAt t : Set (EuclideanSpace ℝ (Fin n))))
  change (⊥ : EReal) <
    (((n.factorial : ℝ) * K.max * volume.real (Δ : Set (EuclideanSpace ℝ (Fin n))) : ℝ) : EReal) -
      ((n.factorial : ℝ) : EReal) * (D : EReal) ↔ D < ⊤
  by_cases hD : D = ⊤
  · rw [hD, EReal.coe_ennreal_top,
      EReal.mul_top_of_pos (show (0 : EReal) < ((n.factorial : ℝ) : EReal) by
        exact_mod_cast Nat.factorial_pos n)]
    simp
  · rw [← EReal.coe_ennreal_toReal hD, ← EReal.coe_mul, ← EReal.coe_sub]
    simp only [EReal.bot_lt_coe, lt_top_iff_ne_top]
    exact iff_of_true trivial hD

end TestCurve

namespace TestFunction

variable {n : ℕ} {Δ : ConvexBody (EuclideanSpace ℝ (Fin n))} (G : TestFunction Δ)

/-- Genuine original inverse levels preserve exactly the source finite-energy class, through actual layer cake rather than an energy certificate. -/
theorem inverseLegendre_hasFiniteEnergy_iff
    (hΔ : 0 < volume (Δ : Set (EuclideanSpace ℝ (Fin n)))) :
    (G.inverseLegendre hΔ).HasFiniteEnergy ↔ G.HasFiniteEnergy := by
  rw [TestCurve.hasFiniteEnergy_iff_deficit_lt_top, G.hasFiniteEnergy_iff_negative_part_lt_top,
    ← G.lintegral_heightGap_eq_volume_deficit hΔ]
  let : IsFiniteMeasure (volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n)))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using Δ.isCompact.measure_lt_top⟩
  exact lintegral_heightGap_lt_top_iff _ G.valueAt G.maxReal

end TestFunction

namespace TestCurve

variable {n : ℕ} {Δ : ConvexBody (EuclideanSpace ℝ (Fin n))} (K : SGPT.Okounkov.TestCurve Δ)

/-- Exact original finite-energy correspondence under the actual proved source bijection. -/
theorem hasFiniteEnergy_iff_toTestFunction_hasFiniteEnergy
    (hΔ : 0 < volume (Δ : Set (EuclideanSpace ℝ (Fin n)))) :
    K.HasFiniteEnergy ↔ K.toTestFunction.HasFiniteEnergy := by
  have hK : K.toTestFunction.inverseLegendre hΔ = K :=
    K.inverse_forward
      (SGPT.AlmostSemigroup.ConvexIntersection.interior_nonempty_of_measure_pos volume Δ.convex hΔ)
  simpa only [hK] using K.toTestFunction.inverseLegendre_hasFiniteEnergy_iff hΔ

end TestCurve
end SGPT.Okounkov
