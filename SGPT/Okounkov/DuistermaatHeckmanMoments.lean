import SGPT.Okounkov.DuistermaatHeckman
import SGPT.Okounkov.LegendreEnergyEquality
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Layercake

noncomputable section

namespace SGPT.Okounkov

open Set Filter MeasureTheory
open scoped Topology

/-- Actual polynomial tail formula from genuine weighted layer cake, retaining infinite moment values. -/
theorem lintegral_pow_eq_weighted_tail {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (f : A → ℝ) (hf : AEMeasurable f μ) (hpos : 0 ≤ᵐ[μ] f) (q : ℕ) :
    (∫⁻ x, ENNReal.ofReal ((f x) ^ (q + 1)) ∂μ) =
      ∫⁻ t in Ioi (0 : ℝ), μ {x | t < f x} * ENNReal.ofReal ((q + 1 : ℝ) * t ^ q) := by
  have hdens : Continuous (fun t : ℝ ↦ (q + 1 : ℝ) * t ^ q) :=
    continuous_const.mul (continuous_id.pow q)
  have hnn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ (q + 1 : ℝ) * t ^ q := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
    exact mul_nonneg (by positivity) (pow_nonneg ht.le q)
  have hi (x : A) : (∫ t in (0 : ℝ)..f x, (q + 1 : ℝ) * t ^ q) = (f x) ^ (q + 1) := by
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero q), sub_zero]
    field_simp
  have h := lintegral_comp_eq_lintegral_meas_lt_mul μ hpos hf
    (fun t _ht ↦ hdens.intervalIntegrable 0 t) hnn
  simpa only [hi] using h

/-- The shared genuine height-reflection weighted layer cake for an actual
nonnegative continuous density. No finite tail integral is assumed. -/
theorem lintegral_interval_eq_weighted_sublevel {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (g : A → ℝ) (hg : Measurable g) (a : ℝ)
    (hle : g ≤ᵐ[μ] fun _ ↦ a) (d : ℝ → ℝ) (hd : Continuous d)
    (hnd : ∀ t, 0 ≤ d t) :
    (∫⁻ x, ENNReal.ofReal (∫ t in g x..a, d t) ∂μ) =
      ∫⁻ t in Iio a, μ {x | g x < t} * ENNReal.ofReal (d t) := by
  have hdc : Continuous (fun r ↦ d (a - r)) := hd.comp (continuous_const.sub continuous_id)
  have hi (x : A) : (∫ r in (0 : ℝ)..a - g x, d (a - r)) = ∫ t in g x..a, d t := by
    rw [intervalIntegral.integral_comp_sub_left]
    simp only [sub_zero, sub_sub_cancel]
  have hgap : 0 ≤ᵐ[μ] fun x ↦ a - g x := hle.mono (fun _ hx ↦ sub_nonneg.mpr hx)
  have h := lintegral_comp_eq_lintegral_meas_lt_mul μ hgap
    (measurable_const.sub hg).aemeasurable (fun r _ ↦ hdc.intervalIntegrable 0 r)
    (Eventually.of_forall (fun r ↦ hnd (a - r)))
  simp only [hi] at h
  rw [h]
  let F : ℝ → ENNReal := fun t ↦ μ {x | g x < t} * ENNReal.ofReal (d t)
  have hm : Measurable (fun t : ℝ ↦ μ {x | g x < t}) := by
    apply Monotone.measurable
    intro s t hst
    exact measure_mono (fun _ hx ↦ hx.trans_le hst)
  have hF : Measurable F := hm.mul hd.measurable.ennreal_ofReal
  have hpre : (fun r : ℝ ↦ a - r) ⁻¹' Iio a = Ioi (0 : ℝ) := by
    ext r
    change a - r < a ↔ 0 < r
    constructor <;> intro hr <;> linarith
  calc
    _ = ∫⁻ r in Ioi (0 : ℝ), F (a - r) := by
      apply lintegral_congr
      intro r
      congr 1
      congr 1
      ext x
      change r < a - g x ↔ g x < a - r
      constructor <;> intro hr <;> linarith
    _ = _ := by
      rw [← hpre]
      exact (volume.measurePreserving_sub_left a).setLIntegral_comp_preimage measurableSet_Iio hF

/-- Genuine shifted weighted layer cake for every odd polynomial, with no finite moment premise. -/
theorem lintegral_odd_pow_gap_eq_weighted_sublevel {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (g : A → ℝ) (hg : Measurable g) (a : ℝ)
    (hle : g ≤ᵐ[μ] fun _ ↦ a) (q : ℕ) (hq : Even q) :
    (∫⁻ x, ENNReal.ofReal (a ^ (q + 1) - (g x) ^ (q + 1)) ∂μ) =
      ∫⁻ t in Iio a, μ {x | g x < t} * ENNReal.ofReal ((q + 1 : ℝ) * t ^ q) := by
  have hi (x : A) : (∫ t in g x..a, (q + 1 : ℝ) * t ^ q) = a ^ (q + 1) - g x ^ (q + 1) := by
    rw [intervalIntegral.integral_const_mul, integral_pow]
    field_simp
  simpa only [hi] using lintegral_interval_eq_weighted_sublevel μ g hg a hle
    (fun t ↦ (q + 1 : ℝ) * t ^ q) (continuous_const.mul (continuous_id.pow q))
    (fun t ↦ mul_nonneg (by positivity) (hq.pow_nonneg t))

/-- Actual integration of clipped polynomial density, proved by splitting the
original interval at zero. -/
theorem integral_clipped_pow_density {g a : ℝ} (hga : g ≤ a) (q : ℕ) (hq : 0 < q) :
    (∫ t in g..a, (q + 1 : ℝ) * (Max.max t 0) ^ q) =
      (Max.max a 0) ^ (q + 1) - (Max.max g 0) ^ (q + 1) := by
  let d : ℝ → ℝ := fun t ↦ (q + 1 : ℝ) * (Max.max t 0) ^ q
  have hd : Continuous d := continuous_const.mul ((continuous_id.max continuous_const).pow q)
  have hlow {x y : ℝ} (hxy : x ≤ y) (hy : y ≤ 0) : (∫ t in x..y, d t) = 0 := by
    calc
      _ = ∫ t in x..y, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hxy] at ht
        dsimp only [d]
        rw [max_eq_right (ht.2.trans hy), zero_pow hq.ne', mul_zero]
      _ = 0 := by simp
  have hhigh {x y : ℝ} (hxy : x ≤ y) (hx : 0 ≤ x) :
      (∫ t in x..y, d t) = y ^ (q + 1) - x ^ (q + 1) := by
    calc
      _ = ∫ t in x..y, (q + 1 : ℝ) * t ^ q := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hxy] at ht
        dsimp only [d]
        rw [max_eq_left (hx.trans ht.1)]
      _ = _ := by rw [intervalIntegral.integral_const_mul, integral_pow]; field_simp
  change (∫ t in g..a, d t) = _
  by_cases ha : a ≤ 0
  · rw [hlow hga ha, max_eq_right ha, max_eq_right (hga.trans ha), sub_self]
  · have ha0 : 0 ≤ a := (lt_of_not_ge ha).le
    rw [max_eq_left ha0]
    by_cases hg : 0 ≤ g
    · rw [max_eq_left hg, hhigh hga hg]
    · have hg0 : g ≤ 0 := (lt_of_not_ge hg).le
      rw [max_eq_right hg0, zero_pow (Nat.succ_ne_zero q), sub_zero]
      calc
        _ = (∫ t in g..0, d t) + ∫ t in (0 : ℝ)..a, d t :=
          (intervalIntegral.integral_add_adjacent_intervals (hd.intervalIntegrable g 0)
            (hd.intervalIntegrable 0 a)).symm
        _ = a ^ (q + 1) := by rw [hlow hg0 le_rfl, hhigh ha0 le_rfl]; simp

/-- Actual even powers split into the genuine clipped positive and negative powers. -/
theorem even_pow_eq_clipped_sum (p : ℕ) (hp : Even p) (hp0 : p ≠ 0) (z : ℝ) :
    z ^ p = (Max.max z 0) ^ p + (Max.max (-z) 0) ^ p := by
  by_cases hz : 0 ≤ z
  · rw [max_eq_left hz, max_eq_right (neg_nonpos.mpr hz), zero_pow hp0, add_zero]
  · have hz0 : z ≤ 0 := (lt_of_not_ge hz).le
    rw [max_eq_right hz0, max_eq_left (neg_nonneg.mpr hz0), zero_pow hp0, zero_add, hp.neg_pow]

/-- Actual polynomial gap algebra integrated without subtracting two infinite
nonnegative moments. -/
theorem lintegral_even_pow_add_clipped_gap {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (g : A → ℝ) (hg : Measurable g) (a : ℝ)
    (hle : g ≤ᵐ[μ] fun _ ↦ a) (q : ℕ) (hq : Odd q) :
    (∫⁻ x, ENNReal.ofReal (g x ^ (q + 1)) ∂μ) +
      (∫⁻ x, ENNReal.ofReal ((Max.max a 0) ^ (q + 1) - (Max.max (g x) 0) ^ (q + 1)) ∂μ) =
    ENNReal.ofReal (a ^ (q + 1)) * μ univ +
      (∫⁻ x, ENNReal.ofReal ((Max.max (-g x) 0) ^ (q + 1) - (Max.max (-a) 0) ^ (q + 1)) ∂μ) := by
  have hp : Even (q + 1) := hq.add_odd odd_one
  rw [← lintegral_add_left (hg.pow_const (q + 1)).ennreal_ofReal,
    ← lintegral_const, ← lintegral_add_left measurable_const]
  apply lintegral_congr_ae
  filter_upwards [hle] with x hx
  have hP : 0 ≤ (Max.max a 0) ^ (q + 1) - (Max.max (g x) 0) ^ (q + 1) := by
    apply sub_nonneg.mpr
    gcongr
  have hN : 0 ≤ (Max.max (-g x) 0) ^ (q + 1) - (Max.max (-a) 0) ^ (q + 1) := by
    apply sub_nonneg.mpr
    gcongr
  rw [← ENNReal.ofReal_add (hp.pow_nonneg _) hP, ← ENNReal.ofReal_add (hp.pow_nonneg _) hN]
  congr 1
  rw [even_pow_eq_clipped_sum _ hp (Nat.succ_ne_zero q) (g x),
    even_pow_eq_clipped_sum _ hp (Nat.succ_ne_zero q) a]
  ring

/-- The positive clipped polynomial gap is genuinely finite on finite measure,
so the even-moment rearrangement never subtracts two infinities. -/
theorem lintegral_positive_clipped_gap_lt_top {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsFiniteMeasure μ] (g : A → ℝ) (a : ℝ) (p : ℕ) :
    (∫⁻ x, ENNReal.ofReal ((Max.max a 0) ^ p - (Max.max (g x) 0) ^ p) ∂μ) < ⊤ := by
  have hb (x : A) : ENNReal.ofReal ((Max.max a 0) ^ p - (Max.max (g x) 0) ^ p) ≤
      ENNReal.ofReal ((Max.max a 0) ^ p) := by
    apply ENNReal.ofReal_le_ofReal
    exact sub_le_self _ (pow_nonneg (le_max_right _ _) _)
  apply lt_of_le_of_lt (lintegral_mono hb)
  rw [lintegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ univ)

/-- Actual positive clipped polynomial gaps have the genuine original
strict-sublevel weighted tails. -/
theorem lintegral_positive_clipped_gap_eq_weighted_sublevel {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (g : A → ℝ) (hg : Measurable g) (a : ℝ)
    (hle : g ≤ᵐ[μ] fun _ ↦ a) (q : ℕ) (hq : 0 < q) :
    (∫⁻ x, ENNReal.ofReal ((Max.max a 0) ^ (q + 1) - (Max.max (g x) 0) ^ (q + 1)) ∂μ) =
      ∫⁻ t in Iio a, μ {x | g x < t} * ENNReal.ofReal ((q + 1 : ℝ) * (Max.max t 0) ^ q) := by
  calc
    _ = ∫⁻ x, ENNReal.ofReal (∫ t in g x..a, (q + 1 : ℝ) * (Max.max t 0) ^ q) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hle] with x hx
      rw [integral_clipped_pow_density hx q hq]
    _ = _ := lintegral_interval_eq_weighted_sublevel μ g hg a hle _
      (continuous_const.mul ((continuous_id.max continuous_const).pow q))
      (fun t ↦ mul_nonneg (by positivity) (pow_nonneg (le_max_right t 0) q))

/-- Actual negative clipped polynomial gaps have genuine reflected tails;
their integral may remain infinite. -/
theorem lintegral_negative_clipped_gap_eq_weighted_sublevel {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (g : A → ℝ) (hg : Measurable g) (a : ℝ)
    (hle : g ≤ᵐ[μ] fun _ ↦ a) (q : ℕ) (hq : 0 < q) :
    (∫⁻ x, ENNReal.ofReal ((Max.max (-g x) 0) ^ (q + 1) - (Max.max (-a) 0) ^ (q + 1)) ∂μ) =
      ∫⁻ t in Iio a, μ {x | g x < t} * ENNReal.ofReal ((q + 1 : ℝ) * (Max.max (-t) 0) ^ q) := by
  calc
    _ = ∫⁻ x, ENNReal.ofReal (∫ t in g x..a, (q + 1 : ℝ) * (Max.max (-t) 0) ^ q) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hle] with x hx
      rw [intervalIntegral.integral_comp_neg (fun t : ℝ ↦ (q + 1 : ℝ) * (Max.max t 0) ^ q),
        integral_clipped_pow_density (neg_le_neg hx) q hq]
    _ = _ := lintegral_interval_eq_weighted_sublevel μ g hg a hle _
      (continuous_const.mul ((continuous_id.neg.max continuous_const).pow q))
      (fun t ↦ mul_nonneg (by positivity) (pow_nonneg (le_max_right (-t) 0) q))

/-- Actual finite measure and a genuine upper bound identify the unchanged signed
integral with its nonnegative height gap, including divergent negative values. -/
theorem signedIntegral_eq_bound_sub_gap {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsFiniteMeasure μ] (g : A → ℝ) (hg : Measurable g) (a : ℝ)
    (hle : g ≤ᵐ[μ] fun _ ↦ a) :
    SGPT.Convex.extendedSignedIntegral μ (fun x ↦ (g x : EReal)) =
      ((a * μ.real univ : ℝ) : EReal) - ((∫⁻ x, ENNReal.ofReal (a - g x) ∂μ) : EReal) := by
  have hgE : Measurable (fun x ↦ (g x : EReal)) := continuous_coe_real_ereal.measurable.comp hg
  have hfin : ∀ᵐ x ∂μ, (g x : EReal) ≠ ⊤ ∧ (g x : EReal) ≠ ⊥ :=
    Eventually.of_forall (fun x ↦ ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩)
  have hp : (∫⁻ x, (g x : EReal).toENNReal ∂μ) < ⊤ := by
    have hb : (fun x ↦ (g x : EReal).toENNReal) ≤ᵐ[μ]
        fun _ ↦ (a : EReal).toENNReal :=
      hle.mono (fun _ hx ↦ EReal.toENNReal_le_toENNReal (EReal.coe_le_coe hx))
    apply lt_of_le_of_lt (lintegral_mono_ae hb)
    rw [lintegral_const]
    exact ENNReal.mul_lt_top (by simp) (measure_lt_top μ univ)
  have hgap : (∫⁻ x, (((a : EReal) - (g x : EReal)).toENNReal) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (a - g x) ∂μ := by
    simp only [← EReal.coe_sub, EReal.real_coe_toENNReal]
  by_cases hn : (∫⁻ x, (-(g x : EReal)).toENNReal ∂μ) < ⊤
  · have hint := integrable_toReal_of_finite_parts μ _ hgE hfin hp hn
    simp only [EReal.toReal_coe] at hint
    have hgapi : Integrable (fun x ↦ a - g x) μ := (integrable_const a).sub hint
    have hgapnn : 0 ≤ᵐ[μ] fun x ↦ a - g x := hle.mono (fun _ hx ↦ sub_nonneg.mpr hx)
    have hgn : 0 ≤ a * μ.real univ - ∫ x, g x ∂μ := by
      have h := integral_nonneg_of_ae hgapnn
      rw [integral_sub (integrable_const a) hint, integral_const, smul_eq_mul] at h
      simpa only [mul_comm] using h
    rw [signedIntegral_eq_coe_integral_of_finite_parts μ _ hgE hfin hp hn]
    simp only [EReal.toReal_coe]
    rw [← ofReal_integral_eq_lintegral_ofReal hgapi hgapnn,
      integral_sub (integrable_const a) hint, integral_const, smul_eq_mul, mul_comm (μ.real univ) a,
      EReal.coe_ennreal_ofReal, max_eq_left hgn, ← EReal.coe_sub]
    congr 1
    ring
  · have hnegTop : (∫⁻ x, (-(g x : EReal)).toENNReal ∂μ) = ⊤ :=
      top_unique (not_lt.mp hn)
    have hgapTop : (∫⁻ x, ENNReal.ofReal (a - g x) ∂μ) = ⊤ := by
      apply top_unique
      apply not_lt.mp
      rw [← hgap, lintegral_heightGap_lt_top_iff]
      exact hn
    rw [SGPT.Convex.extendedSignedIntegral, hnegTop, hgapTop,
      ← EReal.coe_ennreal_toReal hp.ne]
    simp

/-- The true signed polynomial density separates into its actual positive and
negative clipped parts when its degree is odd. -/
theorem odd_pow_negative_density_parts (q : ℕ) (hq : Odd q) (t d : ℝ) (hd : 0 ≤ d) :
    ((t ^ q * -d : ℝ) : EReal).toENNReal = ENNReal.ofReal ((Max.max (-t) 0) ^ q * d) ∧
      (-((t ^ q * -d : ℝ) : EReal)).toENNReal = ENNReal.ofReal ((Max.max t 0) ^ q * d) := by
  simp only [← EReal.coe_neg, EReal.real_coe_toENNReal]
  by_cases ht : 0 ≤ t
  · rw [max_eq_right (neg_nonpos.mpr ht), max_eq_left ht, zero_pow hq.pos.ne', zero_mul]
    constructor
    · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ht q) (neg_nonpos.mpr hd))]
      simp
    · congr 1
      ring
  · have ht0 : t ≤ 0 := (lt_of_not_ge ht).le
    rw [max_eq_left (neg_nonneg.mpr ht0), max_eq_right ht0, zero_pow hq.pos.ne', zero_mul]
    constructor
    · rw [hq.neg_pow]
      congr 1
      ring
    · rw [ENNReal.ofReal_of_nonpos (neg_nonpos.mpr
        (mul_nonneg_of_nonpos_of_nonpos (hq.pow_nonpos_iff.mpr ht0) (neg_nonpos.mpr hd)))]
      simp

namespace TestCurve

variable {n : ℕ} {Δ : ConvexBody (EuclideanSpace ℝ (Fin n))} (K : SGPT.Okounkov.TestCurve Δ)

/-- Actual original negative polynomial moments have genuine strict-sublevel tails; no finite moment is assumed. -/
theorem lintegral_negative_part_pow_eq_tail (q : ℕ) :
    (∫⁻ x, ENNReal.ofReal ((Max.max (-K.realLegendre x) 0) ^ (q + 1))
      ∂volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n)))) =
      ∫⁻ t in Ioi (0 : ℝ),
        (volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n)))) {x | K.realLegendre x < -t} *
          ENNReal.ofReal ((q + 1 : ℝ) * t ^ q) := by
  rw [lintegral_pow_eq_weighted_tail _ (fun x ↦ Max.max (-K.realLegendre x) 0)
    (K.measurable_realLegendre.neg.max measurable_const).aemeasurable
    (Eventually.of_forall (fun _ ↦ le_max_right _ _)) q]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  congr 1
  congr 1
  ext x
  change t < Max.max (-K.realLegendre x) 0 ↔ K.realLegendre x < -t
  rw [lt_max_iff]
  constructor
  · rintro (h | h) <;> linarith
  · intro h
    left
    linarith

/-- Actual original positive polynomial moments have genuine upper tails, with their original infinite values retained. -/
theorem lintegral_positive_part_pow_eq_tail (q : ℕ) :
    (∫⁻ x, ENNReal.ofReal ((Max.max (K.realLegendre x) 0) ^ (q + 1))
      ∂volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n)))) =
      ∫⁻ t in Ioi (0 : ℝ),
        (volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n)))) {x | t < K.realLegendre x} *
          ENNReal.ofReal ((q + 1 : ℝ) * t ^ q) := by
  rw [lintegral_pow_eq_weighted_tail _ (fun x ↦ Max.max (K.realLegendre x) 0)
    (K.measurable_realLegendre.max measurable_const).aemeasurable
    (Eventually.of_forall (fun _ ↦ le_max_right _ _)) q]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  congr 1
  congr 1
  ext x
  change t < Max.max (K.realLegendre x) 0 ↔ t < K.realLegendre x
  rw [lt_max_iff]
  constructor
  · rintro (h | h)
    · exact h
    · linarith
  · exact Or.inl

/-- Actual source polynomial moments are the genuine original-transform pushforward signed integrals. -/
theorem signed_polynomial_moment_pushforward (p : ℕ) :
    SGPT.Convex.extendedSignedIntegral K.duistermaatHeckman (fun t : ℝ ↦ (t : EReal) ^ p) =
      SGPT.Convex.extendedSignedIntegral
        (volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n))))
        (fun x ↦ (K.realLegendre x : EReal) ^ p) := by
  have hf : Measurable (fun t : ℝ ↦ ((t : EReal) ^ p).toENNReal) :=
    (continuous_coe_real_ereal.measurable.pow_const p).ereal_toENNReal
  have hn : Measurable (fun t : ℝ ↦ (-((t : EReal) ^ p)).toENNReal) :=
    (continuous_coe_real_ereal.measurable.pow_const p).neg.ereal_toENNReal
  rw [SGPT.Convex.extendedSignedIntegral, SGPT.Convex.extendedSignedIntegral,
    duistermaatHeckman, lintegral_map hf K.measurable_realLegendre,
    lintegral_map hn K.measurable_realLegendre]

/-- The actual moment pushforward retains the original extended transform almost everywhere. -/
theorem signed_polynomial_moment_eq_original (p : ℕ) :
    SGPT.Convex.extendedSignedIntegral K.duistermaatHeckman (fun t : ℝ ↦ (t : EReal) ^ p) =
      SGPT.Convex.extendedSignedIntegral
        (volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n))))
        (fun x ↦ (K.toTestFunction.valueAt x) ^ p) := by
  rw [K.signed_polynomial_moment_pushforward p]
  unfold SGPT.Convex.extendedSignedIntegral
  congr 1
  · congr 1
    apply lintegral_congr_ae
    filter_upwards [K.coe_realLegendre_ae] with x hx
    rw [hx]
  · congr 1
    apply lintegral_congr_ae
    filter_upwards [K.coe_realLegendre_ae] with x hx
    rw [hx]

/-- The true source cutoff bounds its genuine real representative almost everywhere. -/
theorem realLegendre_le_max_ae :
    ∀ᵐ x ∂volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n))), K.realLegendre x ≤ K.max := by
  filter_upwards [K.coe_realLegendre_ae, ae_restrict_mem Δ.isCompact.measurableSet] with x hx hxΔ
  have hval : K.toTestFunction.valueAt x = K.transform ⟨x, hxΔ⟩ := by
    classical
    rw [TestFunction.valueAt, dif_pos (show x ∈ Δ from hxΔ)]
    rfl
  have hle := K.transform_le_max ⟨x, hxΔ⟩
  rw [← hval, ← hx] at hle
  exact EReal.coe_le_coe_iff.mp hle

/-- The actual finite source cutoff and original finite volume bound all true positive polynomial parts. -/
theorem lintegral_positive_part_pow_lt_top (p : ℕ) :
    (∫⁻ x, ENNReal.ofReal ((Max.max (K.realLegendre x) 0) ^ p)
      ∂volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n)))) < ⊤ := by
  have hbound : ∀ᵐ x ∂volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n))),
      ENNReal.ofReal ((Max.max (K.realLegendre x) 0) ^ p) ≤
        ENNReal.ofReal ((Max.max K.max 0) ^ p) := by
    filter_upwards [K.realLegendre_le_max_ae] with x hx
    gcongr
  apply lt_of_le_of_lt (lintegral_mono_ae hbound)
  rw [lintegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by
    rw [Measure.restrict_apply_univ]
    exact Δ.isCompact.measure_lt_top)

/-- Actual finite-AE original values and exact source superlevels give the true
sub-cutoff real strict-sublevel volume deficit. -/
theorem measure_realLegendre_strict_sublevel_eq_deficit {t : ℝ} (ht : t < K.max) :
    (volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n)))) {x | K.realLegendre x < t} =
      ENNReal.ofReal (volume.real (Δ : Set (EuclideanSpace ℝ (Fin n))) -
        volume.real (K.bodyAt t : Set (EuclideanSpace ℝ (Fin n)))) := by
  have hm : (volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n)))) {x | K.realLegendre x < t} =
      (volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n))))
        {x | K.toTestFunction.valueAt x < (t : EReal)} := by
    apply measure_congr
    filter_upwards [K.coe_realLegendre_ae] with x hx
    apply propext
    change K.realLegendre x < t ↔ K.toTestFunction.valueAt x < (t : EReal)
    rw [← hx, EReal.coe_lt_coe_iff]
  have hb : K.toTestFunction.superlevel t = (K.bodyAt t : Set (EuclideanSpace ℝ (Fin n))) := by
    rw [bodyAt, dif_pos ht]
    ext x
    constructor
    · rintro ⟨hxΔ, hxt⟩
      exact (K.mem_body_iff_le_transform ⟨x, hxΔ⟩ ⟨t, ht⟩).mpr hxt
    · intro hx
      have hxΔ : x ∈ Δ := K.body_subset ⟨t, ht⟩ hx
      exact ⟨hxΔ, (K.mem_body_iff_le_transform ⟨x, hxΔ⟩ ⟨t, ht⟩).mp hx⟩
  rw [hm, K.toTestFunction.measure_strict_sublevel_eq, hb]
  change volume (Δ : Set (EuclideanSpace ℝ (Fin n))) - volume (K.bodyAt t : Set (EuclideanSpace ℝ (Fin n))) =
    ENNReal.ofReal ((volume (Δ : Set (EuclideanSpace ℝ (Fin n)))).toReal -
      (volume (K.bodyAt t : Set (EuclideanSpace ℝ (Fin n)))).toReal)
  rw [← ENNReal.toReal_sub_of_le (measure_mono (K.bodyAt_subset t)) Δ.isCompact.measure_lt_top.ne,
    ENNReal.ofReal_toReal (lt_of_le_of_lt tsub_le_self Δ.isCompact.measure_lt_top).ne]

/-- Actual weighted source sublevels give their true source volume deficits,
with a finite nonnegative weight factored outside the genuine integral. -/
theorem lintegral_weighted_sublevel_eq_const_mul_deficit (c : ℝ) (hc : 0 ≤ c) (d : ℝ → ℝ) :
    (∫⁻ t in Iio K.max,
      (volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n)))) {x | K.realLegendre x < t} *
        ENNReal.ofReal (c * d t)) =
      ENNReal.ofReal c * ∫⁻ t in Iio K.max,
        ENNReal.ofReal (d t * (volume.real (Δ : Set (EuclideanSpace ℝ (Fin n))) -
          volume.real (K.bodyAt t : Set (EuclideanSpace ℝ (Fin n))))) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Iio] with t ht
  rw [K.measure_realLegendre_strict_sublevel_eq_deficit ht, ENNReal.ofReal_mul hc,
    ENNReal.ofReal_mul' (sub_nonneg.mpr (K.volume_bodyAt_le t))]
  ring

/-- The literal original extended moment formula for every positive odd integer,
including its original divergent negative branch. -/
theorem odd_polynomial_moment_eq (q : ℕ) (hq : Even q) :
    SGPT.Convex.extendedSignedIntegral K.duistermaatHeckman (fun t : ℝ ↦ (t : EReal) ^ (q + 1)) =
      ((K.max ^ (q + 1) * volume.real (Δ : Set (EuclideanSpace ℝ (Fin n))) : ℝ) : EReal) +
        (q + 1 : EReal) * SGPT.Convex.extendedSignedIntegral (volume.restrict (Iio K.max))
          (fun t : ℝ ↦ ((t ^ q * (volume.real (K.bodyAt t : Set (EuclideanSpace ℝ (Fin n))) -
            volume.real (Δ : Set (EuclideanSpace ℝ (Fin n)))) : ℝ) : EReal)) := by
  let μ := volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n)))
  let : IsFiniteMeasure μ := ⟨by
    dsimp only [μ]
    rw [Measure.restrict_apply_univ]
    exact Δ.isCompact.measure_lt_top⟩
  let D : ℝ → ℝ := fun t ↦ volume.real (Δ : Set (EuclideanSpace ℝ (Fin n))) -
    volume.real (K.bodyAt t : Set (EuclideanSpace ℝ (Fin n)))
  have hD (t : ℝ) : 0 ≤ D t := sub_nonneg.mpr (K.volume_bodyAt_le t)
  have hp : Odd (q + 1) := hq.add_odd odd_one
  have hle : (fun x ↦ K.realLegendre x ^ (q + 1)) ≤ᵐ[μ] fun _ ↦ K.max ^ (q + 1) :=
    K.realLegendre_le_max_ae.mono (fun _ hx ↦ hp.pow_le_pow.mpr hx)
  have hμ : μ.real univ = volume.real (Δ : Set (EuclideanSpace ℝ (Fin n))) := by
    change ((volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n)))) univ).toReal = _
    rw [Measure.restrict_apply_univ]
    rfl
  have hW : (∫⁻ x, ENNReal.ofReal (K.max ^ (q + 1) - K.realLegendre x ^ (q + 1)) ∂μ) =
      ENNReal.ofReal (q + 1 : ℝ) * ∫⁻ t in Iio K.max, ENNReal.ofReal (t ^ q * D t) := by
    rw [lintegral_odd_pow_gap_eq_weighted_sublevel μ _ K.measurable_realLegendre K.max
      K.realLegendre_le_max_ae q hq,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Iio] with t ht
    rw [K.measure_realLegendre_strict_sublevel_eq_deficit ht,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ q + 1),
      ENNReal.ofReal_mul (hq.pow_nonneg t)]
    change ENNReal.ofReal (D t) * (ENNReal.ofReal (q + 1 : ℝ) * ENNReal.ofReal (t ^ q)) = _
    ring
  have hSI : SGPT.Convex.extendedSignedIntegral (volume.restrict (Iio K.max))
      (fun t : ℝ ↦ ((t ^ q * (volume.real (K.bodyAt t : Set (EuclideanSpace ℝ (Fin n))) -
        volume.real (Δ : Set (EuclideanSpace ℝ (Fin n)))) : ℝ) : EReal)) =
      -((∫⁻ t in Iio K.max, ENNReal.ofReal (t ^ q * D t)) : EReal) := by
    unfold SGPT.Convex.extendedSignedIntegral
    have hz (t : ℝ) : ((t ^ q * (volume.real (K.bodyAt t : Set (EuclideanSpace ℝ (Fin n))) -
        volume.real (Δ : Set (EuclideanSpace ℝ (Fin n)))) : ℝ) : EReal).toENNReal = 0 := by
      apply EReal.toENNReal_of_nonpos
      exact_mod_cast mul_nonpos_of_nonneg_of_nonpos (hq.pow_nonneg t)
        (sub_nonpos.mpr (K.volume_bodyAt_le t))
    simp only [hz, lintegral_zero, EReal.coe_ennreal_zero, zero_sub]
    congr 1
    congr 1
    apply lintegral_congr
    intro t
    rw [← EReal.coe_neg, EReal.real_coe_toENNReal]
    congr 1
    dsimp only [D]
    ring
  rw [K.signed_polynomial_moment_pushforward]
  simp only [← EReal.coe_pow]
  rw [signedIntegral_eq_bound_sub_gap μ _ (K.measurable_realLegendre.pow_const (q + 1)) _ hle,
    hμ, hW, EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal,
    max_eq_left (by positivity : (0 : ℝ) ≤ q + 1), hSI, mul_neg]
  rfl

/-- The literal original extended moment formula for every positive even
integer. Its true positive-infinite branch is preserved. -/
theorem even_polynomial_moment_eq (q : ℕ) (hq : Odd q) :
    SGPT.Convex.extendedSignedIntegral K.duistermaatHeckman (fun t : ℝ ↦ (t : EReal) ^ (q + 1)) =
      ((K.max ^ (q + 1) * volume.real (Δ : Set (EuclideanSpace ℝ (Fin n))) : ℝ) : EReal) +
        (q + 1 : EReal) * SGPT.Convex.extendedSignedIntegral (volume.restrict (Iio K.max))
          (fun t : ℝ ↦ ((t ^ q * (volume.real (K.bodyAt t : Set (EuclideanSpace ℝ (Fin n))) -
            volume.real (Δ : Set (EuclideanSpace ℝ (Fin n)))) : ℝ) : EReal)) := by
  let μ := volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n)))
  let : IsFiniteMeasure μ := ⟨by
    dsimp only [μ]
    rw [Measure.restrict_apply_univ]
    exact Δ.isCompact.measure_lt_top⟩
  let D : ℝ → ℝ := fun t ↦ volume.real (Δ : Set (EuclideanSpace ℝ (Fin n))) -
    volume.real (K.bodyAt t : Set (EuclideanSpace ℝ (Fin n)))
  let P : ENNReal := ∫⁻ t in Iio K.max, ENNReal.ofReal ((Max.max t 0) ^ q * D t)
  let N : ENNReal := ∫⁻ t in Iio K.max, ENNReal.ofReal ((Max.max (-t) 0) ^ q * D t)
  let c : ENNReal := ENNReal.ofReal (q + 1 : ℝ)
  have hD (t : ℝ) : 0 ≤ D t := sub_nonneg.mpr (K.volume_bodyAt_le t)
  have hp : Even (q + 1) := hq.add_odd odd_one
  have hP : (∫⁻ x, ENNReal.ofReal ((Max.max K.max 0) ^ (q + 1) -
      (Max.max (K.realLegendre x) 0) ^ (q + 1)) ∂μ) = c * P := by
    rw [lintegral_positive_clipped_gap_eq_weighted_sublevel μ _ K.measurable_realLegendre K.max
      K.realLegendre_le_max_ae q hq.pos]
    exact K.lintegral_weighted_sublevel_eq_const_mul_deficit (q + 1 : ℝ) (by positivity)
      (fun t ↦ (Max.max t 0) ^ q)
  have hN : (∫⁻ x, ENNReal.ofReal ((Max.max (-K.realLegendre x) 0) ^ (q + 1) -
      (Max.max (-K.max) 0) ^ (q + 1)) ∂μ) = c * N := by
    rw [lintegral_negative_clipped_gap_eq_weighted_sublevel μ _ K.measurable_realLegendre K.max
      K.realLegendre_le_max_ae q hq.pos]
    exact K.lintegral_weighted_sublevel_eq_const_mul_deficit (q + 1 : ℝ) (by positivity)
      (fun t ↦ (Max.max (-t) 0) ^ q)
  have hPfinite : c * P < ⊤ := by
    rw [← hP]
    exact lintegral_positive_clipped_gap_lt_top μ _ K.max (q + 1)
  have hμ : μ.real univ = volume.real (Δ : Set (EuclideanSpace ℝ (Fin n))) := by
    change ((volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n)))) univ).toReal = _
    rw [Measure.restrict_apply_univ]
    rfl
  have hEq := lintegral_even_pow_add_clipped_gap μ _ K.measurable_realLegendre K.max
    K.realLegendre_le_max_ae q hq
  rw [hP, hN] at hEq
  have hEqE := congrArg (fun z : ENNReal ↦ (z : EReal)) hEq
  rw [EReal.coe_ennreal_add, EReal.coe_ennreal_add,
    EReal.coe_ennreal_mul (ENNReal.ofReal (K.max ^ (q + 1))) (μ univ),
    EReal.coe_ennreal_ofReal, max_eq_left (hp.pow_nonneg K.max),
    ← EReal.coe_ennreal_toReal (measure_lt_top μ univ).ne, ← EReal.coe_mul] at hEqE
  change ((∫⁻ x, ENNReal.ofReal (K.realLegendre x ^ (q + 1)) ∂μ) : EReal) + ((c * P : ENNReal) : EReal) =
    ((K.max ^ (q + 1) * μ.real univ : ℝ) : EReal) + ((c * N : ENNReal) : EReal) at hEqE
  rw [hμ] at hEqE
  have hSI : SGPT.Convex.extendedSignedIntegral (volume.restrict (Iio K.max))
      (fun t : ℝ ↦ ((t ^ q * (volume.real (K.bodyAt t : Set (EuclideanSpace ℝ (Fin n))) -
        volume.real (Δ : Set (EuclideanSpace ℝ (Fin n)))) : ℝ) : EReal)) = (N : EReal) - (P : EReal) := by
    unfold SGPT.Convex.extendedSignedIntegral
    congr 1
    · congr 1
      apply lintegral_congr
      intro t
      have heq : t ^ q * (volume.real (K.bodyAt t : Set (EuclideanSpace ℝ (Fin n))) -
          volume.real (Δ : Set (EuclideanSpace ℝ (Fin n)))) = t ^ q * -D t := by dsimp [D]; ring
      change ((t ^ q * (volume.real (K.bodyAt t : Set (EuclideanSpace ℝ (Fin n))) -
        volume.real (Δ : Set (EuclideanSpace ℝ (Fin n)))) : ℝ) : EReal).toENNReal = _
      rw [heq]
      exact (odd_pow_negative_density_parts q hq t (D t) (hD t)).1
    · congr 1
      apply lintegral_congr
      intro t
      have heq : t ^ q * (volume.real (K.bodyAt t : Set (EuclideanSpace ℝ (Fin n))) -
          volume.real (Δ : Set (EuclideanSpace ℝ (Fin n)))) = t ^ q * -D t := by dsimp [D]; ring
      change (-((t ^ q * (volume.real (K.bodyAt t : Set (EuclideanSpace ℝ (Fin n))) -
        volume.real (Δ : Set (EuclideanSpace ℝ (Fin n)))) : ℝ) : EReal)).toENNReal = _
      rw [heq]
      exact (odd_pow_negative_density_parts q hq t (D t) (hD t)).2
  rw [K.signed_polynomial_moment_pushforward]
  have hM : SGPT.Convex.extendedSignedIntegral μ
      (fun x ↦ (K.realLegendre x : EReal) ^ (q + 1)) =
      ((∫⁻ x, ENNReal.ofReal (K.realLegendre x ^ (q + 1)) ∂μ) : EReal) := by
    unfold SGPT.Convex.extendedSignedIntegral
    simp only [← EReal.coe_pow, EReal.real_coe_toENNReal]
    have hz (x : EuclideanSpace ℝ (Fin n)) :
        (-((K.realLegendre x ^ (q + 1) : ℝ) : EReal)).toENNReal = 0 := by
      rw [← EReal.coe_neg, EReal.real_coe_toENNReal]
      exact ENNReal.ofReal_of_nonpos (neg_nonpos.mpr (hp.pow_nonneg _))
    simp only [hz, lintegral_zero, EReal.coe_ennreal_zero, sub_zero]
  rw [hM, hSI]
  calc
    _ = (((∫⁻ x, ENNReal.ofReal (K.realLegendre x ^ (q + 1)) ∂μ) : EReal) +
        ((c * P : ENNReal) : EReal)) - ((c * P : ENNReal) : EReal) := by
      rw [← EReal.coe_ennreal_toReal hPfinite.ne, EReal.add_sub_cancel_right]
    _ = (((K.max ^ (q + 1) * volume.real (Δ : Set (EuclideanSpace ℝ (Fin n))) : ℝ) : EReal) +
        ((c * N : ENNReal) : EReal)) - ((c * P : ENNReal) : EReal) := by rw [hEqE]
    _ = _ := by
      have hcoeff : (q + 1 : EReal) = ((q + 1 : ℝ) : EReal) := by
        rw [EReal.coe_add]
        rfl
      rw [hcoeff, EReal.mul_sub_of_nonneg_of_ne_top
        (EReal.coe_nonneg.mpr (by positivity : (0 : ℝ) ≤ q + 1)) (EReal.coe_ne_top _)]
      dsimp only [c]
      simp only [EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal,
        max_eq_left (by positivity : (0 : ℝ) ≤ q + 1)]
      simp only [sub_eq_add_neg, add_assoc]

/-- Full literal source `prop:DHmoments` / `eq:momentcalc` for every original
positive integer, with both possible divergent parity branches retained. -/
theorem polynomial_moment_eq (p : ℕ) (hp : 0 < p) :
    SGPT.Convex.extendedSignedIntegral K.duistermaatHeckman (fun t : ℝ ↦ (t : EReal) ^ p) =
      ((K.max ^ p * volume.real (Δ : Set (EuclideanSpace ℝ (Fin n))) : ℝ) : EReal) +
        (p : EReal) * SGPT.Convex.extendedSignedIntegral (volume.restrict (Iio K.max))
          (fun t : ℝ ↦ ((t ^ (p - 1) * (volume.real (K.bodyAt t : Set (EuclideanSpace ℝ (Fin n))) -
            volume.real (Δ : Set (EuclideanSpace ℝ (Fin n)))) : ℝ) : EReal)) := by
  cases p with
  | zero => exact False.elim (Nat.not_lt_zero 0 hp)
  | succ q =>
    rcases Nat.even_or_odd q with hq | hq
    · simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
        using K.odd_polynomial_moment_eq q hq
    · simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
        using K.even_polynomial_moment_eq q hq

end TestCurve

end SGPT.Okounkov
