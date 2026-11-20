import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Hom.Set
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.MonotoneContinuity

noncomputable section
namespace SGPT.AlmostSemigroup.CumulativeVolume
open Set Filter MeasureTheory
open scoped Topology

/-- The actual normalized primitive of the original real density. -/
def cumulative (f : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  (∫ t in a..x, f t) / (∫ t in a..b, f t)

variable {f : ℝ → ℝ} {a b : ℝ}

/-- Genuine interior positivity gives positive actual integral on every strict original subinterval. -/
theorem integral_pos_of_interior_pos
    (hcont : ContinuousOn f (Icc a b))
    (hnonneg : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x < y) :
    0 < ∫ t in x..y, f t := by
  have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
  apply intervalIntegral.integral_pos hxy (hcont.mono hsub)
  · intro t ht
    exact hnonneg t (hsub ⟨ht.1.le, ht.2⟩)
  · refine ⟨(x + y) / 2, ⟨by linarith, by linarith⟩, hpos _ ?_⟩
    constructor <;> linarith [hx.1, hy.2]

/-- The actual total density mass is strictly positive, without a mass hypothesis. -/
theorem mass_pos (hab : a < b)
    (hcont : ContinuousOn f (Icc a b))
    (hnonneg : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) :
    0 < ∫ t in a..b, f t :=
  integral_pos_of_interior_pos hcont hnonneg hpos ⟨le_rfl, hab.le⟩
    ⟨hab.le, le_rfl⟩ hab

/-- Continuity of the actual normalized original primitive on the entire source interval. -/
theorem continuousOn_cumulative (hab : a ≤ b)
    (hcont : ContinuousOn f (Icc a b)) :
    ContinuousOn (cumulative f a b) (Icc a b) := by
  have h := intervalIntegral.continuousOn_primitive_interval'
    (hcont.intervalIntegrable_of_Icc hab (μ := volume)) (left_mem_uIcc : a ∈ uIcc a b)
  rw [uIcc_of_le hab] at h
  exact h.div_const _

/-- Actual adjacent integrals turn genuine density positivity into strict cumulative increase. -/
theorem strictMonoOn_cumulative (hab : a < b)
    (hcont : ContinuousOn f (Icc a b))
    (hnonneg : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) :
    StrictMonoOn (cumulative f a b) (Icc a b) := by
  have hm := mass_pos hab hcont hnonneg hpos
  intro x hx y hy hxy
  apply (div_lt_div_iff_of_pos_right hm).mpr
  have hix : IntervalIntegrable f volume a x :=
    (hcont.mono (Icc_subset_Icc le_rfl hx.2)).intervalIntegrable_of_Icc hx.1
  have hiy : IntervalIntegrable f volume a y :=
    (hcont.mono (Icc_subset_Icc le_rfl hy.2)).intervalIntegrable_of_Icc hy.1
  have hd := intervalIntegral.integral_interval_sub_left hiy hix
  have hp := integral_pos_of_interior_pos hcont hnonneg hpos hx hy hxy
  linarith

theorem cumulative_left : cumulative f a b a = 0 := by simp [cumulative]

theorem cumulative_right (hab : a < b)
    (hcont : ContinuousOn f (Icc a b))
    (hnonneg : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) :
    cumulative f a b b = 1 := by
  exact div_self (ne_of_gt (mass_pos hab hcont hnonneg hpos))

/-- The actual continuous normalized primitive covers exactly the whole unit interval. -/
theorem image_cumulative (hab : a < b)
    (hcont : ContinuousOn f (Icc a b))
    (hnonneg : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) :
    cumulative f a b '' Icc a b = Icc 0 1 := by
  have hc := continuousOn_cumulative hab.le hcont
  have hm := (strictMonoOn_cumulative hab hcont hnonneg hpos).monotoneOn
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hright := cumulative_right hab hcont hnonneg hpos
  apply subset_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    constructor
    · simpa only [cumulative_left] using hm ha hx hx.1
    · simpa only [hright] using hm hx hb hx.2
  · intro y hy
    exact hc.surjOn_Icc ha hb (by simpa only [cumulative_left, hright] using hy)

/-- Genuine local density continuity produces the actual cumulative derivative. -/
theorem hasDerivAt_cumulative (hcont : ContinuousOn f (Icc a b)) {x : ℝ}
    (hx : x ∈ Ioo a b) :
    HasDerivAt (cumulative f a b) (f x / (∫ t in a..b, f t)) x := by
  have hfc : ContinuousAt f x :=
    hcont.continuousAt (Icc_mem_nhds hx.1 hx.2)
  have hmeas : StronglyMeasurableAtFilter f (𝓝 x) volume :=
    (hcont.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx
  have hi : IntervalIntegrable f volume a x :=
    (hcont.mono (Icc_subset_Icc le_rfl hx.2.le)).intervalIntegrable_of_Icc hx.1.le
  exact (intervalIntegral.integral_hasDerivAt_right hi hmeas hfc).div_const _

variable (hab : a < b) (hcont : ContinuousOn f (Icc a b))
  (hnonneg : ∀ x ∈ Icc a b, 0 ≤ f x) (hpos : ∀ x ∈ Ioo a b, 0 < f x)

/-- The actual cumulative function itself supplies its order isomorphism with the unit interval. -/
def cumulativeOrderIso : Icc a b ≃o Icc (0 : ℝ) 1 :=
  ((strictMonoOn_cumulative hab hcont hnonneg hpos).orderIso (cumulative f a b) (Icc a b)).trans
    (OrderIso.setCongr _ _ (image_cumulative hab hcont hnonneg hpos))

theorem cumulativeOrderIso_apply (x : Icc a b) :
    (cumulativeOrderIso hab hcont hnonneg hpos x : ℝ) = cumulative f a b x := rfl

/-- The genuine inverse of the actual constructed cumulative map, extended by the left endpoint outside its actual target interval. -/
def inverse (y : ℝ) : ℝ :=
  if hy : y ∈ Icc (0 : ℝ) 1 then
    (cumulativeOrderIso hab hcont hnonneg hpos).symm ⟨y, hy⟩ else a

theorem inverse_mem {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    inverse hab hcont hnonneg hpos y ∈ Icc a b := by
  simpa only [inverse, dif_pos hy] using
    ((cumulativeOrderIso hab hcont hnonneg hpos).symm ⟨y, hy⟩).property

/-- The actual order inverse gives the actual cumulative right-inverse identity. -/
theorem cumulative_inverse {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    cumulative f a b (inverse hab hcont hnonneg hpos y) = y := by
  have h := congrArg Subtype.val ((cumulativeOrderIso hab hcont hnonneg hpos).apply_symm_apply ⟨y, hy⟩)
  simpa only [cumulativeOrderIso_apply, inverse, dif_pos hy] using h

/-- The actual cumulative left-inverse identity on the original full interval. -/
theorem inverse_cumulative {x : ℝ} (hx : x ∈ Icc a b) :
    inverse hab hcont hnonneg hpos (cumulative f a b x) = x := by
  have ht : cumulative f a b x ∈ Icc (0 : ℝ) 1 := by
    rw [← image_cumulative hab hcont hnonneg hpos]
    exact mem_image_of_mem _ hx
  have h := congrArg Subtype.val ((cumulativeOrderIso hab hcont hnonneg hpos).symm_apply_apply ⟨x, hx⟩)
  have he : cumulativeOrderIso hab hcont hnonneg hpos ⟨x, hx⟩ = ⟨cumulative f a b x, ht⟩ :=
    Subtype.ext (cumulativeOrderIso_apply hab hcont hnonneg hpos ⟨x, hx⟩)
  rw [he] at h
  simpa only [inverse, dif_pos ht, cumulativeOrderIso_apply] using h

/-- Genuine order-isomorphism continuity gives actual inverse continuity, including endpoints. -/
theorem continuousOn_inverse :
    ContinuousOn (inverse hab hcont hnonneg hpos) (Icc (0 : ℝ) 1) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  convert (cumulativeOrderIso hab hcont hnonneg hpos).symm.continuous.subtype_val using 1
  funext y
  simp only [domRestrict_apply, inverse, dif_pos y.property]

/-- A genuine interior cumulative value has its actual inverse inside the original strict interval. -/
theorem inverse_mem_Ioo {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    inverse hab hcont hnonneg hpos y ∈ Ioo a b := by
  have hm := inverse_mem hab hcont hnonneg hpos (Ioo_subset_Icc_self hy)
  have heq := cumulative_inverse hab hcont hnonneg hpos (Ioo_subset_Icc_self hy)
  constructor
  · by_contra h
    have hx : inverse hab hcont hnonneg hpos y = a := le_antisymm (le_of_not_gt h) hm.1
    rw [hx, cumulative_left] at heq
    linarith [hy.1]
  · by_contra h
    have hx : inverse hab hcont hnonneg hpos y = b := le_antisymm hm.2 (le_of_not_gt h)
    rw [hx, cumulative_right hab hcont hnonneg hpos] at heq
    linarith [hy.2]

/-- The actual inverse derivative follows from the produced inverse, true interior continuity and the genuine cumulative derivative. -/
theorem hasDerivAt_inverse {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (inverse hab hcont hnonneg hpos)
      ((∫ t in a..b, f t) / f (inverse hab hcont hnonneg hpos y)) y := by
  have hx := inverse_mem_Ioo hab hcont hnonneg hpos hy
  have hc := (continuousOn_inverse hab hcont hnonneg hpos).continuousAt (Icc_mem_nhds hy.1 hy.2)
  have hd := hasDerivAt_cumulative hcont hx
  have hdne : f (inverse hab hcont hnonneg hpos y) / (∫ t in a..b, f t) ≠ 0 :=
    ne_of_gt (div_pos (hpos _ hx) (mass_pos hab hcont hnonneg hpos))
  have heq : ∀ᶠ z in 𝓝 y, cumulative f a b (inverse hab hcont hnonneg hpos z) = z := by
    filter_upwards [Icc_mem_nhds hy.1 hy.2] with z hz
    exact cumulative_inverse hab hcont hnonneg hpos hz
  simpa only [inv_div] using hd.of_local_left_inverse hc hdne heq

end SGPT.AlmostSemigroup.CumulativeVolume
