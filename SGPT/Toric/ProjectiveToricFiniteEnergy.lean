import SGPT.Toric.ProjectiveToricFullMassBounded
import SGPT.Toric.ProjectiveGlobalTropicalData
import SGPT.PSH.AtlasQPSHAddition
import SGPT.Convex.MixedAlexandrovIdentities
import SGPT.Convex.AlexandrovContinuity
import SGPT.Okounkov.LegendreEnergyEquality
import SGPT.Okounkov.DuistermaatHeckmanMoments
import SGPT.Foundations.Analysis.Pending.MongeAmpereEnergyDecreasing
import SGPT.Foundations.Analysis.Pending.GlobalSlotStokes
import SGPT.Foundations.Analysis.Pending.MeteredDivisorPositivity
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set Filter MeasureTheory SGPT.PSH SGPT.Convex
open SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open SGPT.Foundations.Analysis.Pending.MongeAmpereEnergyDecreasing
open scoped Topology RealInnerProductSpace NNReal ENNReal

local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)
local notation "E1" => EuclideanSpace ℝ (Fin 1)
local notation "B" => innerₗ E1

private theorem rankOneMA_linearCombination
    (f g : RealConvexFunction E1) (c d : ℝ≥0) :
    alexandrovMeasure B volume
        (fun x => (((c : ℝ) * f.val x + (d : ℝ) * g.val x : ℝ) : EReal)) =
      c • alexandrovMeasure B volume (fun x => (f.val x : EReal)) +
        d • alexandrovMeasure B volume (fun x => (g.val x : EReal)) := by
  let b := EuclideanSpace.basisFun (Fin 1) ℝ
  have hupdate (a : RealConvexFunction E1) :
      Function.update (fun _ : Fin 1 => f) 0 a = (fun _ : Fin 1 => a) := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp
  have hm := mixedAlexandrovMeasure_update_linear_combination volume b
    (fun _ : Fin 1 => f) 0 c d f g
  rw [hupdate, hupdate, hupdate,
    mixedAlexandrovMeasure_diagonal volume b,
    mixedAlexandrovMeasure_diagonal volume b,
    mixedAlexandrovMeasure_diagonal volume b] at hm
  exact hm

private theorem rankOneDifferenceBound
    {P : Set E1} {f g : E1 → ℝ}
    (hf : (fun x => (f x : EReal)) ∈ BoundedGrowthClass B P)
    (hg : (fun x => (g x : EReal)) ∈ BoundedGrowthClass B P) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |g x - f x| ≤ K := by
  have hgf := singularityLE_trans hg.2.1 hf.2.2
  have hfg := singularityLE_trans hf.2.1 hg.2.2
  obtain ⟨C, hC⟩ := (singularityLE_iff_exists_real _ _).mp hgf
  obtain ⟨D, hD⟩ := (singularityLE_iff_exists_real _ _).mp hfg
  refine ⟨|C| + |D|, add_nonneg (abs_nonneg _) (abs_nonneg _), fun x => ?_⟩
  have hc : g x ≤ f x + C := by
    simpa only [← EReal.coe_add, EReal.coe_le_coe_iff] using hC x
  have hd : f x ≤ g x + D := by
    simpa only [← EReal.coe_add, EReal.coe_le_coe_iff] using hD x
  apply abs_le.mpr
  constructor <;> linarith [le_abs_self C, le_abs_self D, abs_nonneg C, abs_nonneg D]

private def rankOneInterpolation (f g : RealConvexFunction E1) (t : ℝ) : E1 → ℝ :=
  fun x => (1 - t) * f.val x + t * g.val x

private theorem rankOneInterpolation_convex (f g : RealConvexFunction E1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ConvexOn ℝ univ (rankOneInterpolation f g t) := by
  exact (f.property.smul (sub_nonneg.mpr ht.2)).add (g.property.smul ht.1)

private theorem rankOneInterpolation_boundedGrowth
    {P : Set E1} (hP : IsCompact P) (hne : P.Nonempty)
    (f g : RealConvexFunction E1)
    (hf : (fun x => (f.val x : EReal)) ∈ BoundedGrowthClass B P)
    (hg : (fun x => (g.val x : EReal)) ∈ BoundedGrowthClass B P)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (fun x => (rankOneInterpolation f g t x : EReal)) ∈ BoundedGrowthClass B P := by
  have hcv := rankOneInterpolation_convex f g ht
  have hp := isProper_coe_of_convexOn hcv
  have hdom : effectiveDomain (fun x => (rankOneInterpolation f g t x : EReal)) =
      univ := by ext x; simp [effectiveDomain]
  refine ⟨isClosedConvex_of_isProper_full_domain hp hdom, ?_⟩
  obtain ⟨C0, hC0⟩ := (singularityLE_iff_exists_real _ _).mp hf.2.1
  obtain ⟨C1, hC1⟩ := (singularityLE_iff_exists_real _ _).mp hg.2.1
  obtain ⟨D0, hD0⟩ := (singularityLE_iff_exists_real _ _).mp hf.2.2
  obtain ⟨D1, hD1⟩ := (singularityLE_iff_exists_real _ _).mp hg.2.2
  constructor
  · apply (singularityLE_iff_exists_real _ _).mpr
    refine ⟨(1 - t) * C0 + t * C1, fun x => ?_⟩
    obtain ⟨r, hr⟩ := exists_real_support_value B hP hne x
    have hfU : f.val x ≤ r + C0 := by
      simpa only [hr, ← EReal.coe_add, EReal.coe_le_coe_iff] using hC0 x
    have hgU : g.val x ≤ r + C1 := by
      simpa only [hr, ← EReal.coe_add, EReal.coe_le_coe_iff] using hC1 x
    rw [hr, ← EReal.coe_add, EReal.coe_le_coe_iff]
    unfold rankOneInterpolation
    nlinarith [mul_le_mul_of_nonneg_left hfU (sub_nonneg.mpr ht.2),
      mul_le_mul_of_nonneg_left hgU ht.1]
  · apply (singularityLE_iff_exists_real _ _).mpr
    refine ⟨(1 - t) * D0 + t * D1, fun x => ?_⟩
    obtain ⟨r, hr⟩ := exists_real_support_value B hP hne x
    have hfL : r ≤ f.val x + D0 := by
      simpa only [hr, ← EReal.coe_add, EReal.coe_le_coe_iff] using hD0 x
    have hgL : r ≤ g.val x + D1 := by
      simpa only [hr, ← EReal.coe_add, EReal.coe_le_coe_iff] using hD1 x
    rw [hr, ← EReal.coe_add, EReal.coe_le_coe_iff]
    unfold rankOneInterpolation
    nlinarith [mul_le_mul_of_nonneg_left hfL (sub_nonneg.mpr ht.2),
      mul_le_mul_of_nonneg_left hgL ht.1]

private theorem rankOneConjugateCostBound
    {f g : E1 → ℝ} {K : ℝ} (hK : ∀ x, |g x - f x| ≤ K) (m : E1) :
    conjugate B (fun x => (f x : EReal)) m ≤
        conjugate B (fun x => (g x : EReal)) m + (K : EReal) ∧
    conjugate B (fun x => (g x : EReal)) m ≤
        conjugate B (fun x => (f x : EReal)) m + (K : EReal) := by
  constructor
  · apply iSup_le
    intro x
    have hh : (g x : EReal) ≤ (f x : EReal) + (K : EReal) := by
      rw [← EReal.coe_add, EReal.coe_le_coe_iff]
      linarith [(abs_le.mp (hK x)).2]
    exact (real_sub_le_real_sub_add (B x m) K hh).trans
      (add_le_add (le_iSup (fun y => (B y m : EReal) - (g y : EReal)) x) le_rfl)
  · apply iSup_le
    intro x
    have hh : (f x : EReal) ≤ (g x : EReal) + (K : EReal) := by
      rw [← EReal.coe_add, EReal.coe_le_coe_iff]
      linarith [(abs_le.mp (hK x)).1]
    exact (real_sub_le_real_sub_add (B x m) K hh).trans
      (add_le_add (le_iSup (fun y => (B y m : EReal) - (f y : EReal)) x) le_rfl)

private theorem rankOneInterpolationDifferenceBound
    (f g : RealConvexFunction E1) {K : ℝ} (hK : ∀ x, |g.val x - f.val x| ≤ K)
    (s t : ℝ) (x : E1) :
    |rankOneInterpolation f g s x - rankOneInterpolation f g t x| ≤ |s - t| * K := by
  have he : rankOneInterpolation f g s x - rankOneInterpolation f g t x =
      (s - t) * (g.val x - f.val x) := by unfold rankOneInterpolation; ring
  rw [he, abs_mul]
  exact mul_le_mul_of_nonneg_left (hK x) (abs_nonneg _)

private theorem rankOneMA_finite
    {P : Set E1} (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    {f : E1 → ℝ}
    (hf : (fun x => (f x : EReal)) ∈ BoundedGrowthClass B P) :
    IsFiniteMeasure (alexandrovMeasure B volume (fun x => (f x : EReal))) := by
  let : IsFiniteMeasure (volume.restrict P) := ⟨by simpa using hP.measure_lt_top⟩
  have he := alexandrovMeasure_eq_gradient_pushforward_of_mem_fullMassClass (ν := volume) B hP hne hconv
    (mem_fullMassClass_of_mem_boundedGrowthClass B hP hne hconv hf)
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.factorial_one,
    Nat.cast_one, one_smul] at he
  rw [he]
  infer_instance

private theorem rankOneDifference_integrable
    {P : Set E1} (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (f g a : RealConvexFunction E1)
    (hf : (fun x => (f.val x : EReal)) ∈ BoundedGrowthClass B P)
    (hg : (fun x => (g.val x : EReal)) ∈ BoundedGrowthClass B P)
    (ha : (fun x => (a.val x : EReal)) ∈ BoundedGrowthClass B P) :
    Integrable (fun x => g.val x - f.val x)
      (alexandrovMeasure B volume (fun x => (a.val x : EReal))) := by
  let := rankOneMA_finite hP hne hconv ha
  have hc : Continuous (fun x => g.val x - f.val x) :=
    (continuousOn_univ.mp (g.property.continuousOn isOpen_univ)).sub
      (continuousOn_univ.mp (f.property.continuousOn isOpen_univ))
  obtain ⟨K, _hK, hb⟩ := rankOneDifferenceBound hf hg
  exact Integrable.of_bound hc.aestronglyMeasurable K
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x))

private theorem rankOneIntegralAffine
    {P : Set E1} (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (f g : RealConvexFunction E1)
    (hf : (fun x => (f.val x : EReal)) ∈ BoundedGrowthClass B P)
    (hg : (fun x => (g.val x : EReal)) ∈ BoundedGrowthClass B P)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ x, (g.val x - f.val x)
      ∂alexandrovMeasure B volume (fun x => (rankOneInterpolation f g t x : EReal))) =
      (1 - t) * (∫ x, (g.val x - f.val x)
        ∂alexandrovMeasure B volume (fun x => (f.val x : EReal))) +
      t * (∫ x, (g.val x - f.val x)
        ∂alexandrovMeasure B volume (fun x => (g.val x : EReal))) := by
  let c : ℝ≥0 := ⟨1 - t, sub_nonneg.mpr ht.2⟩
  let d : ℝ≥0 := ⟨t, ht.1⟩
  have he := rankOneMA_linearCombination f g c d
  change alexandrovMeasure B volume
      (fun x => (rankOneInterpolation f g t x : EReal)) = _ at he
  rw [he, integral_add_measure]
  · simp only [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
    rfl
  · exact (rankOneDifference_integrable hP hne hconv f g f hf hg hf).smul_measure_nnreal (c := c)
  · exact (rankOneDifference_integrable hP hne hconv f g g hf hg hg).smul_measure_nnreal (c := d)

private theorem rankOneConjugate_coe_toReal
    {P : Set E1} (hP : IsCompact P) (hconv : Convex ℝ P)
    {f : E1 → ℝ}
    (hf : (fun x => (f x : EReal)) ∈ BoundedGrowthClass B P) {m : E1} (hm : m ∈ P) :
    ((conjugate B (fun x => (f x : EReal)) m).toReal : EReal) =
      conjugate B (fun x => (f x : EReal)) m := by
  obtain ⟨a, b, hb⟩ := conjugate_bounds_of_mem_boundedGrowthClass B hP hconv hf
  exact EReal.coe_toReal
    (ne_top_of_le_ne_top (EReal.coe_ne_top b) (hb m hm).2)
    (ne_bot_of_le_ne_bot (EReal.coe_ne_bot a) (hb m hm).1)

private theorem rankOneConjugate_integrable
    {P : Set E1} (hP : IsCompact P) (hconv : Convex ℝ P)
    {f : E1 → ℝ}
    (hf : (fun x => (f x : EReal)) ∈ BoundedGrowthClass B P) :
    IntegrableOn (fun m => (conjugate B (fun x => (f x : EReal)) m).toReal) P volume := by
  obtain ⟨a, b, hb⟩ := conjugate_bounds_of_mem_boundedGrowthClass B hP hconv hf
  apply IntegrableOn.of_bound hP.measure_lt_top
    (measurable_conjugate B (fun x => (f x : EReal))).ereal_toReal.aestronglyMeasurable
    (|a| + |b|)
  filter_upwards [ae_restrict_mem hP.measurableSet] with m hm
  have hh := hb m hm
  rw [← rankOneConjugate_coe_toReal hP hconv hf hm] at hh
  simp only [EReal.coe_le_coe_iff] at hh
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith [le_abs_self a, le_abs_self b, neg_le_abs a, abs_nonneg a, abs_nonneg b]

private def rankOneLegendreDifferenceIntegral
    (f g : RealConvexFunction E1) (P : Set E1) (t : ℝ) : ℝ :=
  ∫ m in P, (conjugate B (fun x => (f.val x : EReal)) m).toReal -
    (conjugate B (fun x => (rankOneInterpolation f g t x : EReal)) m).toReal

private theorem rankOneLegendreDifferenceIntegral_continuous
    {P : Set E1} (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (f g : RealConvexFunction E1)
    (hf : (fun x => (f.val x : EReal)) ∈ BoundedGrowthClass B P)
    (hg : (fun x => (g.val x : EReal)) ∈ BoundedGrowthClass B P) :
    ContinuousOn (rankOneLegendreDifferenceIntegral f g P) (Icc (0 : ℝ) 1) := by
  let : IsFiniteMeasure (volume.restrict P) := ⟨by simpa using hP.measure_lt_top⟩
  obtain ⟨K, hK, hb⟩ := rankOneDifferenceBound hf hg
  let L : ℝ≥0 := ⟨K * (volume.restrict P).real univ,
    mul_nonneg hK measureReal_nonneg⟩
  apply (LipschitzOnWith.of_dist_le_mul (K := L) ?_).continuousOn
  intro s hs t ht
  have hfs := rankOneInterpolation_boundedGrowth hP hne f g hf hg hs
  have hft := rankOneInterpolation_boundedGrowth hP hne f g hf hg ht
  have hJ : rankOneLegendreDifferenceIntegral f g P s -
      rankOneLegendreDifferenceIntegral f g P t =
      ∫ m in P, (conjugate B (fun x => (rankOneInterpolation f g t x : EReal)) m).toReal -
        (conjugate B (fun x => (rankOneInterpolation f g s x : EReal)) m).toReal := by
    unfold rankOneLegendreDifferenceIntegral
    have he := (integral_sub
      ((rankOneConjugate_integrable hP hconv hf).sub (rankOneConjugate_integrable hP hconv hfs))
      ((rankOneConjugate_integrable hP hconv hf).sub (rankOneConjugate_integrable hP hconv hft))).symm
    simp only [Pi.sub_apply] at he
    rw [he]
    apply integral_congr_ae
    exact Eventually.of_forall (fun _ => by ring)
  have hbound : ∀ᵐ m ∂volume.restrict P,
      ‖(conjugate B (fun x => (rankOneInterpolation f g t x : EReal)) m).toReal -
        (conjugate B (fun x => (rankOneInterpolation f g s x : EReal)) m).toReal‖ ≤
          |s - t| * K := by
    filter_upwards [ae_restrict_mem hP.measurableSet] with m hm
    have hc := rankOneConjugateCostBound
      (fun x => rankOneInterpolationDifferenceBound f g hb s t x) m
    rw [← rankOneConjugate_coe_toReal hP hconv hft hm,
      ← rankOneConjugate_coe_toReal hP hconv hfs hm,
      ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff] at hc
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hc.2], by linarith [hc.1]⟩
  rw [Real.dist_eq, hJ]
  have hh := norm_integral_le_of_norm_le_const hbound
  change |∫ m in P,
      (conjugate B (fun x => (rankOneInterpolation f g t x : EReal)) m).toReal -
        (conjugate B (fun x => (rankOneInterpolation f g s x : EReal)) m).toReal| ≤
      (K * (volume.restrict P).real univ) * dist s t
  simpa only [Real.norm_eq_abs, Real.dist_eq, mul_assoc, mul_comm,
    mul_left_comm] using hh

private theorem rankOneRawFenchelAt
    {f : E1 → ℝ} (hf : ConvexOn ℝ univ f) {m : E1}
    (hm : m ∈ interior (effectiveDomain (conjugate B (fun x => (f x : EReal)))))
    (hd : DifferentiableAt ℝ
      (fun p => (conjugate B (fun x => (f x : EReal)) p).toReal) m) :
    (conjugate B (fun x => (f x : EReal)) m).toReal =
      B (conjugateGradient B (fun x => (f x : EReal)) m) m -
        f (conjugateGradient B (fun x => (f x : EReal)) m) := by
  have hp := isProper_coe_of_convexOn hf
  have hraw := mem_rawSubdifferential_conjugateGradient_coe B hf hm hd
  rw [rawSubdifferential_eq_subdifferential_of_isProper B hp] at hraw
  have he := (mem_subdifferential_iff_fenchel B hp (by simp [effectiveDomain])).mp hraw
  simpa only [← EReal.coe_sub, EReal.toReal_coe] using congrArg EReal.toReal he

private theorem rankOneInterpolationFenchelSlope
    (f g : RealConvexFunction E1) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) {m : E1}
    (hms : m ∈ interior (effectiveDomain
      (conjugate B (fun x => (rankOneInterpolation f g s x : EReal)))))
    (hmt : m ∈ interior (effectiveDomain
      (conjugate B (fun x => (rankOneInterpolation f g t x : EReal)))))
    (hds : DifferentiableAt ℝ
      (fun p => (conjugate B (fun x => (rankOneInterpolation f g s x : EReal)) p).toReal) m)
    (hdt : DifferentiableAt ℝ
      (fun p => (conjugate B (fun x => (rankOneInterpolation f g t x : EReal)) p).toReal) m) :
    let xs := conjugateGradient B (fun x => (rankOneInterpolation f g s x : EReal)) m
    let xt := conjugateGradient B (fun x => (rankOneInterpolation f g t x : EReal)) m
    let Gs := (conjugate B (fun x => (rankOneInterpolation f g s x : EReal)) m).toReal
    let Gt := (conjugate B (fun x => (rankOneInterpolation f g t x : EReal)) m).toReal
    (s - t) * (g.val xs - f.val xs) ≤ Gt - Gs ∧
      Gt - Gs ≤ (s - t) * (g.val xt - f.val xt) := by
  let xs := conjugateGradient B (fun x => (rankOneInterpolation f g s x : EReal)) m
  let xt := conjugateGradient B (fun x => (rankOneInterpolation f g t x : EReal)) m
  have hGs := rankOneRawFenchelAt (rankOneInterpolation_convex f g hs) hms hds
  have hGt := rankOneRawFenchelAt (rankOneInterpolation_convex f g ht) hmt hdt
  have hboundS : B xt m - rankOneInterpolation f g s xt ≤
      (conjugate B (fun x => (rankOneInterpolation f g s x : EReal)) m).toReal := by
    have hsTop : m ∈ effectiveDomain
        (conjugate B (fun x => (rankOneInterpolation f g s x : EReal))) :=
      interior_subset hms
    change conjugate B (fun x => (rankOneInterpolation f g s x : EReal)) m < ⊤ at hsTop
    have hh := le_iSup (fun x : E1 =>
      (B x m : EReal) - (rankOneInterpolation f g s x : EReal)) xt
    rw [← EReal.coe_sub] at hh
    change ((B xt m - rankOneInterpolation f g s xt : ℝ) : EReal) ≤
      conjugate B (fun x => (rankOneInterpolation f g s x : EReal)) m at hh
    simpa only [EReal.toReal_coe] using
      EReal.toReal_le_toReal hh (EReal.coe_ne_bot _) (ne_of_lt hsTop)
  have hboundT : B xs m - rankOneInterpolation f g t xs ≤
      (conjugate B (fun x => (rankOneInterpolation f g t x : EReal)) m).toReal := by
    have htTop : m ∈ effectiveDomain
        (conjugate B (fun x => (rankOneInterpolation f g t x : EReal))) :=
      interior_subset hmt
    change conjugate B (fun x => (rankOneInterpolation f g t x : EReal)) m < ⊤ at htTop
    have hh := le_iSup (fun x : E1 =>
      (B x m : EReal) - (rankOneInterpolation f g t x : EReal)) xs
    rw [← EReal.coe_sub] at hh
    change ((B xs m - rankOneInterpolation f g t xs : ℝ) : EReal) ≤
      conjugate B (fun x => (rankOneInterpolation f g t x : EReal)) m at hh
    simpa only [EReal.toReal_coe] using
      EReal.toReal_le_toReal hh (EReal.coe_ne_bot _) (ne_of_lt htTop)
  dsimp only
  rw [hGs, hGt]
  change (s - t) * (g.val xs - f.val xs) ≤
      (B xt m - rankOneInterpolation f g t xt) -
        (B xs m - rankOneInterpolation f g s xs) ∧
    (B xt m - rankOneInterpolation f g t xt) -
      (B xs m - rankOneInterpolation f g s xs) ≤ (s - t) * (g.val xt - f.val xt)
  rw [hGs] at hboundS
  rw [hGt] at hboundT
  dsimp [xs, xt] at hboundS hboundT
  change B xt m - rankOneInterpolation f g s xt ≤
      B xs m - rankOneInterpolation f g s xs at hboundS
  change B xs m - rankOneInterpolation f g t xs ≤
      B xt m - rankOneInterpolation f g t xt at hboundT
  unfold rankOneInterpolation at hboundS hboundT ⊢
  constructor <;> nlinarith

private theorem rankOneInterpolationFenchelSlope_ae
    {P : Set E1} (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (f g : RealConvexFunction E1)
    (hf : (fun x => (f.val x : EReal)) ∈ BoundedGrowthClass B P)
    (hg : (fun x => (g.val x : EReal)) ∈ BoundedGrowthClass B P)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ m ∂volume.restrict P,
      let xs := conjugateGradient B (fun x => (rankOneInterpolation f g s x : EReal)) m
      let xt := conjugateGradient B (fun x => (rankOneInterpolation f g t x : EReal)) m
      let Gs := (conjugate B (fun x => (rankOneInterpolation f g s x : EReal)) m).toReal
      let Gt := (conjugate B (fun x => (rankOneInterpolation f g t x : EReal)) m).toReal
      (s - t) * (g.val xs - f.val xs) ≤ Gt - Gs ∧
        Gt - Gs ≤ (s - t) * (g.val xt - f.val xt) := by
  have hfs := rankOneInterpolation_boundedGrowth hP hne f g hf hg hs
  have hft := rankOneInterpolation_boundedGrowth hP hne f g hf hg ht
  have hms := interior_effectiveDomain_conjugate_ae_eq_of_mem_fullMassClass (ν := volume) B hP hne hconv
    (mem_fullMassClass_of_mem_boundedGrowthClass B hP hne hconv hfs)
  have hmt := interior_effectiveDomain_conjugate_ae_eq_of_mem_fullMassClass (ν := volume) B hP hne hconv
    (mem_fullMassClass_of_mem_boundedGrowthClass B hP hne hconv hft)
  have hds := ae_differentiableAt_toReal_of_isProper (μ := volume)
    (isProper_conjugate_of_isContPerfPair B
      (isProper_coe_of_convexOn (rankOneInterpolation_convex f g hs)))
  have hdt := ae_differentiableAt_toReal_of_isProper (μ := volume)
    (isProper_conjugate_of_isContPerfPair B
      (isProper_coe_of_convexOn (rankOneInterpolation_convex f g ht)))
  filter_upwards [ae_restrict_of_ae hms, ae_restrict_of_ae hmt,
    ae_restrict_of_ae hds, ae_restrict_of_ae hdt, ae_restrict_mem hP.measurableSet]
    with m hms' hmt' hds' hdt' hm
  have hims : m ∈ interior (effectiveDomain
      (conjugate B (fun x => (rankOneInterpolation f g s x : EReal)))) := hms'.mpr hm
  have himt : m ∈ interior (effectiveDomain
      (conjugate B (fun x => (rankOneInterpolation f g t x : EReal)))) := hmt'.mpr hm
  exact rankOneInterpolationFenchelSlope f g hs ht hims himt (hds' hims) (hdt' himt)

private theorem rankOneGradientDifference_integrable
    {P : Set E1} (hP : IsCompact P) (f g : RealConvexFunction E1)
    {K : ℝ} (hK : ∀ x, |g.val x - f.val x| ≤ K) (a : E1 → EReal) :
    IntegrableOn (fun m => g.val (conjugateGradient B a m) -
      f.val (conjugateGradient B a m)) P volume := by
  let : IsFiniteMeasure (volume.restrict P) := ⟨by simpa using hP.measure_lt_top⟩
  have hc : Measurable (fun x => g.val x - f.val x) :=
    ((continuousOn_univ.mp (g.property.continuousOn isOpen_univ)).sub
      (continuousOn_univ.mp (f.property.continuousOn isOpen_univ))).measurable
  exact Integrable.of_bound (hc.comp (measurable_conjugateGradient B a)).aestronglyMeasurable K
    (Eventually.of_forall (fun m => by simpa only [Real.norm_eq_abs] using hK (conjugateGradient B a m)))

private theorem rankOneGradientIntegral_eq
    {P : Set E1} (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (f g : RealConvexFunction E1) {a : E1 → ℝ}
    (ha : (fun x => (a x : EReal)) ∈ BoundedGrowthClass B P) :
    (∫ m in P, g.val (conjugateGradient B (fun x => (a x : EReal)) m) -
      f.val (conjugateGradient B (fun x => (a x : EReal)) m)) =
      ∫ x, (g.val x - f.val x) ∂alexandrovMeasure B volume (fun x => (a x : EReal)) := by
  have hc : Measurable (fun x => g.val x - f.val x) :=
    ((continuousOn_univ.mp (g.property.continuousOn isOpen_univ)).sub
      (continuousOn_univ.mp (f.property.continuousOn isOpen_univ))).measurable
  have he := integral_alexandrovMeasure_of_mem_fullMassClass (ν := volume) B hP hne hconv
    (mem_fullMassClass_of_mem_boundedGrowthClass B hP hne hconv ha) hc
  simpa only [finrank_euclideanSpace, Fintype.card_fin, Nat.factorial_one,
    Nat.cast_one, one_mul] using he.symm

private theorem rankOneIntegratedSlopeBounds
    {P : Set E1} (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (f g : RealConvexFunction E1)
    (hf : (fun x => (f.val x : EReal)) ∈ BoundedGrowthClass B P)
    (hg : (fun x => (g.val x : EReal)) ∈ BoundedGrowthClass B P)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    let C := fun r : ℝ =>
      ∫ x, (g.val x - f.val x)
        ∂alexandrovMeasure B volume (fun x => (rankOneInterpolation f g r x : EReal))
    (s - t) * C s ≤ rankOneLegendreDifferenceIntegral f g P s -
      rankOneLegendreDifferenceIntegral f g P t ∧
    rankOneLegendreDifferenceIntegral f g P s -
      rankOneLegendreDifferenceIntegral f g P t ≤ (s - t) * C t := by
  have hfs := rankOneInterpolation_boundedGrowth hP hne f g hf hg hs
  have hft := rankOneInterpolation_boundedGrowth hP hne f g hf hg ht
  obtain ⟨K, _hK, hKbound⟩ := rankOneDifferenceBound hf hg
  have his := rankOneGradientDifference_integrable hP f g hKbound
    (fun x => (rankOneInterpolation f g s x : EReal))
  have hit := rankOneGradientDifference_integrable hP f g hKbound
    (fun x => (rankOneInterpolation f g t x : EReal))
  have hid := (rankOneConjugate_integrable hP hconv hft).sub
    (rankOneConjugate_integrable hP hconv hfs)
  have hJ : rankOneLegendreDifferenceIntegral f g P s -
      rankOneLegendreDifferenceIntegral f g P t =
      ∫ m in P, (conjugate B (fun x => (rankOneInterpolation f g t x : EReal)) m).toReal -
        (conjugate B (fun x => (rankOneInterpolation f g s x : EReal)) m).toReal := by
    unfold rankOneLegendreDifferenceIntegral
    have he := (integral_sub
      ((rankOneConjugate_integrable hP hconv hf).sub (rankOneConjugate_integrable hP hconv hfs))
      ((rankOneConjugate_integrable hP hconv hf).sub (rankOneConjugate_integrable hP hconv hft))).symm
    simp only [Pi.sub_apply] at he
    rw [he]
    apply integral_congr_ae
    exact Eventually.of_forall (fun _ => by ring)
  have hae := rankOneInterpolationFenchelSlope_ae hP hne hconv f g hf hg hs ht
  have hl := integral_mono_ae (his.const_mul (s - t)) hid (hae.mono (fun _ h => h.1))
  have hu := integral_mono_ae hid (hit.const_mul (s - t)) (hae.mono (fun _ h => h.2))
  simp only [Pi.sub_apply] at hl hu
  rw [integral_const_mul, rankOneGradientIntegral_eq hP hne hconv f g hfs, ← hJ] at hl
  rw [integral_const_mul, rankOneGradientIntegral_eq hP hne hconv f g hft, ← hJ] at hu
  exact ⟨hl, hu⟩

private theorem rankOneLegendreDifferenceIntegral_hasDerivAt
    {P : Set E1} (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (f g : RealConvexFunction E1)
    (hf : (fun x => (f.val x : EReal)) ∈ BoundedGrowthClass B P)
    (hg : (fun x => (g.val x : EReal)) ∈ BoundedGrowthClass B P)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (rankOneLegendreDifferenceIntegral f g P)
      ((1 - t) * (∫ x, (g.val x - f.val x)
        ∂alexandrovMeasure B volume (fun x => (f.val x : EReal))) +
        t * (∫ x, (g.val x - f.val x)
          ∂alexandrovMeasure B volume (fun x => (g.val x : EReal)))) t := by
  let C : ℝ → ℝ := fun r =>
    (1 - r) * (∫ x, (g.val x - f.val x)
      ∂alexandrovMeasure B volume (fun x => (f.val x : EReal))) +
    r * (∫ x, (g.val x - f.val x)
      ∂alexandrovMeasure B volume (fun x => (g.val x : EReal)))
  have hc : Continuous C := by dsimp [C]; fun_prop
  have hnear : ∀ᶠ s in 𝓝 t, s ∈ Icc (0 : ℝ) 1 :=
    mem_of_superset (isOpen_Ioo.mem_nhds ht) Ioo_subset_Icc_self
  have hbounds (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      (s - t) * C s ≤ rankOneLegendreDifferenceIntegral f g P s -
        rankOneLegendreDifferenceIntegral f g P t ∧
      rankOneLegendreDifferenceIntegral f g P s -
        rankOneLegendreDifferenceIntegral f g P t ≤ (s - t) * C t := by
    have hh := rankOneIntegratedSlopeBounds hP hne hconv f g hf hg hs
      (Ioo_subset_Icc_self ht)
    dsimp only at hh
    rw [rankOneIntegralAffine hP hne hconv f g hf hg hs,
      rankOneIntegralAffine hP hne hconv f g hf hg (Ioo_subset_Icc_self ht)] at hh
    exact hh
  change HasDerivAt (rankOneLegendreDifferenceIntegral f g P) (C t) t
  apply hasDerivAt_iff_tendsto_slope_left_right.mpr
  constructor
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    · filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with s hs (hst : s < t)
      rw [slope_def_field]
      apply (le_div_iff_of_neg (sub_neg.mpr hst)).mpr
      simpa only [mul_comm] using (hbounds s hs).2
    · filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with s hs (hst : s < t)
      rw [slope_def_field]
      apply (div_le_iff_of_neg (sub_neg.mpr hst)).mpr
      simpa only [mul_comm] using (hbounds s hs).1
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) tendsto_const_nhds
    · filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with s hs (hst : t < s)
      rw [slope_def_field]
      apply (le_div_iff₀ (sub_pos.mpr hst)).mpr
      simpa only [mul_comm] using (hbounds s hs).1
    · filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with s hs (hst : t < s)
      rw [slope_def_field]
      apply (div_le_iff₀ (sub_pos.mpr hst)).mpr
      simpa only [mul_comm] using (hbounds s hs).2

/-- The rank-one endpoint formula follows from the SAME mixed-slot measures,
actual Fenchel gradients and ordinary real mean-value theorem. -/
theorem rankOneLegendreEndpointIntegral
    {P : Set E1} (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (f g : RealConvexFunction E1)
    (hf : (fun x => (f.val x : EReal)) ∈ BoundedGrowthClass B P)
    (hg : (fun x => (g.val x : EReal)) ∈ BoundedGrowthClass B P) :
    Integrable (fun x => g.val x - f.val x)
        (alexandrovMeasure B volume (fun x => (f.val x : EReal))) ∧
    Integrable (fun x => g.val x - f.val x)
        (alexandrovMeasure B volume (fun x => (g.val x : EReal))) ∧
    IntegrableOn (fun m => (conjugate B (fun x => (f.val x : EReal)) m).toReal -
        (conjugate B (fun x => (g.val x : EReal)) m).toReal) P volume ∧
    (∫ m in P, (conjugate B (fun x => (f.val x : EReal)) m).toReal -
        (conjugate B (fun x => (g.val x : EReal)) m).toReal) =
      (1 / 2 : ℝ) * ((∫ x, (g.val x - f.val x)
          ∂alexandrovMeasure B volume (fun x => (f.val x : EReal))) +
        (∫ x, (g.val x - f.val x)
          ∂alexandrovMeasure B volume (fun x => (g.val x : EReal)))) := by
  refine ⟨rankOneDifference_integrable hP hne hconv f g f hf hg hf,
    rankOneDifference_integrable hP hne hconv f g g hf hg hg,
    (rankOneConjugate_integrable hP hconv hf).sub (rankOneConjugate_integrable hP hconv hg), ?_⟩
  let I0 := ∫ x, (g.val x - f.val x)
    ∂alexandrovMeasure B volume (fun x => (f.val x : EReal))
  let I1 := ∫ x, (g.val x - f.val x)
    ∂alexandrovMeasure B volume (fun x => (g.val x : EReal))
  let Q : ℝ → ℝ := fun t => rankOneLegendreDifferenceIntegral f g P t -
    (t * I0 + (1 / 2 : ℝ) * (I1 - I0) * (t * t))
  have hc : ContinuousOn Q (Icc (0 : ℝ) 1) :=
    (rankOneLegendreDifferenceIntegral_continuous hP hne hconv f g hf hg).sub
      (by fun_prop)
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : HasDerivAt Q 0 t := by
    have hj := rankOneLegendreDifferenceIntegral_hasDerivAt hP hne hconv f g hf hg ht
    have hp := ((hasDerivAt_id t).mul_const I0).add
      (((hasDerivAt_id t).mul (hasDerivAt_id t)).const_mul ((1 / 2 : ℝ) * (I1 - I0)))
    have hp' : HasDerivAt
        (fun r : ℝ => r * I0 + (1 / 2 : ℝ) * (I1 - I0) * (r * r))
        (I0 + (1 / 2 : ℝ) * (I1 - I0) * (t + t)) t := by
      convert hp using 1 <;> first
      | rfl
      | simp only [id_eq, one_mul, mul_one]
    have hq := hj.sub hp'
    change HasDerivAt Q
      (((1 - t) * I0 + t * I1) -
        (I0 + (1 / 2 : ℝ) * (I1 - I0) * (t + t))) t at hq
    have hz : ((1 - t) * I0 + t * I1) -
        (I0 + (1 / 2 : ℝ) * (I1 - I0) * (t + t)) = 0 := by ring
    rw [hz] at hq
    exact hq
  obtain ⟨c, _hc, he⟩ := exists_hasDerivAt_eq_slope Q (fun _ => 0) zero_lt_one hc hd
  have hQ : Q 1 = Q 0 := by
    norm_num at he
    exact sub_eq_zero.mp he.symm
  have hzero : rankOneInterpolation f g 0 = f.val := by
    funext x
    simp [rankOneInterpolation]
  have hone : rankOneInterpolation f g 1 = g.val := by
    funext x
    simp [rankOneInterpolation]
  simp only [Q, rankOneLegendreDifferenceIntegral, hzero, hone, sub_self,
    zero_mul, one_mul, mul_zero, add_zero, integral_zero] at hQ
  dsimp [I0, I1] at hQ ⊢
  linarith

/-- The actual normalized truncations retain original source membership, poles,
and the whole literal Legendre supremum. No conjugate convergence is supplied. -/
theorem projectiveToricLegendre_truncation_iSup {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) (hu0 : u ≤ fun _ => (0 : EReal)) :
    let v : ℕ → P1 → EReal := fun j p => max (u p) (-((j : ℝ) : EReal))
    (∀ j, projectiveLineAtlas.IsThetaPSH projectiveFSForm (v j) ∧
      ProjectiveCircleInvariant (v j) ∧ IsBoundedPotential (v j)) ∧
    (∀ p, Antitone (fun j => v j p) ∧
      Tendsto (fun j => v j p) atTop (𝓝 (u p))) ∧
    (∀ m, Monotone (fun j => projectiveToricLegendre (v j) m)) ∧
    (∀ m, projectiveToricLegendre u m = ⨆ j : ℕ, projectiveToricLegendre (v j) m) := by
  let v : ℕ → P1 → EReal := fun j p => max (u p) (-((j : ℝ) : EReal))
  have hv (j : ℕ) : projectiveLineAtlas.IsThetaPSH projectiveFSForm (v j) := by
    have hc := isThetaPSH_projectiveZero.add_const (-(j : ℝ))
    have hh := hu.max hc
    simpa only [zero_add, EReal.coe_neg] using hh
  have hvi (j : ℕ) : ProjectiveCircleInvariant (v j) := by
    intro a ha p
    change max (u _) _ = max (u p) _
    rw [hi a ha p]
  have heq (j : ℕ) :
      v j = truncation (fun _ : P1 => (0 : EReal)) u j := by
    funext p
    simp only [v, truncation, zero_sub]
  have hb (j : ℕ) : IsBoundedPotential (v j) := by
    rw [heq]
    exact truncation_bounded ⟨0, 0, fun _ => ⟨le_rfl, le_rfl⟩⟩ hu0 j
  have hm (p : P1) : Antitone (fun j => v j p) := by
    simpa only [heq] using truncation_antitone (fun _ : P1 => (0 : EReal)) u p
  have ht (p : P1) : Tendsto (fun j => v j p) atTop (𝓝 (u p)) := by
    simpa only [heq] using
      tendsto_truncation (u := u) (φ := fun _ : P1 => (0 : EReal))
        ⟨0, 0, fun _ => ⟨le_rfl, le_rfl⟩⟩ p
  have hdesc (j : ℕ) (x : E1) :
      projectiveToricCorrectedDescent (v j) x =
        max (projectiveToricCorrectedDescent u x)
          (projectiveToricCorrectedDescent (fun _ : P1 => (0 : EReal)) x - (j : EReal)) := by
    change max (u _) (-((j : ℝ) : EReal)) + _ =
      max (u _ + _) ((0 : EReal) + _ - (j : EReal))
    rw [← max_add_add_right]
    congr 1
    simp only [zero_add, sub_eq_add_neg, add_comm, ← EReal.coe_natCast]
  have hcost (x m : E1) :
      (B x m : EReal) - projectiveToricCorrectedDescent u x =
        ⨆ j : ℕ, (B x m : EReal) - projectiveToricCorrectedDescent (v j) x := by
    obtain ⟨f, _hf, he⟩ := exists_real_convex_projectiveToricCorrectedDescent hu hi
    obtain ⟨f0, _hf0, he0⟩ := exists_real_convex_projectiveToricCorrectedDescent
      isThetaPSH_projectiveZero (fun _ _ _ => rfl)
    obtain ⟨j, hj⟩ := exists_nat_ge
      (f0 x - f x)
    have hjmax : projectiveToricCorrectedDescent (v j) x =
        projectiveToricCorrectedDescent u x := by
      rw [hdesc, he, he0, ← EReal.coe_natCast, ← EReal.coe_sub, max_eq_left]
      exact EReal.coe_le_coe_iff.mpr (by linarith)
    apply le_antisymm
    · rw [← hjmax]
      exact le_iSup (fun l : ℕ =>
        (B x m : EReal) - projectiveToricCorrectedDescent (v l) x) j
    · apply iSup_le
      intro l
      apply EReal.sub_le_sub le_rfl
      rw [hdesc]
      exact le_max_left _ _
  refine ⟨fun j => ⟨hv j, hvi j, hb j⟩, fun p => ⟨hm p, ht p⟩, ?_, ?_⟩
  · intro m i j hij
    exact (projectiveThetaPSH_le_iff_legendre (hv j) (hv i) (hvi j) (hvi i)).mp
      (fun p => hm p hij) m
  · intro m
    simp only [projectiveToricLegendre, conjugate]
    simp_rw [hcost]
    exact iSup_comm

private theorem projectiveFiniteEnergy_profile_coe {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    (fun x => (projectiveToricEuclideanProfile u x : EReal)) =
      projectiveToricCorrectedDescent u := by
  obtain ⟨f, _hf, he⟩ := exists_real_convex_projectiveToricCorrectedDescent hu hi
  funext x
  simp only [projectiveToricEuclideanProfile, he, EReal.toReal_coe]

private theorem projectiveFiniteEnergy_chartDifference {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) {z : ComplexModel 1}
    (hz : z ∈ tropicalSmoothDomain 1) :
    canonicalERealDiffToReal (u ((projectiveNativeChart false).val.symm z)) 0 =
      projectiveToricEuclideanProfile u (tropicalization z) -
        projectiveToricEuclideanProfile (fun _ : P1 => (0 : EReal)) (tropicalization z) := by
  have hc := projectiveToricEuclideanProfile_corrected hu hi hz
  change u ((projectiveNativeChart false).val.symm z) + (projectiveFSPotential z : EReal) =
    (projectiveToricEuclideanProfile u (tropicalization z) : EReal) at hc
  have huval : u ((projectiveNativeChart false).val.symm z) =
      ((projectiveToricEuclideanProfile u (tropicalization z) -
        projectiveFSPotential z : ℝ) : EReal) := by
    calc
      _ = (u ((projectiveNativeChart false).val.symm z) +
          (projectiveFSPotential z : EReal)) + ((-projectiveFSPotential z : ℝ) : EReal) :=
        (MeteredDivisorPositivity.add_coe_add_neg_coe _ _).symm
      _ = _ := by rw [hc, ← EReal.coe_add]; rfl
  have hi0 : ProjectiveCircleInvariant (fun _ : P1 => (0 : EReal)) := fun _ _ _ => rfl
  have h0 := projectiveToricEuclideanProfile_corrected isThetaPSH_projectiveZero hi0 hz
  change (0 : EReal) + (projectiveFSPotential z : EReal) =
    (projectiveToricEuclideanProfile (fun _ : P1 => (0 : EReal))
      (tropicalization z) : EReal) at h0
  have hρ : projectiveFSPotential z =
      projectiveToricEuclideanProfile (fun _ : P1 => (0 : EReal)) (tropicalization z) :=
    EReal.coe_injective (by simpa only [zero_add] using h0)
  rw [huval]
  change canonicalERealDiffToReal
    ((projectiveToricEuclideanProfile u (tropicalization z) -
      projectiveFSPotential z : ℝ) : EReal) ((0 : ℝ) : EReal) = _
  rw [canonicalERealDiffToReal_coe_coe, sub_zero, hρ]

private theorem projectiveFiniteEnergy_signedEndpoint {u w : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u)
    (hw : projectiveLineAtlas.IsThetaPSH projectiveFSForm w)
    (hiw : ProjectiveCircleInvariant w) :
    (∫ p, canonicalERealDiffToReal (u p) 0 ∂projectiveToricNonPluripolarMeasure hw) =
      ∫ x, (projectiveToricEuclideanProfile u x -
        projectiveToricEuclideanProfile (fun _ : P1 => (0 : EReal)) x)
        ∂alexandrovMeasure B volume (fun x => (projectiveToricEuclideanProfile w x : EReal)) := by
  let μ := tropicalCanonicalBTMeasure (projectiveToricEuclideanProfile_convex hw hiw)
  let P := tropicalPotentialPatch (projectiveNativeChart false) projectiveTropicalLocalPotential
    (projectiveToricEuclideanProfile_convex hw hiw)
    (projectiveToricEuclideanProfile_corrected hw hiw)
  have hnull : μ (tropicalSmoothDomain 1 : Set (ComplexModel 1))ᶜ = 0 :=
    MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure_compl _ _ _
  have hmem : ∀ᵐ z ∂μ, z ∈ tropicalSmoothDomain 1 := ae_iff.mpr hnull
  have hi0 : ProjectiveCircleInvariant (fun _ : P1 => (0 : EReal)) := fun _ _ _ => rfl
  have hcont : Continuous (fun x => projectiveToricEuclideanProfile u x -
      projectiveToricEuclideanProfile (fun _ : P1 => (0 : EReal)) x) :=
    (continuousOn_univ.mp ((projectiveToricEuclideanProfile_convex hu hi).continuousOn
      isOpen_univ)).sub
      (continuousOn_univ.mp ((projectiveToricEuclideanProfile_convex
        isThetaPSH_projectiveZero hi0).continuousOn isOpen_univ))
  obtain ⟨hT, _⟩ := exists_compact_tropical_torus_lift (n := 1) isCompact_empty
  rw [projectiveToricNonPluripolarMeasure_eq_tropicalCanonical hw hiw]
  calc
    _ = ∫ z, canonicalERealDiffToReal (u ((projectiveNativeChart false).val.symm z)) 0 ∂μ :=
      P.integral_pushMeasure hnull _
    _ = ∫ z, (projectiveToricEuclideanProfile u (tropicalization z) -
        projectiveToricEuclideanProfile (fun _ : P1 => (0 : EReal)) (tropicalization z)) ∂μ :=
      integral_congr_ae (hmem.mono (fun z hz => projectiveFiniteEnergy_chartDifference hu hi hz))
    _ = _ := by
      rw [← tropicalization_canonicalBTMeasure_eq_alexandrov
        (projectiveToricEuclideanProfile_convex hw hiw)]
      exact (integral_map hT.aemeasurable hcont.aestronglyMeasurable).symm

private theorem projectiveFiniteEnergy_endpointMeasure_zero {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u) :
    RelativeEnergy.endpointMixedMeasure projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) u
      isModelPotential_projectiveNativeZero.plurisubharmonic
      (isThetaPshPotential_projectiveNativeFS_of_source hu) (0 : Fin 2) =
        projectiveToricNonPluripolarMeasure isThetaPSH_projectiveZero := by
  unfold RelativeEnergy.endpointMixedMeasure projectiveToricNonPluripolarMeasure
    DiagonalMass.diagonalPotentialMeasure
  refine GlobalDiagonalScaling.globalMixedMeasure_congr rfl ?_ _ _
  funext i p
  simp only [RelativeEnergy.endpointMixedPotential, Fin.val_zero, not_lt_zero, if_false]

private theorem projectiveFiniteEnergy_endpointMeasure_one {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u) :
    RelativeEnergy.endpointMixedMeasure projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) u
      isModelPotential_projectiveNativeZero.plurisubharmonic
      (isThetaPshPotential_projectiveNativeFS_of_source hu) (1 : Fin 2) =
        projectiveToricNonPluripolarMeasure hu := by
  unfold RelativeEnergy.endpointMixedMeasure projectiveToricNonPluripolarMeasure
    DiagonalMass.diagonalPotentialMeasure
  refine GlobalDiagonalScaling.globalMixedMeasure_congr rfl ?_ _ _
  funext i p
  have hi : i = (0 : Fin 1) := Fin.eq_zero i
  subst i
  simp only [RelativeEnergy.endpointMixedPotential, Fin.val_zero, Fin.val_one,
    Nat.zero_lt_one, if_true]

/-- The actual original native bounded energy is the SAME endpoint Legendre
integral; both endpoint measures are transported by the existing true mothers. -/
theorem projectiveToricEnergyOfMinimalType_eq_legendreIntegral {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u)
    (hb : RelativeEInfinity projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) u) :
    RelativeEnergy.relativeEnergyOfMinimalType projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) u
      isModelPotential_projectiveNativeZero.plurisubharmonic
      (isThetaPshPotential_projectiveNativeFS_of_source hu) =
      ∫ m in projectiveMomentInterval,
        (projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m).toReal -
          (projectiveToricLegendre u m).toReal := by
  have hi0 : ProjectiveCircleInvariant (fun _ : P1 => (0 : EReal)) := fun _ _ _ => rfl
  let f : RealConvexFunction E1 :=
    ⟨projectiveToricEuclideanProfile (fun _ : P1 => (0 : EReal)),
      projectiveToricEuclideanProfile_convex isThetaPSH_projectiveZero hi0⟩
  let g : RealConvexFunction E1 :=
    ⟨projectiveToricEuclideanProfile u, projectiveToricEuclideanProfile_convex hu hi⟩
  have he0 := projectiveFiniteEnergy_profile_coe isThetaPSH_projectiveZero hi0
  have heu := projectiveFiniteEnergy_profile_coe hu hi
  have hf : (fun x => (f.val x : EReal)) ∈ BoundedGrowthClass B projectiveMomentInterval := by
    change (fun x => (projectiveToricEuclideanProfile (fun _ : P1 => (0 : EReal)) x : EReal)) ∈ _
    rw [he0]
    exact (projectiveToric_mem_relativeEInfinity_iff_boundedGrowthClass
      isThetaPSH_projectiveZero hi0).mp
      ⟨isModelPotential_projectiveNativeZero.plurisubharmonic,
        SameSingularityTypeOn.refl _ _⟩
  have hg : (fun x => (g.val x : EReal)) ∈ BoundedGrowthClass B projectiveMomentInterval := by
    change (fun x => (projectiveToricEuclideanProfile u x : EReal)) ∈ _
    rw [heu]
    exact (projectiveToric_mem_relativeEInfinity_iff_boundedGrowthClass hu hi).mp hb
  obtain ⟨_hint0, _hintu, _hintG, he⟩ := rankOneLegendreEndpointIntegral
    isCompact_projectiveMomentInterval nonempty_projectiveMomentInterval
    convex_projectiveMomentInterval f g hf hg
  have hE : RelativeEnergy.relativeEnergyOfMinimalType projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) u
      isModelPotential_projectiveNativeZero.plurisubharmonic
      (isThetaPshPotential_projectiveNativeFS_of_source hu) =
      (1 / 2 : ℝ) * ((∫ x, g.val x - f.val x
        ∂alexandrovMeasure B volume (fun x => (f.val x : EReal))) +
        (∫ x, g.val x - f.val x
          ∂alexandrovMeasure B volume (fun x => (g.val x : EReal)))) := by
    unfold RelativeEnergy.relativeEnergyOfMinimalType
    rw [Fin.sum_univ_two]
    unfold RelativeEnergy.relativeEnergyTerm
    rw [projectiveFiniteEnergy_endpointMeasure_zero hu,
      projectiveFiniteEnergy_endpointMeasure_one hu,
      projectiveFiniteEnergy_signedEndpoint hu hi isThetaPSH_projectiveZero hi0,
      projectiveFiniteEnergy_signedEndpoint hu hi hu hi]
    dsimp [f, g]
    ring
  rw [hE, ← he]
  change (∫ m in projectiveMomentInterval,
      (conjugate B (fun x => (projectiveToricEuclideanProfile
        (fun _ : P1 => (0 : EReal)) x : EReal)) m).toReal -
      (conjugate B (fun x => (projectiveToricEuclideanProfile u x : EReal)) m).toReal) = _
  rw [he0, heu]
  rfl

private theorem projectiveFiniteEnergy_legendre_finite {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u)
    (hb : RelativeEInfinity projectiveNativeFSBackground.form (fun _ : P1 => (0 : EReal)) u)
    {m : E1} (hm : m ∈ projectiveMomentInterval) :
    ((projectiveToricLegendre u m).toReal : EReal) = projectiveToricLegendre u m := by
  have hf := (projectiveToric_mem_relativeEInfinity_iff_boundedGrowthClass hu hi).mp hb
  obtain ⟨a, b, hab⟩ := conjugate_bounds_of_mem_boundedGrowthClass B
    isCompact_projectiveMomentInterval convex_projectiveMomentInterval hf
  exact EReal.coe_toReal
    (ne_top_of_le_ne_top (EReal.coe_ne_top b) (hab m hm).2)
    (ne_bot_of_le_ne_bot (EReal.coe_ne_bot a) (hab m hm).1)

private theorem projectiveFiniteEnergy_legendre_integrable {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u)
    (hb : RelativeEInfinity projectiveNativeFSBackground.form (fun _ : P1 => (0 : EReal)) u) :
    IntegrableOn (fun m => (projectiveToricLegendre u m).toReal)
      projectiveMomentInterval volume := by
  have hf := (projectiveToric_mem_relativeEInfinity_iff_boundedGrowthClass hu hi).mp hb
  obtain ⟨a, b, hab⟩ := conjugate_bounds_of_mem_boundedGrowthClass B
    isCompact_projectiveMomentInterval convex_projectiveMomentInterval hf
  apply IntegrableOn.of_bound isCompact_projectiveMomentInterval.measure_lt_top
    (measurable_conjugate B (projectiveToricCorrectedDescent u)).ereal_toReal.aestronglyMeasurable
    (|a| + |b|)
  filter_upwards [ae_restrict_mem isCompact_projectiveMomentInterval.measurableSet] with m hm
  have hh := hab m hm
  change (a : EReal) ≤ projectiveToricLegendre u m ∧
    projectiveToricLegendre u m ≤ (b : EReal) at hh
  rw [← projectiveFiniteEnergy_legendre_finite hu hi hb hm] at hh
  simp only [EReal.coe_le_coe_iff] at hh
  rw [Real.norm_eq_abs]
  change |(projectiveToricLegendre u m).toReal| ≤ |a| + |b|
  apply abs_le.mpr
  constructor <;> linarith [le_abs_self a, le_abs_self b, neg_le_abs a, abs_nonneg a,
    abs_nonneg b]

private theorem projectiveFiniteEnergy_iSup_nonnegative (a : ℕ → EReal)
    (ha : ∀ j, 0 ≤ a j) :
    (⨆ j, a j).toENNReal = ⨆ j, (a j).toENNReal := by
  apply le_antisymm
  · have h : (⨆ j, a j) ≤ ((⨆ j, (a j).toENNReal : ℝ≥0∞) : EReal) := by
      apply iSup_le
      intro j
      rw [← EReal.coe_toENNReal (ha j)]
      exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr
        (le_iSup (fun k => (a k).toENNReal) j)
    simpa only [EReal.toENNReal_coe] using EReal.toENNReal_le_toENNReal h
  · exact iSup_le fun j => EReal.toENNReal_le_toENNReal (le_iSup a j)

private theorem projectiveFiniteEnergy_coe_iSup (a : ℕ → ℝ≥0∞) :
    (((⨆ j, a j) : ℝ≥0∞) : EReal) = ⨆ j, (a j : EReal) := by
  apply le_antisymm
  · have h := iSup_le fun j => EReal.toENNReal_le_toENNReal
      (le_iSup (fun k => (a k : EReal)) j)
    simp only [EReal.toENNReal_coe] at h
    have h0 : (0 : EReal) ≤ ⨆ j, (a j : EReal) :=
      (EReal.coe_ennreal_nonneg (a 0)).trans (le_iSup (fun k => (a k : EReal)) 0)
    simpa only [EReal.coe_toENNReal h0] using
      EReal.coe_ennreal_le_coe_ennreal_iff.mpr h
  · exact iSup_le fun j => EReal.coe_ennreal_le_coe_ennreal_iff.mpr (le_iSup a j)

private theorem projectiveFiniteEnergy_normalized {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) (hu0 : u ≤ fun _ => (0 : EReal)) :
    RelativeDarvasDistance.energy projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) isModelPotential_projectiveNativeZero u =
      extendedSignedIntegral (volume.restrict projectiveMomentInterval)
        (fun m => projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m -
          projectiveToricLegendre u m) := by
  let v : ℕ → P1 → EReal := fun j p => max (u p) (-((j : ℝ) : EReal))
  obtain ⟨hv, _hpt, hmono, hsup⟩ := projectiveToricLegendre_truncation_iSup hu hi hu0
  have hi0 : ProjectiveCircleInvariant (fun _ : P1 => (0 : EReal)) := fun _ _ _ => rfl
  have hb0 : RelativeEInfinity projectiveNativeFSBackground.form (fun _ : P1 => (0 : EReal))
      (fun _ => (0 : EReal)) :=
    ⟨isModelPotential_projectiveNativeZero.plurisubharmonic, SameSingularityTypeOn.refl _ _⟩
  have h0b : IsBoundedPotential (fun _ : P1 => (0 : EReal)) :=
    ⟨0, 0, fun _ => ⟨le_rfl, le_rfl⟩⟩
  have hb (j : ℕ) : RelativeEInfinity projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) (v j) :=
    ⟨isThetaPshPotential_projectiveNativeFS_of_source (hv j).1,
      BoundedMongeAmpereEnergy.sameSingularityType_of_bounded (hv j).2.2 h0b⟩
  let a (j : ℕ) (m : E1) :=
    (projectiveToricLegendre (v j) m -
      projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m).toENNReal
  have horder (j : ℕ) : projectiveToricLegendre (fun _ : P1 => (0 : EReal)) ≤
      projectiveToricLegendre (v j) :=
    (projectiveThetaPSH_le_iff_legendre (hv j).1 isThetaPSH_projectiveZero (hv j).2.1 hi0).mp
      (fun p => max_le (hu0 p) (by simp))
  have hnonneg (j : ℕ) (m : E1) (hm : m ∈ projectiveMomentInterval) :
      0 ≤ projectiveToricLegendre (v j) m -
      projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m :=
    (EReal.sub_nonneg
      (Or.inr (by rw [← projectiveFiniteEnergy_legendre_finite
        isThetaPSH_projectiveZero hi0 hb0 hm]; exact EReal.coe_ne_top _))
      (Or.inr (by rw [← projectiveFiniteEnergy_legendre_finite
        isThetaPSH_projectiveZero hi0 hb0 hm]; exact EReal.coe_ne_bot _))).mpr (horder j m)
  have haj (j : ℕ) : (∫⁻ m in projectiveMomentInterval, a j m ∂volume) =
      ENNReal.ofReal (∫ m in projectiveMomentInterval,
        (projectiveToricLegendre (v j) m).toReal -
          (projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m).toReal) := by
    have hI := (projectiveFiniteEnergy_legendre_integrable (hv j).1 (hv j).2.1 (hb j)).sub
      (projectiveFiniteEnergy_legendre_integrable isThetaPSH_projectiveZero hi0 hb0)
    change Integrable (fun m => (projectiveToricLegendre (v j) m).toReal -
      (projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m).toReal)
      (volume.restrict projectiveMomentInterval) at hI
    have hp : 0 ≤ᵐ[volume.restrict projectiveMomentInterval] (fun m =>
        (projectiveToricLegendre (v j) m).toReal -
          (projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m).toReal) := by
      filter_upwards [ae_restrict_mem isCompact_projectiveMomentInterval.measurableSet] with m hm
      have hh := horder j m
      rw [← projectiveFiniteEnergy_legendre_finite (hv j).1 (hv j).2.1 (hb j) hm,
        ← projectiveFiniteEnergy_legendre_finite isThetaPSH_projectiveZero hi0 hb0 hm] at hh
      exact sub_nonneg.mpr (EReal.coe_le_coe_iff.mp hh)
    rw [ofReal_integral_eq_lintegral_ofReal hI hp]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem isCompact_projectiveMomentInterval.measurableSet] with m hm
    dsimp [a]
    rw [← projectiveFiniteEnergy_legendre_finite (hv j).1 (hv j).2.1 (hb j) hm,
      ← projectiveFiniteEnergy_legendre_finite isThetaPSH_projectiveZero hi0 hb0 hm,
      ← EReal.coe_sub, EReal.real_coe_toENNReal, EReal.toReal_coe, EReal.toReal_coe]
  have henergy (j : ℕ) :
      (RelativeEnergy.relativeEnergyOfMinimalType projectiveNativeFSBackground.form
        (fun _ : P1 => (0 : EReal)) (v j) isModelPotential_projectiveNativeZero.plurisubharmonic
        (isThetaPshPotential_projectiveNativeFS_of_source (hv j).1) : EReal) =
      -((∫⁻ m in projectiveMomentInterval, a j m ∂volume) : EReal) := by
    rw [projectiveToricEnergyOfMinimalType_eq_legendreIntegral (hv j).1 (hv j).2.1 (hb j), haj]
    have hp : 0 ≤ ∫ m in projectiveMomentInterval,
        (projectiveToricLegendre (v j) m).toReal -
          (projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m).toReal := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem isCompact_projectiveMomentInterval.measurableSet] with m hm
      have hh := horder j m
      rw [← projectiveFiniteEnergy_legendre_finite (hv j).1 (hv j).2.1 (hb j) hm,
        ← projectiveFiniteEnergy_legendre_finite isThetaPSH_projectiveZero hi0 hb0 hm] at hh
      exact sub_nonneg.mpr (EReal.coe_le_coe_iff.mp hh)
    rw [EReal.coe_ennreal_ofReal, max_eq_left hp, ← EReal.coe_neg, ← integral_neg]
    congr 2
    funext m
    ring
  have hrel : RelativePSH projectiveNativeFSBackground.form (fun _ : P1 => (0 : EReal)) u :=
    ⟨isThetaPshPotential_projectiveNativeFS_of_source hu, hu0⟩
  rw [RelativeDarvasDistance.energy_eq hrel,
    relativeMongeAmpereEnergy_eq_iInf_truncation projectiveNativeFSBackground
      projectiveNativeFSBackground.form isModelPotential_projectiveNativeZero hrel h0b]
  have heq (j : ℕ) : truncation (fun _ : P1 => (0 : EReal)) u j = v j := by
    funext p
    simp only [truncation, v, zero_sub]
  simp_rw [heq, henergy]
  have hneg := EReal.negOrderIso.map_iSup
    (fun j : ℕ => ((∫⁻ m in projectiveMomentInterval, a j m ∂volume) : EReal))
  change - (⨆ j, ((∫⁻ m in projectiveMomentInterval, a j m ∂volume) : EReal)) =
    ⨅ j, -((∫⁻ m in projectiveMomentInterval, a j m ∂volume) : EReal) at hneg
  rw [← hneg, ← projectiveFiniteEnergy_coe_iSup]
  have ha : ∀ j, Measurable (a j) := fun j =>
    ((measurable_conjugate B (projectiveToricCorrectedDescent (v j))).sub
      (measurable_conjugate B (projectiveToricCorrectedDescent (fun _ : P1 => (0 : EReal))))).ereal_toENNReal
  rw [← lintegral_iSup ha (fun i j hij m =>
    EReal.toENNReal_le_toENNReal (EReal.sub_le_sub (hmono m hij) le_rfl))]
  have hgap : ∀ m ∈ projectiveMomentInterval,
      (⨆ j, a j m) = (projectiveToricLegendre u m -
        projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m).toENNReal := by
    intro m hm
    rw [← projectiveFiniteEnergy_iSup_nonnegative _ (fun j => hnonneg j m hm)]
    rw [← projectiveFiniteEnergy_legendre_finite isThetaPSH_projectiveZero hi0 hb0 hm]
    simp_rw [sub_eq_add_neg, ← EReal.coe_neg]
    rw [iSup_add_coe, ← hsup]
  have htotal := lintegral_congr_ae (μ := volume.restrict projectiveMomentInterval)
    ((ae_restrict_mem isCompact_projectiveMomentInterval.measurableSet).mono
      (fun m hm => hgap m hm))
  rw [htotal]
  unfold extendedSignedIntegral
  have hpzero : (∫⁻ m in projectiveMomentInterval,
      (projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m -
        projectiveToricLegendre u m).toENNReal ∂volume) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [] with m
    apply EReal.toENNReal_of_nonpos
    exact EReal.sub_nonpos.mpr
      ((projectiveThetaPSH_le_iff_legendre hu isThetaPSH_projectiveZero hi hi0).mp hu0 m)
  rw [hpzero, EReal.coe_ennreal_zero, zero_sub]
  congr 2
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem isCompact_projectiveMomentInterval.measurableSet] with m hm
  have hf := projectiveFiniteEnergy_legendre_finite isThetaPSH_projectiveZero hi0 hb0 hm
  rw [← hf, EReal.neg_sub (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)),
    sub_eq_add_neg, add_comm]

private theorem projectiveFiniteEnergy_signed_bound {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsFiniteMeasure μ] (g : A → EReal) (hg : Measurable g)
    (C : ℝ) (hupper : g ≤ᵐ[μ] fun _ => (C : EReal)) :
    extendedSignedIntegral μ g = ((C * μ.real univ : ℝ) : EReal) -
      ((∫⁻ x, ((C : EReal) - g x).toENNReal ∂μ) : EReal) := by
  have hp : (∫⁻ x, (g x).toENNReal ∂μ) < ⊤ := by
    apply lt_of_le_of_lt (lintegral_mono_ae
      (hupper.mono fun _ hx => EReal.toENNReal_le_toENNReal hx))
    rw [lintegral_const, EReal.real_coe_toENNReal]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ univ)
  by_cases hn : (∫⁻ x, (-g x).toENNReal ∂μ) < ⊤
  · have hfin : ∀ᵐ x ∂μ, g x ≠ ⊤ ∧ g x ≠ ⊥ := by
      filter_upwards [hupper, ae_lt_top hg.neg.ereal_toENNReal hn.ne] with x hx hxn
      refine ⟨ne_top_of_le_ne_top (EReal.coe_ne_top C) hx, ?_⟩
      intro hb
      have he : (-g x).toENNReal = ⊤ := by rw [hb]; rfl
      exact hxn.ne he
    have hreal : g =ᵐ[μ] fun x => ((g x).toReal : EReal) :=
      hfin.mono fun x hx => (EReal.coe_toReal hx.1 hx.2).symm
    have hrealupper : (fun x => (g x).toReal) ≤ᵐ[μ] fun _ => C := by
      filter_upwards [hupper, hreal] with x hx he
      rw [he] at hx
      exact EReal.coe_le_coe_iff.mp hx
    have hmother := SGPT.Okounkov.signedIntegral_eq_bound_sub_gap μ
      (fun x => (g x).toReal) hg.ereal_toReal C hrealupper
    calc
      extendedSignedIntegral μ g =
          extendedSignedIntegral μ (fun x => ((g x).toReal : EReal)) := by
        unfold extendedSignedIntegral
        congr 1 <;> apply congrArg (fun t : ℝ≥0∞ => (t : EReal)) <;>
          apply lintegral_congr_ae <;> filter_upwards [hreal] with x hx <;>
          rw [hx] <;> simp only [EReal.toReal_coe]
      _ = _ := by
        rw [hmother]
        congr 2
        apply lintegral_congr_ae
        filter_upwards [hreal] with x hx
        rw [hx, ← EReal.coe_sub, EReal.real_coe_toENNReal, EReal.toReal_coe]
  · have hnTop : (∫⁻ x, (-g x).toENNReal ∂μ) = ⊤ := top_unique (not_lt.mp hn)
    have hgapTop : (∫⁻ x, ((C : EReal) - g x).toENNReal ∂μ) = ⊤ := by
      apply top_unique
      apply not_lt.mp
      rw [SGPT.Okounkov.lintegral_heightGap_lt_top_iff]
      exact hn
    rw [extendedSignedIntegral, hnTop, hgapTop, ← EReal.coe_ennreal_toReal hp.ne]
    simp

private theorem projectiveFiniteEnergy_zero_modelVolume :
    RelativePreceqClasses.modelVolume projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) isModelPotential_projectiveNativeZero = 1 := by
  unfold RelativePreceqClasses.modelVolume
  change (projectiveToricNonPluripolarMeasure isThetaPSH_projectiveZero).real univ = 1
  rw [measureReal_def, projectiveToricNonPluripolarMeasure_zero_univ]
  norm_num

private theorem projectiveFiniteEnergy_moment_volume : volume projectiveMomentInterval = 1 := by
  have hi0 : ProjectiveCircleInvariant (fun _ : P1 => (0 : EReal)) := fun _ _ _ => rfl
  have h := projectiveToricNonPluripolarMeasure_univ_eq_newtonLength
    isThetaPSH_projectiveZero hi0
  rw [projectiveToricNonPluripolarMeasure_zero_univ, projectiveToricNewtonBody_zero] at h
  exact h.symm

private theorem projectiveFiniteEnergy_gap_shift (r C : ℝ) (a : EReal) :
    (C : EReal) - ((r : EReal) - a) =
      -((r : EReal) - (a - ((-C : ℝ) : EReal))) := by
  cases a using EReal.rec <;> simp [← EReal.coe_sub]
  congr 1
  ring

/-- The unnormalized original native energy equals the actual extended signed
Legendre integral. The compact source upper bound is produced internally. -/
theorem projectiveToricEnergy_eq_extendedLegendreIntegral {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    RelativeDarvasDistance.energy projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) isModelPotential_projectiveNativeZero u =
      extendedSignedIntegral (volume.restrict projectiveMomentInterval)
        (fun m => projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m -
          projectiveToricLegendre u m) := by
  let : IsFiniteMeasure (volume.restrict projectiveMomentInterval) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_projectiveMomentInterval.measure_lt_top⟩
  obtain ⟨C, hC⟩ := exists_upper_bound_projectiveThetaPSH hu
  let v : P1 → EReal := fun p => u p + ((-C : ℝ) : EReal)
  have hv : projectiveLineAtlas.IsThetaPSH projectiveFSForm v := hu.add_const (-C)
  have hvi : ProjectiveCircleInvariant v := by
    intro a ha p
    change u _ + _ = u p + _
    rw [hi a ha p]
  have hv0 : v ≤ fun _ => (0 : EReal) := by
    intro p
    change u p + ((-C : ℝ) : EReal) ≤ 0
    have hh := add_le_add (hC p) (le_rfl : ((-C : ℝ) : EReal) ≤ _)
    simpa only [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] using hh
  have hi0 : ProjectiveCircleInvariant (fun _ : P1 => (0 : EReal)) := fun _ _ _ => rfl
  have hb0 : RelativeEInfinity projectiveNativeFSBackground.form (fun _ : P1 => (0 : EReal))
      (fun _ => (0 : EReal)) :=
    ⟨isModelPotential_projectiveNativeZero.plurisubharmonic, SameSingularityTypeOn.refl _ _⟩
  have h0b : IsBoundedPotential (fun _ : P1 => (0 : EReal)) :=
    ⟨0, 0, fun _ => ⟨le_rfl, le_rfl⟩⟩
  have hGv : projectiveToricLegendre v =
      fun m => projectiveToricLegendre u m - ((-C : ℝ) : EReal) :=
    projectiveToricLegendre_add_const u (-C)
  have hconst := isThetaPSH_projectiveZero.add_const C
  have hconsti : ProjectiveCircleInvariant (fun _ : P1 => (0 : EReal) + (C : EReal)) :=
    fun _ _ _ => rfl
  have horder := (projectiveThetaPSH_le_iff_legendre hu hconst hi hconsti).mp
    (fun p => by simpa only [zero_add] using hC p)
  let g (m : E1) := projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m -
    projectiveToricLegendre u m
  have hg : Measurable g :=
    (measurable_conjugate B (projectiveToricCorrectedDescent (fun _ : P1 => (0 : EReal)))).sub
      (measurable_conjugate B (projectiveToricCorrectedDescent u))
  have hupper : g ≤ᵐ[volume.restrict projectiveMomentInterval] fun _ => (C : EReal) := by
    filter_upwards [ae_restrict_mem isCompact_projectiveMomentInterval.measurableSet] with m hm
    have hh := horder m
    rw [projectiveToricLegendre_add_const] at hh
    change projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m -
      (C : EReal) ≤ projectiveToricLegendre u m at hh
    change projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m -
      projectiveToricLegendre u m ≤ (C : EReal)
    rw [← projectiveFiniteEnergy_legendre_finite isThetaPSH_projectiveZero hi0 hb0 hm] at hh ⊢
    exact (real_sub_le_iff_comm _ _ _).mpr hh
  have hgap : (fun m => ((C : EReal) - g m).toENNReal) =ᵐ[
      volume.restrict projectiveMomentInterval] (fun m =>
      (-(projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m -
        projectiveToricLegendre v m)).toENNReal) := by
    filter_upwards [ae_restrict_mem isCompact_projectiveMomentInterval.measurableSet] with m hm
    dsimp [g]
    rw [hGv, ← projectiveFiniteEnergy_legendre_finite isThetaPSH_projectiveZero hi0 hb0 hm,
      projectiveFiniteEnergy_gap_shift]
  have hvenergy := projectiveFiniteEnergy_normalized hv hvi hv0
  have hnpos : (∫⁻ m in projectiveMomentInterval,
      (projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m -
        projectiveToricLegendre v m).toENNReal ∂volume) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    exact Eventually.of_forall fun m => EReal.toENNReal_of_nonpos
      (EReal.sub_nonpos.mpr
        ((projectiveThetaPSH_le_iff_legendre hv isThetaPSH_projectiveZero hvi hi0).mp hv0 m))
  rw [extendedSignedIntegral, hnpos, EReal.coe_ennreal_zero, zero_sub] at hvenergy
  have hE := RelativePreceqClasses.energy_add_const
    (hφ := isModelPotential_projectiveNativeZero) projectiveNativeFSBackground h0b v C
  have heuv : (fun p => v p + (C : EReal)) = u := by
    funext p
    simpa only [neg_neg] using RelativePreceqClasses.add_coe_add_coe_neg (u p) (-C)
  rw [heuv, projectiveFiniteEnergy_zero_modelVolume, mul_one, hvenergy] at hE
  rw [hE, projectiveFiniteEnergy_signed_bound (volume.restrict projectiveMomentInterval) g hg C hupper]
  have hvol : (volume.restrict projectiveMomentInterval).real univ = 1 := by
    rw [measureReal_def, Measure.restrict_apply_univ, projectiveFiniteEnergy_moment_volume]
    norm_num
  rw [hvol, mul_one, lintegral_congr_ae hgap, sub_eq_add_neg, add_comm]

private theorem projectiveFiniteEnergy_shift_positive (a : ℝ) (g : E1 → EReal) :
    (∫⁻ m in projectiveMomentInterval, (g m - (a : EReal)).toENNReal ∂volume) < ⊤ ↔
      (∫⁻ m in projectiveMomentInterval, (g m).toENNReal ∂volume) < ⊤ := by
  let : IsFiniteMeasure (volume.restrict projectiveMomentInterval) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_projectiveMomentInterval.measure_lt_top⟩
  have h := SGPT.Okounkov.lintegral_heightGap_lt_top_iff
    (volume.restrict projectiveMomentInterval) (fun m => -g m) (-a)
  simpa only [sub_eq_add_neg, neg_neg, EReal.coe_neg, add_comm] using h

private theorem projectiveFiniteEnergy_energy_positive_iff {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    ⊥ < RelativeDarvasDistance.energy projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) isModelPotential_projectiveNativeZero u ↔
      (∫⁻ m in projectiveMomentInterval, (projectiveToricLegendre u m).toENNReal ∂volume) < ⊤ := by
  have hi0 : ProjectiveCircleInvariant (fun _ : P1 => (0 : EReal)) := fun _ _ _ => rfl
  have hf0 := (projectiveToric_mem_relativeEInfinity_iff_boundedGrowthClass
    isThetaPSH_projectiveZero hi0).mp
    ⟨isModelPotential_projectiveNativeZero.plurisubharmonic, SameSingularityTypeOn.refl _ _⟩
  obtain ⟨a, b, hab⟩ := conjugate_bounds_of_mem_boundedGrowthClass B
    isCompact_projectiveMomentInterval convex_projectiveMomentInterval hf0
  have hf := projectiveToricCorrectedDescent_mem_growthClass hu hi
  have hzero : (0 : E1) ∈ effectiveDomain (projectiveToricCorrectedDescent u) := by
    rw [effectiveDomain_eq_univ_of_mem_growthClass B isCompact_projectiveMomentInterval
      nonempty_projectiveMomentInterval hf]
    exact mem_univ _
  let L : ℝ := -(projectiveToricCorrectedDescent u 0).toReal
  have hL (m : E1) : (L : EReal) ≤ projectiveToricLegendre u m :=
    coe_lower_bound_conjugate_from_zero B hf.1 hzero m
  let g (m : E1) := projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m -
    projectiveToricLegendre u m
  have hpos : (∫⁻ m in projectiveMomentInterval, (g m).toENNReal ∂volume) < ⊤ := by
    apply lintegral_toENNReal_lt_top_of_bound volume
      isCompact_projectiveMomentInterval.measure_lt_top
    intro m hm
    have hh := EReal.sub_le_sub (hab m hm).2 (hL m)
    change projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m -
      projectiveToricLegendre u m ≤ ((b - L : ℝ) : EReal)
    change projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m -
      projectiveToricLegendre u m ≤ (b : EReal) - (L : EReal) at hh
    simpa only [← EReal.coe_sub] using hh
  rw [projectiveToricEnergy_eq_extendedLegendreIntegral hu hi,
    SGPT.Okounkov.bot_lt_signedIntegral_iff _ _ hpos]
  have hneg (m : E1) (hm : m ∈ projectiveMomentInterval) :
      -g m = projectiveToricLegendre u m -
        projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m := by
    have hh := hab m hm
    have htop : projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m ≠ ⊤ :=
      ne_top_of_le_ne_top (EReal.coe_ne_top b) hh.2
    have hbot : projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m ≠ ⊥ :=
      ne_bot_of_le_ne_bot (EReal.coe_ne_bot a) hh.1
    exact EReal.neg_sub (Or.inl hbot) (Or.inl htop) |>.trans (add_comm _ _)
  constructor
  · intro hgap
    apply (projectiveFiniteEnergy_shift_positive b (projectiveToricLegendre u)).mp
    apply lt_of_le_of_lt (lintegral_mono_ae ?_) hgap
    filter_upwards [ae_restrict_mem isCompact_projectiveMomentInterval.measurableSet] with m hm
    rw [hneg m hm]
    exact EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl (hab m hm).2)
  · intro hp
    have hs := (projectiveFiniteEnergy_shift_positive a (projectiveToricLegendre u)).mpr hp
    apply lt_of_le_of_lt (lintegral_mono_ae ?_) hs
    filter_upwards [ae_restrict_mem isCompact_projectiveMomentInterval.measurableSet] with m hm
    rw [hneg m hm]
    exact EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl (hab m hm).1)

private theorem projectiveFiniteEnergy_finite_class_iff_positive {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    RelativePreceqClasses.RelativeFiniteEnergyPreceq projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) u isModelPotential_projectiveNativeZero ↔
      (∫⁻ m in projectiveMomentInterval, (projectiveToricLegendre u m).toENNReal ∂volume) < ⊤ := by
  have hnative := isThetaPshPotential_projectiveNativeFS_of_source hu
  have hpreceq : RelativePreceqClasses.RelativePSHPreceq projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) u := by
    refine ⟨hnative, ?_⟩
    obtain ⟨C, hC⟩ := exists_upper_bound_projectiveThetaPSH hu
    exact (singularityLE_iff_exists_real _ _).mpr ⟨C, by simpa only [zero_add] using hC⟩
  exact (RelativePreceqClasses.relativeFiniteEnergyPreceq_iff_bot_lt_energy
    (hφ := isModelPotential_projectiveNativeZero) projectiveNativeFSBackground
    ⟨0, 0, fun _ => ⟨le_rfl, le_rfl⟩⟩ hpreceq).trans
    (projectiveFiniteEnergy_energy_positive_iff hu hi)

/-- The original unnormalized finite-energy class is exactly the original
Euclidean/Haar energy-one class. Full mass is produced by the native criterion. -/
theorem projectiveToric_mem_relativeFiniteEnergyPreceq_iff_energyOneClass {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    RelativePreceqClasses.RelativeFiniteEnergyPreceq projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) u isModelPotential_projectiveNativeZero ↔
      projectiveToricCorrectedDescent u ∈ EnergyOneClass B projectiveMomentInterval volume := by
  rw [mem_energyOneClass_iff volume B isCompact_projectiveMomentInterval
    nonempty_projectiveMomentInterval]
  constructor
  · intro hE
    exact ⟨(projectiveToric_mem_relativeFullMassPreceq_iff hu hi).mp hE.1,
      (projectiveFiniteEnergy_finite_class_iff_positive hu hi).mp hE⟩
  · rintro ⟨_hfull, hpos⟩
    exact (projectiveFiniteEnergy_finite_class_iff_positive hu hi).mpr hpos

/-- Actual finite-AE values are retained alongside integrability of the real
Legendre representative; no infinite value is silently mapped to real zero. -/
theorem projectiveToric_mem_relativeFiniteEnergyPreceq_iff_legendre_integrable {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    RelativePreceqClasses.RelativeFiniteEnergyPreceq projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) u isModelPotential_projectiveNativeZero ↔
      (∀ᵐ m ∂volume.restrict projectiveMomentInterval,
        projectiveToricLegendre u m ≠ ⊤ ∧ projectiveToricLegendre u m ≠ ⊥) ∧
      IntegrableOn (fun m => (projectiveToricLegendre u m).toReal)
        projectiveMomentInterval volume := by
  rw [projectiveFiniteEnergy_finite_class_iff_positive hu hi]
  have hf := projectiveToricCorrectedDescent_mem_growthClass hu hi
  have hG : Measurable (projectiveToricLegendre u) :=
    measurable_conjugate B (projectiveToricCorrectedDescent u)
  have hn := lintegral_neg_conjugate_lt_top_of_mem_growthClass volume B
    isCompact_projectiveMomentInterval nonempty_projectiveMomentInterval hf
  have hbot (m : E1) : projectiveToricLegendre u m ≠ ⊥ :=
    (isProper_conjugate_of_isContPerfPair B hf.1).2.2 m
  constructor
  · intro hp
    have hfin : ∀ᵐ m ∂volume.restrict projectiveMomentInterval,
        projectiveToricLegendre u m ≠ ⊤ ∧ projectiveToricLegendre u m ≠ ⊥ := by
      filter_upwards [ae_lt_top hG.ereal_toENNReal hp.ne] with m hm
      exact ⟨EReal.toENNReal_ne_top_iff.mp hm.ne, hbot m⟩
    exact ⟨hfin, SGPT.Okounkov.integrable_toReal_of_finite_parts
      (volume.restrict projectiveMomentInterval) (projectiveToricLegendre u) hG hfin hp hn⟩
  · rintro ⟨hfin, hI⟩
    have he : (∫⁻ m in projectiveMomentInterval, (projectiveToricLegendre u m).toENNReal ∂volume) =
        ∫⁻ m in projectiveMomentInterval, ENNReal.ofReal (projectiveToricLegendre u m).toReal ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [hfin] with m hm
      rw [← EReal.coe_toReal hm.1 hm.2, EReal.real_coe_toENNReal, EReal.toReal_coe]
    rw [he]
    exact (lintegral_ofReal_le_lintegral_enorm _).trans_lt hI.2

end SGPT.Toric
