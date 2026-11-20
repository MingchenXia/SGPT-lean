import SGPT.Toric.SingularProjectiveToricEnergy
import SGPT.Convex.ExtendedSignedIntegralUpperBound

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open SGPT.Foundations.Analysis.Pending.RelativeEnergy
open SGPT.Foundations.Analysis.Pending.RelativePreceqClasses
open scoped Topology ENNReal RealInnerProductSpace
local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)
local notation "E1" => EuclideanSpace ℝ (Fin 1)
local notation "B" => innerₗ E1

private theorem zero_bounded : IsBoundedPotential (fun _ : P1 => (0 : EReal)) :=
  ⟨0, 0, fun _ => by simp⟩

private theorem zero_invariant : ProjectiveCircleInvariant (fun _ : P1 => (0 : EReal)) :=
  fun _ _ _ => rfl

private theorem moment_volume : volume projectiveMomentInterval = 1 := by
  have h := projectiveToricNonPluripolarMeasure_zero_univ
  rw [projectiveToricNonPluripolarMeasure_univ_eq_newtonLength
    isThetaPSH_projectiveZero zero_invariant, projectiveToricNewtonBody_zero] at h
  exact h

private theorem model_volume : modelVolume projectiveNativeFSBackground.form
    (fun _ : P1 => (0 : EReal)) isModelPotential_projectiveNativeZero = 1 := by
  have h := congrArg ENNReal.toReal projectiveToricNonPluripolarMeasure_zero_univ
  simpa only [modelVolume, Measure.real, DiagonalMass.diagonalPotentialMeasure,
    projectiveToricNonPluripolarMeasure, ENNReal.toReal_one] using h

private theorem zero_legendre_finite : ∀ m ∈ projectiveMomentInterval,
    projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m =
      ((projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m).toReal : EReal) := by
  have hg := (projectiveToric_mem_relativeEInfinity_iff_boundedGrowthClass
    isThetaPSH_projectiveZero zero_invariant).mp
    ⟨isThetaPshPotential_projectiveNativeFS_of_source isThetaPSH_projectiveZero,
      BoundedMongeAmpereEnergy.sameSingularityType_of_bounded zero_bounded zero_bounded⟩
  obtain ⟨a, b, hab⟩ := conjugate_bounds_of_mem_boundedGrowthClass B
    isCompact_projectiveMomentInterval convex_projectiveMomentInterval hg
  have hp := isProper_conjugate_of_isContPerfPair B
    (projectiveToricCorrectedDescent_mem_growthClass isThetaPSH_projectiveZero zero_invariant).1
  intro m hm
  exact (EReal.coe_toReal
    (ne_top_of_le_ne_top (EReal.coe_ne_top b) (hab m hm).2) (hp.2.2 m)).symm

private theorem finite_sub_le (r C : ℝ) (z : EReal)
    (h : (r : EReal) ≤ z + (C : EReal)) : (r : EReal) - z ≤ (C : EReal) := by
  induction z using EReal.rec with
  | bot => simp at h
  | top => simp
  | coe z =>
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    linarith

private theorem finite_gap_shift (r C : ℝ) (z : EReal) :
    (C : EReal) - ((r : EReal) - z) = (z + (C : EReal)) - (r : EReal) := by
  induction z using EReal.rec with
  | bot => simp
  | top => simp
  | coe z => rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_sub]; congr 1; ring

/-- The literal original extended signed Legendre integral equals the actual
native energy for every original invariant FS-PSH source potential. -/
theorem projectiveToric_energy_eq_extendedSignedIntegral {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    RelativeDarvasDistance.energy projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) isModelPotential_projectiveNativeZero u =
      extendedSignedIntegral (volume.restrict projectiveMomentInterval)
        (fun m => projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m -
          projectiveToricLegendre u m) := by
  obtain ⟨A, hA⟩ := exists_upper_bound_projectiveThetaPSH hu
  let C : ℝ := max A 0
  have hC : 0 ≤ C := le_max_right _ _
  have hupper : u ≤ fun _ => (C : EReal) := fun p =>
    (hA p).trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
  let v : P1 → EReal := fun p => u p + ((-C : ℝ) : EReal)
  have hv : projectiveLineAtlas.IsThetaPSH projectiveFSForm v := hu.add_const (-C)
  have hiv : ProjectiveCircleInvariant v := fun a b p =>
    congrArg (fun z : EReal => z + ((-C : ℝ) : EReal)) (hi a b p)
  have hv0 : v ≤ fun _ => (0 : EReal) := by
    intro p
    have h := add_le_add (hupper p) (le_refl ((-C : ℝ) : EReal))
    simpa only [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] using h
  have hGv : projectiveToricLegendre v = fun m => projectiveToricLegendre u m + (C : EReal) := by
    simpa only [v, EReal.coe_neg, sub_eq_add_neg, neg_neg] using projectiveToricLegendre_add_const u (-C)
  let H : E1 → EReal := fun m => projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m -
    projectiveToricLegendre u m
  have hH : Measurable H := (measurable_conjugate B _).sub (measurable_conjugate B _)
  have horder : projectiveToricLegendre (fun _ : P1 => (0 : EReal)) ≤ projectiveToricLegendre v := by
    apply conjugate_antitone B
    intro x
    exact add_le_add (hv0 _) le_rfl
  have hHupper : H ≤ᵐ[volume.restrict projectiveMomentInterval] fun _ => (C : EReal) := by
    filter_upwards [ae_restrict_mem isCompact_projectiveMomentInterval.isClosed.measurableSet] with m hm
    dsimp only [H]
    rw [zero_legendre_finite m hm]
    have h := horder m
    rw [hGv, zero_legendre_finite m hm] at h
    exact finite_sub_le _ C _ h
  have hgap : (∫⁻ m, ((C : EReal) - H m).toENNReal ∂volume.restrict projectiveMomentInterval) =
      ∫⁻ m in projectiveMomentInterval,
        (projectiveToricLegendre v m - projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m).toENNReal := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem isCompact_projectiveMomentInterval.isClosed.measurableSet] with m hm
    simp only [H, hGv]
    rw [zero_legendre_finite m hm]
    exact congrArg EReal.toENNReal (finite_gap_shift _ C _)
  have hfinite : IsFiniteMeasure (volume.restrict projectiveMomentInterval) := by
    exact ⟨by simpa only [Measure.restrict_apply_univ] using
      isCompact_projectiveMomentInterval.measure_lt_top (μ := volume)⟩
  have hsigned := extendedSignedIntegral_eq_upper_gap
    (volume.restrict projectiveMomentInterval) hH C hC hHupper
  rw [Measure.restrict_apply_univ, moment_volume, mul_one, ← EReal.real_coe_toENNReal,
    EReal.coe_toENNReal (EReal.coe_le_coe_iff.mpr hC), hgap] at hsigned
  have he := energy_add_const (hφ := isModelPotential_projectiveNativeZero)
    projectiveNativeFSBackground zero_bounded v C
  have hefun : (fun p => v p + (C : EReal)) = u := by
    simpa only [neg_neg] using translate_translate_neg u (-C)
  rw [hefun, model_volume, mul_one,
    projectiveToric_energy_eq_neg_gap_lintegral_of_nonpos hv hiv hv0] at he
  rw [he, hsigned]
  exact add_comm _ _

private theorem positive_lintegral_add_nonneg_iff {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsFiniteMeasure μ] (H : A → EReal) (hH : Measurable H)
    (C : ℝ) (hC : 0 ≤ C) :
    (∫⁻ x, (H x + (C : EReal)).toENNReal ∂μ) < ⊤ ↔
      (∫⁻ x, (H x).toENNReal ∂μ) < ⊤ := by
  have hp : Measurable (fun x => (H x).toENNReal) :=
    EReal.continuous_toENNReal.measurable.comp hH
  have hK : (∫⁻ _x : A, ENNReal.ofReal C ∂μ) < ⊤ := by
    rw [lintegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ Set.univ)
  have hlo : (∫⁻ x, (H x).toENNReal ∂μ) ≤ ∫⁻ x, (H x + (C : EReal)).toENNReal ∂μ := by
    apply lintegral_mono
    intro x
    apply EReal.toENNReal_le_toENNReal
    simpa using add_le_add (le_refl (H x)) (EReal.coe_le_coe_iff.mpr hC)
  have hhi : (∫⁻ x, (H x + (C : EReal)).toENNReal ∂μ) ≤
      (∫⁻ x, (H x).toENNReal ∂μ) + ∫⁻ _x : A, ENNReal.ofReal C ∂μ := by
    rw [← lintegral_add_left hp]
    apply lintegral_mono
    intro x
    simpa only [EReal.real_coe_toENNReal] using (EReal.toENNReal_add_le (x := H x) (y := (C : EReal)))
  exact ⟨fun h => lt_of_le_of_lt hlo h,
    fun h => lt_of_le_of_lt hhi (ENNReal.add_lt_top.mpr ⟨h, hK⟩)⟩

/-- The actual original unnormalized native finite-energy class is exactly
finite positive-part integral of the genuine original Legendre function. -/
theorem projectiveToric_mem_relativeFiniteEnergyPreceq_iff_legendre_positive {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    RelativeFiniteEnergyPreceq projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) u isModelPotential_projectiveNativeZero ↔
      (∫⁻ m in projectiveMomentInterval, (projectiveToricLegendre u m).toENNReal) < ⊤ := by
  obtain ⟨A, hA⟩ := exists_upper_bound_projectiveThetaPSH hu
  let C : ℝ := max A 0
  have hC : 0 ≤ C := le_max_right _ _
  have hupper : u ≤ fun _ => (C : EReal) := fun p =>
    (hA p).trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
  let v : P1 → EReal := fun p => u p + ((-C : ℝ) : EReal)
  have hv : projectiveLineAtlas.IsThetaPSH projectiveFSForm v := hu.add_const (-C)
  have hiv : ProjectiveCircleInvariant v := fun a b p =>
    congrArg (fun z : EReal => z + ((-C : ℝ) : EReal)) (hi a b p)
  have hv0 : v ≤ fun _ => (0 : EReal) := by
    intro p
    have h := add_le_add (hupper p) (le_refl ((-C : ℝ) : EReal))
    simpa only [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] using h
  have hGv : projectiveToricLegendre v = fun m => projectiveToricLegendre u m + (C : EReal) := by
    simpa only [v, EReal.coe_neg, sub_eq_add_neg, neg_neg] using projectiveToricLegendre_add_const u (-C)
  have hclass : RelativeFiniteEnergyPreceq projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) u isModelPotential_projectiveNativeZero ↔
      RelativeFiniteEnergy projectiveNativeFSBackground.form
        (fun _ : P1 => (0 : EReal)) v isModelPotential_projectiveNativeZero := by
    constructor
    · intro h
      exact h.relativeFiniteEnergy_add projectiveNativeFSBackground hv0
    · intro h
      exact relativeFiniteEnergyPreceq_of_add projectiveNativeFSBackground (preceq_of_relativeFiniteEnergy h)
  have hfinite : IsFiniteMeasure (volume.restrict projectiveMomentInterval) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      isCompact_projectiveMomentInterval.measure_lt_top (μ := volume)⟩
  rw [hclass, projectiveToric_mem_relativeFiniteEnergy_iff_legendre_positive hv hiv hv0, hGv]
  exact positive_lintegral_add_nonneg_iff (volume.restrict projectiveMomentInterval)
    (projectiveToricLegendre u) (measurable_conjugate B _) C hC

/-- Actual native unnormalized E1 supplies the original convex full-mass clause,
so its positive-integral condition is precisely the original EnergyOneClass. -/
theorem projectiveToric_mem_relativeFiniteEnergyPreceq_iff_energyOneClass_localSingular {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    RelativeFiniteEnergyPreceq projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) u isModelPotential_projectiveNativeZero ↔
      projectiveToricCorrectedDescent u ∈ EnergyOneClass B projectiveMomentInterval volume := by
  rw [mem_energyOneClass_iff volume B isCompact_projectiveMomentInterval nonempty_projectiveMomentInterval]
  constructor
  · intro h
    exact ⟨(projectiveToric_mem_relativeFullMassPreceq_iff hu hi).mp h.1,
      (projectiveToric_mem_relativeFiniteEnergyPreceq_iff_legendre_positive hu hi).mp h⟩
  · intro h
    exact (projectiveToric_mem_relativeFiniteEnergyPreceq_iff_legendre_positive hu hi).mpr h.2

/-- The full unnormalized original E1/Legendre L1 correspondence preserves every
infinite conjugate value in the actual extended absolute integral. -/
theorem projectiveToric_mem_relativeFiniteEnergyPreceq_iff_legendre_L1 {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    RelativeFiniteEnergyPreceq projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) u isModelPotential_projectiveNativeZero ↔
      (∫⁻ m in projectiveMomentInterval,
        (projectiveToricLegendre u m).toENNReal + (-projectiveToricLegendre u m).toENNReal) < ⊤ := by
  rw [projectiveToric_mem_relativeFiniteEnergyPreceq_iff_legendre_positive hu hi]
  have hm : Measurable (fun m => (projectiveToricLegendre u m).toENNReal) :=
    EReal.continuous_toENNReal.measurable.comp (measurable_conjugate B _)
  rw [lintegral_add_left hm]
  have hn := lintegral_neg_conjugate_lt_top_of_mem_growthClass volume B
    isCompact_projectiveMomentInterval nonempty_projectiveMomentInterval
    (projectiveToricCorrectedDescent_mem_growthClass hu hi)
  exact ⟨fun h => ENNReal.add_lt_top.mpr ⟨h, hn⟩,
    fun h => (ENNReal.add_lt_top.mp h).1⟩
end SGPT.Toric
