import SGPT.Toric.ProjectiveProductFiniteEnergy
import SGPT.Convex.ExtendedSignedIntegralUpperBound

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open SGPT.Foundations.Analysis.Pending.RelativeEnergy
open SGPT.Foundations.Analysis.Pending.RelativePreceqClasses
open scoped Topology ENNReal RealInnerProductSpace

variable {n : ℕ}
local notation "X" => projectiveProductSpace n
local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "B" => innerₗ En

private theorem zero_bounded : IsBoundedPotential (fun _ : X => (0 : EReal)) :=
  ⟨0, 0, fun _ => by simp⟩
private theorem zero_invariant : ProjectiveProductCircleInvariant (fun _ : X => (0 : EReal)) :=
  fun _ _ _ => rfl
private theorem profile_coe_eq {u : X → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) :
    (fun x => (projectiveProductToricEuclideanProfile u x : EReal)) =
      projectiveProductToricCorrectedDescent u := by
  funext x
  have hf := finite_of_pshOn_tropicalPullback (pshOn_projectiveProductToricCorrectedDescent hu hi) x
  exact EReal.coe_toReal hf.1 hf.2

private theorem source_upper_bound {u : X → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u) :
    ∃ A : ℝ, ∀ p, u p ≤ (A : EReal) := by
  let : Nonempty X := ⟨(projectiveProductCoordinates n).symm (fun _ => projectiveOrigin)⟩
  exact hu.exists_global_upper_bound

/-- Actual native strong PSH and original invariance give the literal translated profile,
with genuine source finiteness established before every real readback. -/
theorem projectiveProductToricEuclideanProfile_add_const {u : X → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) (C : ℝ) :
    projectiveProductToricEuclideanProfile (fun p => u p + (C : EReal)) =
      fun x => projectiveProductToricEuclideanProfile u x + C := by
  have hi' : ProjectiveProductCircleInvariant (fun p => u p + (C : EReal)) :=
    fun a ha p => congrArg (fun z : EReal => z + (C : EReal)) (hi a ha p)
  funext x
  apply EReal.coe_injective
  rw [EReal.coe_add, congrFun (profile_coe_eq (hu.add_const C) hi') x,
    congrFun (profile_coe_eq hu hi) x]
  exact add_right_comm _ (C : EReal) _

/-- Literal finite source translation commutes with the extended conjugate supremum,
retaining all original infinite values. -/
theorem projectiveProductToricLegendre_add_const {u : X → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) (C : ℝ) :
    projectiveProductToricLegendre (fun p => u p + (C : EReal)) =
      fun y => projectiveProductToricLegendre u y - (C : EReal) := by
  funext y
  let f : En → EReal := fun x => (projectiveProductToricEuclideanProfile u x : EReal)
  have hcost (x : En) : (B x y : EReal) - (f x + (C : EReal)) =
      ((B x y : EReal) - f x) - (C : EReal) := by
    simpa only [add_zero, zero_add, zero_sub, sub_eq_add_neg] using
      (EReal.add_sub_add_comm (a := (B x y : EReal)) (b := 0)
        (c := f x) (d := (C : EReal)) (.inr (EReal.coe_ne_top C)) (.inr (EReal.coe_ne_bot C)))
  simp only [projectiveProductToricLegendre,
    projectiveProductToricEuclideanProfile_add_const hu hi C, EReal.coe_add, conjugate]
  change (⨆ x, (B x y : EReal) - (f x + (C : EReal))) =
    (⨆ x, (B x y : EReal) - f x) - (C : EReal)
  simp_rw [hcost]
  simpa only [sub_eq_add_neg, ← EReal.coe_neg] using
    SGPT.Foundations.Analysis.FirstPass.iSup_add_coe (fun x => (B x y : EReal) - f x) (-C)

/-- The actual native reference model volume is the literal produced n!, also for n=0. -/
theorem projectiveProductZero_modelVolume (n : ℕ) :
    modelVolume (projectiveProductFSBackground n).form (fun _ : projectiveProductSpace n => (0 : EReal))
      (isModelPotential_projectiveProductZero n) = (n.factorial : ℝ) := by
  have h := congrArg ENNReal.toReal (projectiveProductZeroMixedMeasure_univ n)
  simpa only [modelVolume, Measure.real, DiagonalMass.diagonalPotentialMeasure,
    ENNReal.toReal_natCast] using h

private theorem zero_legendre_finite : ∀ m ∈ euclideanUnitCube n,
    projectiveProductToricLegendre (fun _ : X => (0 : EReal)) m =
      ((projectiveProductToricLegendre (fun _ : X => (0 : EReal)) m).toReal : EReal) :=
  projectiveProductToricLegendre_finite_of_bounded
    (isThetaPshPotential_projectiveProductZero n) zero_invariant zero_bounded

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

/-- The actual original unnormalized native energy equals n! times the true
extended signed Legendre integral. Infinite conjugate values remain extended. -/
theorem projectiveProduct_energy_eq_extendedSignedIntegral {u : X → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) :
    RelativeDarvasDistance.energy (projectiveProductFSBackground n).form (fun _ : X => (0 : EReal))
      (isModelPotential_projectiveProductZero n) u =
      ((n.factorial : ℝ) : EReal) * extendedSignedIntegral (volume.restrict (euclideanUnitCube n))
        (fun m => projectiveProductToricLegendre (fun _ : X => (0 : EReal)) m -
          projectiveProductToricLegendre u m) := by
  obtain ⟨A, hA⟩ := source_upper_bound hu
  let C : ℝ := max A 0
  have hC : 0 ≤ C := le_max_right _ _
  have hupper : u ≤ fun _ => (C : EReal) := fun p =>
    (hA p).trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
  let v : X → EReal := fun p => u p + ((-C : ℝ) : EReal)
  have hv : IsThetaPshPotential (projectiveProductFSBackground n).form.val v := hu.add_const (-C)
  have hiv : ProjectiveProductCircleInvariant v := fun a b p =>
    congrArg (fun z : EReal => z + ((-C : ℝ) : EReal)) (hi a b p)
  have hv0 : v ≤ fun _ => (0 : EReal) := by
    intro p
    have h := add_le_add (hupper p) (le_refl ((-C : ℝ) : EReal))
    simpa only [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] using h
  have hGv : projectiveProductToricLegendre v = fun m => projectiveProductToricLegendre u m + (C : EReal) := by
    simpa only [v, EReal.coe_neg, sub_eq_add_neg, neg_neg] using
      projectiveProductToricLegendre_add_const hu hi (-C)
  let H : En → EReal := fun m => projectiveProductToricLegendre (fun _ : X => (0 : EReal)) m -
    projectiveProductToricLegendre u m
  have hH : Measurable H := (measurable_conjugate B _).sub (measurable_conjugate B _)
  have horder : projectiveProductToricLegendre (fun _ : X => (0 : EReal)) ≤ projectiveProductToricLegendre v := by
    apply conjugate_antitone B
    rw [profile_coe_eq hv hiv, profile_coe_eq (isThetaPshPotential_projectiveProductZero n) zero_invariant]
    intro x
    exact add_le_add (hv0 _) le_rfl
  have hHupper : H ≤ᵐ[volume.restrict (euclideanUnitCube n)] fun _ => (C : EReal) := by
    filter_upwards [ae_restrict_mem (isCompact_euclideanUnitCube n).isClosed.measurableSet] with m hm
    dsimp only [H]
    rw [zero_legendre_finite m hm]
    have h := horder m
    rw [hGv, zero_legendre_finite m hm] at h
    exact finite_sub_le _ C _ h
  have hgap : (∫⁻ m, ((C : EReal) - H m).toENNReal ∂volume.restrict (euclideanUnitCube n)) =
      ∫⁻ m in euclideanUnitCube n,
        (projectiveProductToricLegendre v m - projectiveProductToricLegendre (fun _ : X => (0 : EReal)) m).toENNReal := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (isCompact_euclideanUnitCube n).isClosed.measurableSet] with m hm
    simp only [H, hGv]
    rw [zero_legendre_finite m hm]
    exact congrArg EReal.toENNReal (finite_gap_shift _ C _)
  let : IsFiniteMeasure (volume.restrict (euclideanUnitCube n)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (isCompact_euclideanUnitCube n).measure_lt_top (μ := volume)⟩
  have hsigned := extendedSignedIntegral_eq_upper_gap
    (volume.restrict (euclideanUnitCube n)) hH C hC hHupper
  rw [Measure.restrict_apply_univ, volume_euclideanUnitCube, mul_one,
    ← EReal.real_coe_toENNReal, EReal.coe_toENNReal (EReal.coe_le_coe_iff.mpr hC), hgap] at hsigned
  have he := energy_add_const (hφ := isModelPotential_projectiveProductZero n)
    (projectiveProductFSBackground n) zero_bounded v C
  have hefun : (fun p => v p + (C : EReal)) = u := by
    simpa only [neg_neg] using translate_translate_neg u (-C)
  rw [hefun, projectiveProductZero_modelVolume,
    projectiveProduct_energy_eq_neg_gap_lintegral_of_nonpos hv hiv hv0] at he
  rw [he, hsigned, EReal.mul_sub_of_nonneg_of_ne_top
    (EReal.coe_nonneg.mpr (Nat.cast_nonneg n.factorial)) (EReal.coe_ne_top _)]
  have hcn : (((n.factorial : ℝ) : EReal)) = ((n.factorial : ENNReal) : EReal) := by
    simpa only [ENNReal.toReal_natCast] using
      (EReal.coe_ennreal_toReal (x := (n.factorial : ENNReal)) (by simp))
  rw [EReal.coe_ennreal_mul, ← hcn, ← EReal.coe_mul, mul_comm (n.factorial : ℝ) C,
    sub_eq_add_neg, add_comm]

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


/-- The actual original unnormalized native E1 class is exactly finite extended
positive conjugate integral, through genuine native finite translation. -/
theorem projectiveProduct_mem_relativeFiniteEnergyPreceq_iff_legendre_positive {u : X → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) :
    RelativeFiniteEnergyPreceq (projectiveProductFSBackground n).form
      (fun _ : X => (0 : EReal)) u (isModelPotential_projectiveProductZero n) ↔
      (∫⁻ m in euclideanUnitCube n, (projectiveProductToricLegendre u m).toENNReal) < ⊤ := by
  obtain ⟨A, hA⟩ := source_upper_bound hu
  let C : ℝ := max A 0
  have hC : 0 ≤ C := le_max_right _ _
  have hupper : u ≤ fun _ => (C : EReal) := fun p =>
    (hA p).trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
  let v : X → EReal := fun p => u p + ((-C : ℝ) : EReal)
  have hv : IsThetaPshPotential (projectiveProductFSBackground n).form.val v := hu.add_const (-C)
  have hiv : ProjectiveProductCircleInvariant v := fun a b p =>
    congrArg (fun z : EReal => z + ((-C : ℝ) : EReal)) (hi a b p)
  have hv0 : v ≤ fun _ => (0 : EReal) := by
    intro p
    have h := add_le_add (hupper p) (le_refl ((-C : ℝ) : EReal))
    simpa only [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] using h
  have hGv : projectiveProductToricLegendre v = fun m => projectiveProductToricLegendre u m + (C : EReal) := by
    simpa only [v, EReal.coe_neg, sub_eq_add_neg, neg_neg] using
      projectiveProductToricLegendre_add_const hu hi (-C)
  have hclass : RelativeFiniteEnergyPreceq (projectiveProductFSBackground n).form
      (fun _ : X => (0 : EReal)) u (isModelPotential_projectiveProductZero n) ↔
      RelativeFiniteEnergy (projectiveProductFSBackground n).form
        (fun _ : X => (0 : EReal)) v (isModelPotential_projectiveProductZero n) := by
    constructor
    · intro h
      exact h.relativeFiniteEnergy_add (projectiveProductFSBackground n) hv0
    · intro h
      exact relativeFiniteEnergyPreceq_of_add (projectiveProductFSBackground n)
        (preceq_of_relativeFiniteEnergy h)
  let : IsFiniteMeasure (volume.restrict (euclideanUnitCube n)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (isCompact_euclideanUnitCube n).measure_lt_top (μ := volume)⟩
  rw [hclass, projectiveProduct_mem_relativeFiniteEnergy_iff_legendre_positive hv hiv hv0, hGv]
  exact positive_lintegral_add_nonneg_iff (volume.restrict (euclideanUnitCube n))
    (projectiveProductToricLegendre u) (measurable_conjugate B _) C hC

/-- Full original unnormalized native E1 is equivalent to true extended Legendre L1;
original growth supplies the negative part without erasing any infinite value. -/
theorem projectiveProduct_mem_relativeFiniteEnergyPreceq_iff_legendre_L1 {u : X → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) :
    RelativeFiniteEnergyPreceq (projectiveProductFSBackground n).form
      (fun _ : X => (0 : EReal)) u (isModelPotential_projectiveProductZero n) ↔
      (∫⁻ m in euclideanUnitCube n, (projectiveProductToricLegendre u m).toENNReal +
        (-projectiveProductToricLegendre u m).toENNReal) < ⊤ := by
  rw [projectiveProduct_mem_relativeFiniteEnergyPreceq_iff_legendre_positive hu hi]
  have hm : Measurable (fun m => (projectiveProductToricLegendre u m).toENNReal) :=
    EReal.continuous_toENNReal.measurable.comp (measurable_conjugate B _)
  rw [lintegral_add_left hm]
  have hn := lintegral_neg_conjugate_lt_top_of_mem_growthClass volume B
    (isCompact_euclideanUnitCube n) (nonempty_euclideanUnitCube n)
    (projectiveProductToricProfile_mem_growthClass hu hi)
  exact ⟨fun h => ENNReal.add_lt_top.mpr ⟨h, hn⟩,
    fun h => (ENNReal.add_lt_top.mp h).1⟩

end SGPT.Toric
