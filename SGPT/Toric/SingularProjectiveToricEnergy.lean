import SGPT.Toric.ProjectiveToricTruncation
import SGPT.Foundations.Analysis.Pending.FiniteEnergyCharacterization

set_option autoImplicit false

/-!
# The actual normalized singular projective toric energy

Genuine original lower truncations and the extended conjugate-gap MCT identify
the actual native extended energy, including negative infinity. The true native
finite-energy characterization then supplies the original E1/Legendre criterion.
-/

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

private theorem legendre_finite_of_bounded {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) (hb : IsBoundedPotential u) :
    ∀ m ∈ projectiveMomentInterval,
      projectiveToricLegendre u m = ((projectiveToricLegendre u m).toReal : EReal) := by
  have hg := (projectiveToric_mem_relativeEInfinity_iff_boundedGrowthClass hu hi).mp
    ⟨isThetaPshPotential_projectiveNativeFS_of_source hu,
      BoundedMongeAmpereEnergy.sameSingularityType_of_bounded hb zero_bounded⟩
  obtain ⟨a, b, hab⟩ := conjugate_bounds_of_mem_boundedGrowthClass B
    isCompact_projectiveMomentInterval convex_projectiveMomentInterval hg
  have hp := isProper_conjugate_of_isContPerfPair B
    (projectiveToricCorrectedDescent_mem_growthClass hu hi).1
  intro m hm
  exact (EReal.coe_toReal
    (ne_top_of_le_ne_top (EReal.coe_ne_top b) (hab m hm).2) (hp.2.2 m)).symm

private theorem legendre_zero_le_of_nonpos {u : P1 → EReal}
    (hle : u ≤ fun _ => (0 : EReal)) :
    projectiveToricLegendre (fun _ : P1 => (0 : EReal)) ≤ projectiveToricLegendre u := by
  apply conjugate_antitone B
  intro x
  exact add_le_add (hle _) le_rfl

private theorem coe_iSup_ennreal (a : ℕ → ℝ≥0∞) :
    (((⨆ j : ℕ, a j) : ℝ≥0∞) : EReal) = ⨆ j : ℕ, (a j : EReal) := by
  let s : EReal := ⨆ j : ℕ, (a j : EReal)
  have hs : 0 ≤ s := (EReal.coe_ennreal_nonneg (a 0)).trans
    (le_iSup (fun j : ℕ => (a j : EReal)) 0)
  have hall : ∀ j, a j ≤ s.toENNReal := by
    intro j
    simpa only [EReal.toENNReal_coe] using
      EReal.toENNReal_le_toENNReal (le_iSup (fun i : ℕ => (a i : EReal)) j)
  apply le_antisymm
  · have h := EReal.coe_ennreal_le_coe_ennreal_iff.mpr (iSup_le hall)
    rwa [EReal.coe_toENNReal hs] at h
  · exact iSup_le (fun j => EReal.coe_ennreal_le_coe_ennreal_iff.mpr (le_iSup a j))

private theorem iInf_neg_coe_ennreal (a : ℕ → ℝ≥0∞) :
    (⨅ j : ℕ, -(a j : EReal)) = -(((⨆ j : ℕ, a j) : ℝ≥0∞) : EReal) := by
  apply le_antisymm
  · have hall : ∀ j : ℕ, (a j : EReal) ≤ -(⨅ i : ℕ, -(a i : EReal)) := by
      intro j
      simpa only [neg_neg] using EReal.neg_le_neg_iff.mpr (iInf_le (fun i => -(a i : EReal)) j)
    have h : (((⨆ j : ℕ, a j) : ℝ≥0∞) : EReal) ≤ -(⨅ i : ℕ, -(a i : EReal)) := by
      rw [coe_iSup_ennreal]
      exact iSup_le hall
    simpa only [neg_neg] using EReal.neg_le_neg_iff.mpr h
  · apply le_iInf
    intro j
    exact EReal.neg_le_neg_iff.mpr (EReal.coe_ennreal_le_coe_ennreal_iff.mpr (le_iSup a j))

private theorem bounded_energy_eq_neg_gap {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) (hb : IsBoundedPotential u)
    (hle : u ≤ fun _ => (0 : EReal)) :
    (relativeEnergyOfMinimalType projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) u
      (isThetaPshPotential_projectiveNativeFS_of_source isThetaPSH_projectiveZero)
      (isThetaPshPotential_projectiveNativeFS_of_source hu) : EReal) =
        -((∫⁻ m in projectiveMomentInterval,
          (projectiveToricLegendre u m -
            projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m).toENNReal) : EReal) := by
  let q : E1 → ℝ := fun m => (projectiveToricLegendre u m).toReal -
    (projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m).toReal
  have iq : Integrable q (volume.restrict projectiveMomentInterval) :=
    (projectiveToricLegendre_integrable_of_bounded hu hi hb).sub
      (projectiveToricLegendre_integrable_of_bounded
        isThetaPSH_projectiveZero zero_invariant zero_bounded)
  have hf := legendre_finite_of_bounded hu hi hb
  have h0 := legendre_finite_of_bounded isThetaPSH_projectiveZero zero_invariant zero_bounded
  have hqn : 0 ≤ᵐ[volume.restrict projectiveMomentInterval] q := by
    filter_upwards [ae_restrict_mem isCompact_projectiveMomentInterval.isClosed.measurableSet]
      with m hm
    have h := legendre_zero_le_of_nonpos hle m
    rw [hf m hm, h0 m hm, EReal.coe_le_coe_iff] at h
    exact sub_nonneg.mpr h
  have hlin : (∫⁻ m in projectiveMomentInterval,
      (projectiveToricLegendre u m -
        projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m).toENNReal) =
      ∫⁻ m, ENNReal.ofReal (q m) ∂volume.restrict projectiveMomentInterval := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem isCompact_projectiveMomentInterval.isClosed.measurableSet]
      with m hm
    rw [hf m hm, h0 m hm, ← EReal.coe_sub, EReal.real_coe_toENNReal]
  have hiq : 0 ≤ ∫ m, q m ∂volume.restrict projectiveMomentInterval :=
    integral_nonneg_of_ae hqn
  have hcoe :
      ((∫⁻ m in projectiveMomentInterval,
        (projectiveToricLegendre u m -
          projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m).toENNReal) : EReal) =
      (((∫ m, q m ∂volume.restrict projectiveMomentInterval) : ℝ) : EReal) := by
    rw [hlin, ← ofReal_integral_eq_lintegral_ofReal iq hqn]
    simpa only [EReal.real_coe_toENNReal] using
      EReal.coe_toENNReal (EReal.coe_nonneg.mpr hiq)
  rw [projectiveToric_relativeEnergyOfMinimalType_zero_eq_legendre hu hi hb, hcoe]
  rw [show (fun m => (projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m).toReal -
    (projectiveToricLegendre u m).toReal) = fun m => -q m from by funext m; dsimp [q]; ring,
    integral_neg, EReal.coe_neg]

/-- The actual normalized singular source energy is the negative genuine
extended Legendre gap integral. An infinite gap gives negative-infinite energy;
all native normalization, model, truncation and source fields are manufactured. -/
theorem projectiveToric_energy_eq_neg_gap_lintegral_of_nonpos {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) (hle : u ≤ fun _ => (0 : EReal)) :
    RelativeDarvasDistance.energy projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) isModelPotential_projectiveNativeZero u =
        -((∫⁻ m in projectiveMomentInterval,
          (projectiveToricLegendre u m -
            projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m).toENNReal) : EReal) := by
  have hrel : RelativePSH projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) u :=
    ⟨isThetaPshPotential_projectiveNativeFS_of_source hu, hle⟩
  have hInf := MongeAmpereEnergyDecreasing.relativeMongeAmpereEnergy_eq_iInf_truncation
    projectiveNativeFSBackground projectiveNativeFSBackground.form
    isModelPotential_projectiveNativeZero hrel zero_bounded
  have hcut (j : ℕ) : MongeAmpereEnergyDecreasing.truncation
      (fun _ : P1 => (0 : EReal)) u j = projectiveToricTruncation u j := by
    funext p
    simp only [MongeAmpereEnergyDecreasing.truncation, projectiveToricTruncation,
      zero_sub, ← EReal.coe_neg]
  calc
    _ = ⨅ j : ℕ, (relativeEnergyOfMinimalType projectiveNativeFSBackground.form
        (fun _ : P1 => (0 : EReal)) (projectiveToricTruncation u j)
        (isThetaPshPotential_projectiveNativeFS_of_source isThetaPSH_projectiveZero)
        (isThetaPshPotential_projectiveNativeFS_of_source
          (isThetaPSH_projectiveToricTruncation hu j)) : EReal) := by
      rw [RelativeDarvasDistance.energy_eq hrel, hInf]
      apply iInf_congr
      intro j
      congr 1
      exact RelativePreceqClasses.relativeEnergyOfMinimalType_congr _ (hcut j) _ _
    _ = ⨅ j : ℕ, -((∫⁻ m in projectiveMomentInterval,
        (projectiveToricLegendre (projectiveToricTruncation u j) m -
          projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m).toENNReal) : EReal) := by
      apply iInf_congr
      intro j
      exact bounded_energy_eq_neg_gap (isThetaPSH_projectiveToricTruncation hu j)
        (hi.truncation j) (isBoundedPotential_projectiveToricTruncation hle j)
        (fun p => max_le (hle p)
          (EReal.coe_le_coe_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg j))))
    _ = -(((⨆ j : ℕ, ∫⁻ m in projectiveMomentInterval,
        (projectiveToricLegendre (projectiveToricTruncation u j) m -
          projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m).toENNReal) : ℝ≥0∞) : EReal) :=
      iInf_neg_coe_ennreal _
    _ = _ := by rw [← projectiveToricLegendre_gap_lintegral_eq_iSup_truncation hu hi]

private theorem sub_coe_add_coe (z : EReal) (r : ℝ) :
    (z - (r : EReal)) + (r : EReal) = z := by
  cases z using EReal.rec with
  | bot => simp
  | top => simp
  | coe a =>
    rw [← EReal.coe_sub, ← EReal.coe_add]
    congr 1
    ring

/-- Finite bounds for the genuine zero-reference conjugate compare actual
extended positive-part and gap integrals, without discarding infinite values. -/
theorem projectiveToric_gap_lintegral_lt_top_iff_positive_lintegral {u : P1 → EReal}
    (_hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (_hi : ProjectiveCircleInvariant u) :
    (∫⁻ m in projectiveMomentInterval,
      (projectiveToricLegendre u m -
        projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m).toENNReal) < ⊤ ↔
      (∫⁻ m in projectiveMomentInterval, (projectiveToricLegendre u m).toENNReal) < ⊤ := by
  let G : E1 → EReal := projectiveToricLegendre u
  let G0 : E1 → EReal := projectiveToricLegendre (fun _ : P1 => (0 : EReal))
  let q : E1 → ℝ≥0∞ := fun m => (G m - G0 m).toENNReal
  let p : E1 → ℝ≥0∞ := fun m => (G m).toENNReal
  have hG : Measurable G := measurable_conjugate B _
  have hG0 : Measurable G0 := measurable_conjugate B _
  have hp : Measurable p := EReal.continuous_toENNReal.measurable.comp hG
  have hq : Measurable q := EReal.continuous_toENNReal.measurable.comp (hG.sub hG0)
  have hg0 := (projectiveToric_mem_relativeEInfinity_iff_boundedGrowthClass
    isThetaPSH_projectiveZero zero_invariant).mp
    ⟨isThetaPshPotential_projectiveNativeFS_of_source isThetaPSH_projectiveZero,
      BoundedMongeAmpereEnergy.sameSingularityType_of_bounded zero_bounded zero_bounded⟩
  obtain ⟨a, b, hab⟩ := conjugate_bounds_of_mem_boundedGrowthClass B
    isCompact_projectiveMomentInterval convex_projectiveMomentInterval hg0
  let M : ℝ := |a| + |b|
  let K : ℝ≥0∞ := ENNReal.ofReal M
  have hMb : b ≤ M := by
    change b ≤ |a| + |b|
    linarith [le_abs_self b, abs_nonneg a]
  have hMa : -a ≤ M := by
    change -a ≤ |a| + |b|
    linarith [neg_abs_le a, abs_nonneg b]
  have hK : (∫⁻ _m : E1, K ∂volume.restrict projectiveMomentInterval) < ⊤ := by
    rw [lintegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (by simpa using isCompact_projectiveMomentInterval.measure_lt_top (μ := volume))
  have h0f := legendre_finite_of_bounded isThetaPSH_projectiveZero zero_invariant zero_bounded
  have hbnd : ∀ m ∈ projectiveMomentInterval, p m ≤ q m + K ∧ q m ≤ p m + K := by
    intro m hm
    have h0p : (G0 m).toENNReal ≤ K := by
      apply le_trans (EReal.toENNReal_le_toENNReal
        ((hab m hm).2.trans (EReal.coe_le_coe_iff.mpr hMb)))
      exact le_of_eq (EReal.real_coe_toENNReal M)
    have h0n : (-G0 m).toENNReal ≤ K := by
      have hn := EReal.neg_le_neg_iff.mpr (hab m hm).1
      rw [← EReal.coe_neg] at hn
      apply le_trans (EReal.toENNReal_le_toENNReal
        (hn.trans (EReal.coe_le_coe_iff.mpr hMa)))
      exact le_of_eq (EReal.real_coe_toENNReal M)
    have hcancel : (G m - G0 m) + G0 m = G m := by
      change (G m - projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m) +
        projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m = G m
      rw [h0f m hm]
      exact sub_coe_add_coe _ _
    constructor
    · calc
        p m = ((G m - G0 m) + G0 m).toENNReal := congrArg EReal.toENNReal hcancel.symm
        _ ≤ q m + (G0 m).toENNReal := EReal.toENNReal_add_le
        _ ≤ q m + K := add_le_add le_rfl h0p
    · exact EReal.toENNReal_add_le.trans (add_le_add le_rfl h0n)
  have hb1 : (∫⁻ m, p m ∂volume.restrict projectiveMomentInterval) ≤
      (∫⁻ m, q m ∂volume.restrict projectiveMomentInterval) +
        ∫⁻ _m : E1, K ∂volume.restrict projectiveMomentInterval := by
    rw [← lintegral_add_left hq (fun _ => K)]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem isCompact_projectiveMomentInterval.isClosed.measurableSet]
      with m hm
    exact (hbnd m hm).1
  have hb2 : (∫⁻ m, q m ∂volume.restrict projectiveMomentInterval) ≤
      (∫⁻ m, p m ∂volume.restrict projectiveMomentInterval) +
        ∫⁻ _m : E1, K ∂volume.restrict projectiveMomentInterval := by
    rw [← lintegral_add_left hp (fun _ => K)]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem isCompact_projectiveMomentInterval.isClosed.measurableSet]
      with m hm
    exact (hbnd m hm).2
  change (∫⁻ m, q m ∂volume.restrict projectiveMomentInterval) < ⊤ ↔
    (∫⁻ m, p m ∂volume.restrict projectiveMomentInterval) < ⊤
  constructor
  · intro h
    exact lt_of_le_of_lt hb1 (ENNReal.add_lt_top.mpr ⟨h, hK⟩)
  · intro h
    exact lt_of_le_of_lt hb2 (ENNReal.add_lt_top.mpr ⟨h, hK⟩)

private theorem bot_lt_neg_coe_ennreal_iff (a : ℝ≥0∞) :
    ⊥ < -(a : EReal) ↔ a < ⊤ := by
  constructor
  · intro h
    have h' : (a : EReal) < ⊤ := by simpa using EReal.lt_neg_of_lt_neg h
    exact EReal.coe_ennreal_lt_coe_ennreal_iff.mp h'
  · intro h
    have h' : (a : EReal) < ⊤ := EReal.coe_ennreal_lt_coe_ennreal_iff.mpr h
    have h'' : -(-(a : EReal)) < ⊤ := by simpa using h'
    simpa using EReal.neg_lt_of_neg_lt h''

/-- Original normalized invariant source inputs give the actual native E1
criterion through the genuine extended positive conjugate integral. -/
theorem projectiveToric_mem_relativeFiniteEnergy_iff_legendre_positive {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) (hle : u ≤ fun _ => (0 : EReal)) :
    RelativeFiniteEnergy projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) u isModelPotential_projectiveNativeZero ↔
      (∫⁻ m in projectiveMomentInterval, (projectiveToricLegendre u m).toENNReal) < ⊤ := by
  have hrel : RelativePSH projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) u :=
    ⟨isThetaPshPotential_projectiveNativeFS_of_source hu, hle⟩
  rw [FiniteEnergyCharacterization.relativeFiniteEnergy_iff_bot_lt_energy
    projectiveNativeFSBackground projectiveNativeFSBackground.form
    isModelPotential_projectiveNativeZero zero_bounded hrel,
    ← RelativeDarvasDistance.energy_eq hrel,
    projectiveToric_energy_eq_neg_gap_lintegral_of_nonpos hu hi hle,
    bot_lt_neg_coe_ennreal_iff,
    projectiveToric_gap_lintegral_lt_top_iff_positive_lintegral hu hi]

/-- The source's original convex energy-one class has its actual full-mass
clause produced from native E1, rather than introduced as a convergence field. -/
theorem projectiveToric_mem_relativeFiniteEnergy_iff_energyOneClass {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) (hle : u ≤ fun _ => (0 : EReal)) :
    RelativeFiniteEnergy projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) u isModelPotential_projectiveNativeZero ↔
      projectiveToricCorrectedDescent u ∈ EnergyOneClass B projectiveMomentInterval volume := by
  rw [mem_energyOneClass_iff volume B isCompact_projectiveMomentInterval nonempty_projectiveMomentInterval]
  constructor
  · intro h
    exact ⟨(projectiveToric_mem_relativeFullMassPreceq_iff hu hi).mp
      (preceq_of_relativeFiniteEnergy h).1,
      (projectiveToric_mem_relativeFiniteEnergy_iff_legendre_positive hu hi hle).mp h⟩
  · intro h
    exact (projectiveToric_mem_relativeFiniteEnergy_iff_legendre_positive hu hi hle).mpr h.2

/-- Genuine extended L1 keeps every infinite original conjugate value. The
negative part is internally proved finite from the original proper growth class. -/
theorem projectiveToric_mem_relativeFiniteEnergy_iff_legendre_L1 {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) (hle : u ≤ fun _ => (0 : EReal)) :
    RelativeFiniteEnergy projectiveNativeFSBackground.form
      (fun _ : P1 => (0 : EReal)) u isModelPotential_projectiveNativeZero ↔
      (∫⁻ m in projectiveMomentInterval,
        (projectiveToricLegendre u m).toENNReal + (-projectiveToricLegendre u m).toENNReal) < ⊤ := by
  rw [projectiveToric_mem_relativeFiniteEnergy_iff_legendre_positive hu hi hle]
  have hm : Measurable (fun m => (projectiveToricLegendre u m).toENNReal) :=
    EReal.continuous_toENNReal.measurable.comp (measurable_conjugate B _)
  rw [lintegral_add_left hm]
  have hn := lintegral_neg_conjugate_lt_top_of_mem_growthClass volume B
    isCompact_projectiveMomentInterval nonempty_projectiveMomentInterval
    (projectiveToricCorrectedDescent_mem_growthClass hu hi)
  exact ⟨fun h => ENNReal.add_lt_top.mpr ⟨h, hn⟩,
    fun h => (ENNReal.add_lt_top.mp h).1⟩

end SGPT.Toric
