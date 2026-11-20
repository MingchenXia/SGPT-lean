import SGPT.Toric.ProjectiveToricFiniteEnergy
import SGPT.Toric.ProjectiveToricRooftop
import SGPT.Foundations.Analysis.FirstPass.ThetaPshEnvelopes
import SGPT.Foundations.Analysis.Pending.RelativePreceqClasses
import SGPT.Okounkov.LegendreEnergyEquality

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.RelativePreceqClasses
open scoped Topology ContDiff RealInnerProductSpace

local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)
local notation "E1" => EuclideanSpace ℝ (Fin 1)
local notation "θ" => projectiveNativeFSBackground.form

/-- The actual original preferred projective atlas and native theta record agree. -/
theorem isThetaPSH_projectiveFS_iff_nativeThetaPotential {u : P1 → EReal} :
    projectiveLineAtlas.IsThetaPSH projectiveFSForm u ↔
      IsThetaPshPotential projectiveNativeFSBackground.form.val u := by
  constructor
  · exact isThetaPshPotential_projectiveNativeFS_of_source
  · intro hu
    apply isThetaPSH_of_chart_corrected (fun _ => projectiveFSPotential)
    · intro i
      exact contDiff_projectiveFSPotential.contDiffOn
    · intro i z hz
      rfl
    · intro i
      let e := projectiveNativeChart i
      have hρ : IsSmoothLocalPotential projectiveNativeFSBackground.form.val e e.val.target projectiveFSPotential :=
        ⟨e.val.open_target, Subset.rfl, contDiff_projectiveFSPotential.contDiffOn,
          fun _ _ => rfl⟩
      have hF : ∀ w ∈ ({u} : Set (P1 → EReal)), IsThetaPshPotential projectiveNativeFSBackground.form.val w := by
        intro w hw
        simpa only [mem_singleton_iff.mp hw] using hu
      have hmem : (fun z => u (e.val.symm z) + (projectiveFSPotential z : EReal)) ∈
          chartCorrectedFamily ({u} : Set (P1 → EReal)) e projectiveFSPotential :=
        ⟨u, mem_singleton u, rfl⟩
      exact chartCorrectedFamily_plurisubharmonicOn hF e hρ _ hmem
    · exact hu.quasiPshPotential.1.ne_top
    · intro x _ O hO hx
      obtain ⟨y, hyO, hyfinite⟩ := hu.2 x O hO hx
      exact ⟨y, ⟨mem_univ y, hyO⟩, hyfinite⟩

/-- Genuine finite-energy closure manufactures the same whole original raw rooftop. -/
theorem projectiveToric_finiteEnergy_rooftop_readback {u v : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hv : projectiveLineAtlas.IsThetaPSH projectiveFSForm v)
    (hiu : ProjectiveCircleInvariant u) (hiv : ProjectiveCircleInvariant v)
    (hEu : RelativeFiniteEnergyPreceq θ (fun _ : P1 => (0 : EReal)) u
      isModelPotential_projectiveNativeZero)
    (hEv : RelativeFiniteEnergyPreceq θ (fun _ : P1 => (0 : EReal)) v
      isModelPotential_projectiveNativeZero) :
    let R := RelativeDarvasDistance.rooftop θ u v
    RelativeFiniteEnergyPreceq θ (fun _ : P1 => (0 : EReal)) R
      isModelPotential_projectiveNativeZero ∧
    projectiveLineAtlas.IsThetaPSH projectiveFSForm R ∧
    ProjectiveCircleInvariant R ∧ R = thetaRooftop projectiveFSForm u v ∧
    projectiveToricLegendre R =
      fun m => max (projectiveToricLegendre u m) (projectiveToricLegendre v m) := by
  let R := RelativeDarvasDistance.rooftop θ u v
  let R0 := thetaRooftop projectiveFSForm u v
  have hER := relativeFiniteEnergyPreceq_rooftop projectiveNativeFSBackground hEu hEv
  have hRn : IsThetaPshPotential projectiveNativeFSBackground.form.val R :=
    hER.1.relativePSHPreceq.1
  have hRs : projectiveLineAtlas.IsThetaPSH projectiveFSForm R :=
    isThetaPSH_projectiveFS_iff_nativeThetaPotential.mpr hRn
  have hun := isThetaPshPotential_projectiveNativeFS_of_source hu
  have hvn := isThetaPshPotential_projectiveNativeFS_of_source hv
  have hRleft := RelativeDarvasDistance.rooftop_le_left hun hvn
  have hRright := RelativeDarvasDistance.rooftop_le_right hun hvn
  have hR0 : R ≤ R0 := le_thetaRooftop hRs hRleft hRright
  have hne : R0 ≠ ⊥ := by
    intro hbot
    obtain ⟨y, _hy, hfin⟩ := hRn.2 projectiveOrigin univ isOpen_univ (mem_univ _)
    apply hfin
    apply le_bot_iff.mp
    simpa only [hbot, Pi.bot_apply] using hR0 y
  have hR0s := isThetaPSH_projective_thetaRooftop hu hv hne
  have hR0n := isThetaPshPotential_projectiveNativeFS_of_source hR0s
  have hback : R0 ≤ R := (RelativeDarvasDistance.le_rooftop_iff hun hvn hR0n).mpr
    ⟨thetaRooftop_le_left projectiveFSForm u v, thetaRooftop_le_right projectiveFSForm u v⟩
  have heq : R = R0 := le_antisymm hR0 hback
  refine ⟨hER, hRs, ?_, heq, ?_⟩
  · change ProjectiveCircleInvariant R
    rw [heq]
    exact projectiveCircleInvariant_thetaRooftop hiu hiv
  · change projectiveToricLegendre R = _
    rw [heq]
    exact projectiveToricLegendre_thetaRooftop hu hv hiu hiv hne

private theorem darvas_reference_legendre_integrable :
    (∀ m ∈ projectiveMomentInterval,
      projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m ≠ ⊤ ∧
      projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m ≠ ⊥) ∧
    IntegrableOn (fun m => (projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m).toReal)
      projectiveMomentInterval volume := by
  let : IsFiniteMeasure (volume.restrict projectiveMomentInterval) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_projectiveMomentInterval.measure_lt_top⟩
  have hi0 : ProjectiveCircleInvariant (fun _ : P1 => (0 : EReal)) := fun _ _ _ => rfl
  have hf0 := (projectiveToric_mem_relativeEInfinity_iff_boundedGrowthClass
    isThetaPSH_projectiveZero hi0).mp
    ⟨isModelPotential_projectiveNativeZero.plurisubharmonic, SameSingularityTypeOn.refl _ _⟩
  obtain ⟨a, b, hab⟩ := conjugate_bounds_of_mem_boundedGrowthClass (innerₗ E1)
    isCompact_projectiveMomentInterval convex_projectiveMomentInterval hf0
  have hfin (m : E1) (hm : m ∈ projectiveMomentInterval) :
      projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m ≠ ⊤ ∧
      projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m ≠ ⊥ :=
    ⟨ne_top_of_le_ne_top (EReal.coe_ne_top b) (hab m hm).2,
      ne_bot_of_le_ne_bot (EReal.coe_ne_bot a) (hab m hm).1⟩
  refine ⟨hfin, (integrable_const (|a| + |b|)).mono' ?_ ?_⟩
  · exact (measurable_conjugate (innerₗ E1)
      (projectiveToricCorrectedDescent (fun _ : P1 => (0 : EReal)))).ereal_toReal.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem isCompact_projectiveMomentInterval.measurableSet] with m hm
    have hh := hab m hm
    change (a : EReal) ≤ projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m ∧
      projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m ≤ (b : EReal) at hh
    rw [← EReal.coe_toReal (hfin m hm).1 (hfin m hm).2] at hh
    have hlow := EReal.coe_le_coe_iff.mp hh.1
    have hhigh := EReal.coe_le_coe_iff.mp hh.2
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · have ha := neg_abs_le a
      have hb := abs_nonneg b
      linarith
    · have ha := abs_nonneg a
      have hb := le_abs_self b
      linarith

private theorem darvas_signedIntegral_eq_real {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (g : A → EReal) (hg : Measurable g)
    (hfin : ∀ᵐ x ∂μ, g x ≠ ⊤ ∧ g x ≠ ⊥)
    (hI : Integrable (fun x => (g x).toReal) μ) :
    extendedSignedIntegral μ g = ((∫ x, (g x).toReal ∂μ : ℝ) : EReal) := by
  apply SGPT.Okounkov.signedIntegral_eq_coe_integral_of_finite_parts μ g hg hfin
  · have he : (∫⁻ x, (g x).toENNReal ∂μ) =
        ∫⁻ x, ENNReal.ofReal (g x).toReal ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hfin] with x hx
      rw [← EReal.coe_toReal hx.1 hx.2, EReal.toReal_coe, EReal.real_coe_toENNReal]
    rw [he]
    exact (lintegral_ofReal_le_lintegral_enorm _).trans_lt hI.2
  · have he : (∫⁻ x, (-g x).toENNReal ∂μ) =
        ∫⁻ x, ENNReal.ofReal (-(g x).toReal) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hfin] with x hx
      rw [← EReal.coe_toReal hx.1 hx.2]
      simp only [← EReal.coe_neg, EReal.real_coe_toENNReal, EReal.toReal_coe]
    rw [he]
    exact (lintegral_ofReal_le_lintegral_enorm _).trans_lt hI.neg.2

private theorem darvas_energy_eq_integral {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u)
    (hE : RelativeFiniteEnergyPreceq θ (fun _ : P1 => (0 : EReal)) u
      isModelPotential_projectiveNativeZero) :
    (RelativeDarvasDistance.energy θ (fun _ : P1 => (0 : EReal))
      isModelPotential_projectiveNativeZero u).toReal =
      ∫ m in projectiveMomentInterval,
        (projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m).toReal -
          (projectiveToricLegendre u m).toReal ∂volume := by
  obtain ⟨hufin, huI⟩ := (projectiveToric_mem_relativeFiniteEnergyPreceq_iff_legendre_integrable hu hi).mp hE
  obtain ⟨h0fin, h0I⟩ := darvas_reference_legendre_integrable
  let g := fun m => projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m -
    projectiveToricLegendre u m
  have hg : Measurable g := (measurable_conjugate (innerₗ E1)
    (projectiveToricCorrectedDescent (fun _ : P1 => (0 : EReal)))).sub
      (measurable_conjugate (innerₗ E1) (projectiveToricCorrectedDescent u))
  have he : ∀ᵐ m ∂volume.restrict projectiveMomentInterval,
      g m = (((projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m).toReal -
        (projectiveToricLegendre u m).toReal : ℝ) : EReal) := by
    filter_upwards [hufin, ae_restrict_mem isCompact_projectiveMomentInterval.measurableSet] with m hm hp
    dsimp only [g]
    rw [← EReal.coe_toReal (h0fin m hp).1 (h0fin m hp).2,
      ← EReal.coe_toReal hm.1 hm.2, ← EReal.coe_sub]
    simp only [EReal.toReal_coe]
  have hfin : ∀ᵐ m ∂volume.restrict projectiveMomentInterval, g m ≠ ⊤ ∧ g m ≠ ⊥ := by
    filter_upwards [he] with m hm
    rw [hm]
    exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩
  have heReal : ∀ᵐ m ∂volume.restrict projectiveMomentInterval,
      (g m).toReal = (projectiveToricLegendre (fun _ : P1 => (0 : EReal)) m).toReal -
        (projectiveToricLegendre u m).toReal := by
    filter_upwards [he] with m hm
    rw [hm, EReal.toReal_coe]
  have hI : Integrable (fun m => (g m).toReal) (volume.restrict projectiveMomentInterval) :=
    (h0I.sub huI).congr (heReal.mono (fun _ h => h.symm))
  rw [projectiveToricEnergy_eq_extendedLegendreIntegral hu hi,
    darvas_signedIntegral_eq_real _ g hg hfin hI, EReal.toReal_coe]
  exact integral_congr_ae heReal

/-- The actual P1 Darvas distance is the original Legendre integral, with finite-AE/L1 readback. -/
theorem projectiveToric_relativeD1_eq_legendreIntegral {u v : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hv : projectiveLineAtlas.IsThetaPSH projectiveFSForm v)
    (hiu : ProjectiveCircleInvariant u) (hiv : ProjectiveCircleInvariant v)
    (hEu : RelativeFiniteEnergyPreceq θ (fun _ : P1 => (0 : EReal)) u
      isModelPotential_projectiveNativeZero)
    (hEv : RelativeFiniteEnergyPreceq θ (fun _ : P1 => (0 : EReal)) v
      isModelPotential_projectiveNativeZero) :
    let g := fun m => (2 : EReal) * max (projectiveToricLegendre u m)
      (projectiveToricLegendre v m) - projectiveToricLegendre u m - projectiveToricLegendre v m
    RelativeDarvasDistance.relativeD1 θ (fun _ : P1 => (0 : EReal))
      isModelPotential_projectiveNativeZero u v =
        ∫ m in projectiveMomentInterval, (g m).toReal ∂volume ∧
    (∀ᵐ m ∂volume.restrict projectiveMomentInterval, g m ≠ ⊤ ∧ g m ≠ ⊥) ∧
    IntegrableOn (fun m => (g m).toReal) projectiveMomentInterval volume := by
  let R := RelativeDarvasDistance.rooftop θ u v
  let g := fun m => (2 : EReal) * max (projectiveToricLegendre u m)
    (projectiveToricLegendre v m) - projectiveToricLegendre u m - projectiveToricLegendre v m
  obtain ⟨hER, hRs, hiR, _heqR, hGR⟩ :=
    projectiveToric_finiteEnergy_rooftop_readback hu hv hiu hiv hEu hEv
  obtain ⟨hufin, huI⟩ := (projectiveToric_mem_relativeFiniteEnergyPreceq_iff_legendre_integrable hu hiu).mp hEu
  obtain ⟨hvfin, hvI⟩ := (projectiveToric_mem_relativeFiniteEnergyPreceq_iff_legendre_integrable hv hiv).mp hEv
  obtain ⟨hRfin, hRI⟩ := (projectiveToric_mem_relativeFiniteEnergyPreceq_iff_legendre_integrable hRs hiR).mp hER
  have he : ∀ᵐ m ∂volume.restrict projectiveMomentInterval,
      g m = (((2 * (projectiveToricLegendre R m).toReal -
        (projectiveToricLegendre u m).toReal - (projectiveToricLegendre v m).toReal : ℝ)) : EReal) := by
    filter_upwards [hufin, hvfin, hRfin] with m hum hvm hRm
    dsimp only [g]
    rw [← congrFun hGR m, ← EReal.coe_toReal hRm.1 hRm.2,
      ← EReal.coe_toReal hum.1 hum.2, ← EReal.coe_toReal hvm.1 hvm.2]
    change ((2 : ℝ) : EReal) * _ - _ - _ = _
    rw [← EReal.coe_mul, ← EReal.coe_sub, ← EReal.coe_sub]
    simp only [EReal.toReal_coe]
  have heReal : ∀ᵐ m ∂volume.restrict projectiveMomentInterval,
      (g m).toReal = 2 * (projectiveToricLegendre R m).toReal -
        (projectiveToricLegendre u m).toReal - (projectiveToricLegendre v m).toReal := by
    filter_upwards [he] with m hm
    rw [hm, EReal.toReal_coe]
  have hI : Integrable (fun m => (g m).toReal) (volume.restrict projectiveMomentInterval) :=
    ((hRI.const_mul 2).sub huI |>.sub hvI).congr (heReal.mono (fun _ h => h.symm))
  have hlinear : (∫ m in projectiveMomentInterval,
      2 * (projectiveToricLegendre R m).toReal -
        (projectiveToricLegendre u m).toReal - (projectiveToricLegendre v m).toReal ∂volume) =
      2 * (∫ m in projectiveMomentInterval, (projectiveToricLegendre R m).toReal ∂volume) -
        (∫ m in projectiveMomentInterval, (projectiveToricLegendre u m).toReal ∂volume) -
        (∫ m in projectiveMomentInterval, (projectiveToricLegendre v m).toReal ∂volume) := by
    calc
      _ = (∫ m in projectiveMomentInterval,
          2 * (projectiveToricLegendre R m).toReal - (projectiveToricLegendre u m).toReal ∂volume) -
          (∫ m in projectiveMomentInterval, (projectiveToricLegendre v m).toReal ∂volume) :=
        integral_sub ((hRI.const_mul 2).sub huI) hvI
      _ = _ := by
        rw [integral_sub (hRI.const_mul 2) huI, integral_const_mul]
  refine ⟨?_, ?_, hI⟩
  · obtain ⟨_h0fin, h0I⟩ := darvas_reference_legendre_integrable
    have hUE := (darvas_energy_eq_integral hu hiu hEu).trans (integral_sub h0I huI)
    have hVE := (darvas_energy_eq_integral hv hiv hEv).trans (integral_sub h0I hvI)
    have hRE := (darvas_energy_eq_integral hRs hiR hER).trans (integral_sub h0I hRI)
    rw [RelativeDarvasDistance.relativeD1, hUE, hVE, hRE, integral_congr_ae heReal, hlinear]
    ring
  · filter_upwards [he] with m hm
    change g m ≠ ⊤ ∧ g m ≠ ⊥
    rw [hm]
    exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩

end SGPT.Toric
