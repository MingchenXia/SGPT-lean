import SGPT.Toric.ProjectiveScalarSmoothMeasure
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCalculus
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCanonicalTraceMeasure

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set Filter MeasureTheory TopologicalSpace SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorDecreasing
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorContinuity
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorLocality
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothTraceMeasure
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCanonicalTraceMeasure
open scoped Topology ContDiff Distributions ENNReal

/-- The same actual nonzero model domain, for every finite convex profile. -/
def scalarPuncturedBTDomain : Opens (ComplexModel 1) :=
  ⟨complexTorus 1, isOpen_complexTorus 1⟩

local notation "D" => scalarPuncturedBTDomain

theorem continuousOn_scalarPuncturedProfile {h : ℝ → ℝ}
    (hc : ConvexOn ℝ univ h) : ContinuousOn (scalarPuncturedProfile h) D := by
  have hnorm : Continuous (fun z : ComplexModel 1 => ‖z 0‖ ^ 2) := by
    simpa only [projectiveModelEquiv_symm_apply, ← Complex.sq_norm]
      using contDiff_projectiveModel_normSq.continuous
  have hlog : ContinuousOn (fun z : ComplexModel 1 => Real.log (‖z 0‖ ^ 2)) D :=
    hnorm.continuousOn.log (fun z hz => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hz 0)))
  have heq : scalarPuncturedProfile h = (fun z => h (Real.log (‖z 0‖ ^ 2))) := by
    funext z
    rw [scalarPuncturedProfile, tropicalization_apply_eq_log_norm_sq]
  rw [heq]
  exact (continuousOn_univ.mp (hc.continuousOn isOpen_univ)).comp_continuousOn hlog

theorem isLocallyBoundedPshOn_scalarPuncturedProfile {h : ℝ → ℝ}
    (hc : ConvexOn ℝ univ h) : IsLocallyBoundedPshOn D (scalarPuncturedProfile h) :=
  LocalBedfordTaylorCalculus.isLocallyBoundedPshOn_of_continuousOn
    (plurisubharmonicOn_scalarPuncturedProfile hc)
    (continuousOn_scalarPuncturedProfile hc)

theorem tendstoLocallyUniformlyOn_scalarPuncturedProfile_smoothApprox {h : ℝ → ℝ}
    (hc : ConvexOn ℝ univ h) :
    TendstoLocallyUniformlyOn
      (fun j => scalarPuncturedProfile (finiteConvexSmoothApprox volume h j))
      (scalarPuncturedProfile h) atTop D := by
  have hreal : TendstoLocallyUniformlyOn (finiteConvexSmoothApprox volume h) h atTop univ := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mpr
    intro K _ hK
    exact tendstoUniformlyOn_finiteConvexSmoothApprox volume hc hK
  have hnorm : Continuous (fun z : ComplexModel 1 => ‖z 0‖ ^ 2) := by
    simpa only [projectiveModelEquiv_symm_apply, ← Complex.sq_norm]
      using contDiff_projectiveModel_normSq.continuous
  have hlog : ContinuousOn (fun z : ComplexModel 1 => Real.log (‖z 0‖ ^ 2)) D :=
    hnorm.continuousOn.log (fun z hz => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hz 0)))
  have ht := hreal.comp (fun z : ComplexModel 1 => Real.log (‖z 0‖ ^ 2))
    (fun _ _ => mem_univ _) hlog
  have heq (f : ℝ → ℝ) : scalarPuncturedProfile f =
      (fun z : ComplexModel 1 => f (Real.log (‖z 0‖ ^ 2))) := by
    funext z
    rw [scalarPuncturedProfile, tropicalization_apply_eq_log_norm_sq]
  simpa only [heq, Function.comp_def] using ht

/-- The independently constructed full real Alexandrov radial map. -/
def scalarAlexandrovRadialMeasure (h : ℝ → ℝ) : Measure ℂ :=
  Measure.map logLogRadialPoint
    ((alexandrovMeasure scalarPairing volume (fun x => (h x : EReal))).prod
      logLogAngularMeasure)

theorem exists_scalarRadial_compact_window {K : Set ℂ} (hK : IsCompact K)
    (hzero : (0 : ℂ) ∉ K) :
    ∃ a b : ℝ, ∀ x t : ℝ, logLogRadialPoint (x, t) ∈ K → x ∈ Icc a b := by
  obtain ⟨ε, hε, hlow⟩ := hK.exists_forall_le' continuous_norm.continuousOn
    (fun z hz => norm_pos_iff.mpr (fun he => hzero (he ▸ hz)))
  obtain ⟨R, hR, hhigh⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨2 * Real.log ε, 2 * Real.log R, ?_⟩
  intro x t hp
  have hlo := hlow (logLogRadialPoint (x, t)) hp
  have hhi := hhigh (logLogRadialPoint (x, t)) hp
  rw [norm_logLogRadialPoint] at hlo hhi
  have hloglo := (Real.log_le_iff_le_exp hε).2 hlo
  have hloghi := (Real.le_log_iff_exp_le hR).2 hhi
  exact ⟨by linarith, by linarith⟩

theorem scalarAlexandrovRadialMeasure_origin (h : ℝ → ℝ) :
    scalarAlexandrovRadialMeasure h {0} = 0 := by
  rw [scalarAlexandrovRadialMeasure,
    Measure.map_apply continuous_logLogRadialPoint.measurable (measurableSet_singleton 0)]
  have hempty : logLogRadialPoint ⁻¹' ({0} : Set ℂ) = ∅ := by
    ext p
    simp [logLogRadialPoint_ne_zero p]
  rw [hempty, measure_empty]

theorem scalarAlexandrovRadialMeasure_finiteOn_puncturedCompacts {h : ℝ → ℝ}
    (hc : ConvexOn ℝ univ h) {K : Set ℂ} (hK : IsCompact K)
    (hzero : (0 : ℂ) ∉ K) : scalarAlexandrovRadialMeasure h K < ⊤ := by
  let μ := alexandrovMeasure scalarPairing volume (fun x => (h x : EReal))
  let : IsLocallyFiniteMeasure μ := isLocallyFiniteMeasure_alexandrovMeasure_coe scalarPairing hc
  obtain ⟨a, b, hwindow⟩ := exists_scalarRadial_compact_window hK hzero
  have hfinite : (μ.prod logLogAngularMeasure) (Icc a b ×ˢ (univ : Set ℝ)) < ⊤ := by
    rw [Measure.prod_prod, logLogAngularMeasure_univ, mul_one]
    exact isCompact_Icc.measure_lt_top
  rw [scalarAlexandrovRadialMeasure,
    Measure.map_apply continuous_logLogRadialPoint.measurable hK.isClosed.measurableSet]
  apply lt_of_le_of_lt (measure_mono ?_) hfinite
  intro p hp
  exact ⟨hwindow p.1 p.2 hp, mem_univ p.2⟩

/-- The actual canonical real-tuple BT construction, independently of the radial map. -/
def scalarCanonicalBTMeasure {h : ℝ → ℝ} (hc : ConvexOn ℝ univ h) : Measure (ComplexModel 1) :=
  canonicalMixedBedfordTaylorMeasure D (fun _ : Fin 1 => scalarPuncturedProfile h)
    (fun _ => isLocallyBoundedPshOn_scalarPuncturedProfile hc)

theorem tendsto_integral_scalarCanonicalBT_smoothApprox {h : ℝ → ℝ}
    (hc : ConvexOn ℝ univ h) {g : ComplexModel 1 → ℝ}
    (hg : Continuous g) (hK : HasCompactSupport g) (hU : tsupport g ⊆ D) :
    Tendsto (fun j => ∫ z, g z ∂scalarPuncturedSmoothMeasure
      (convexOn_finiteConvexSmoothApprox volume hc j)
      (contDiff_finiteConvexSmoothApprox volume hc j)) atTop
      (𝓝 (∫ z, g z ∂scalarCanonicalBTMeasure hc)) := by
  let v : ℕ → Fin 1 → ComplexModel 1 → ℝ := fun j _ =>
    scalarPuncturedProfile (finiteConvexSmoothApprox volume h j)
  let v0 : Fin 1 → ComplexModel 1 → ℝ := fun _ => scalarPuncturedProfile h
  have hv (j : ℕ) (i : Fin 1) : IsLocallyBoundedPshOn D (v j i) :=
    isLocallyBoundedPshOn_of_isSmoothPshOn (isSmoothPshOn_of_psh
      (contDiffOn_scalarPuncturedProfile (contDiff_finiteConvexSmoothApprox volume hc j))
      (plurisubharmonicOn_scalarPuncturedProfile (convexOn_finiteConvexSmoothApprox volume hc j)))
  let T := oneCurrentOf (U := D) (Nat.zero_add 1)
  have hP (j : ℕ) : IsPositive (btProduct 1 0 (v j) T) :=
    (isPositive_btProduct 1 0 (v j) T (isPositive_oneCurrentOf _)
      (isClosedAny_oneCurrentOf _) (hv j)).1
  have hP0 : IsPositive (btProduct 1 0 v0 T) :=
    (isPositive_btProduct 1 0 v0 T (isPositive_oneCurrentOf _)
      (isClosedAny_oneCurrentOf _) (fun _ => isLocallyBoundedPshOn_scalarPuncturedProfile hc)).1
  have hw := weakTendsto_btProduct 1 0 v v0 (fun _ => T) T
    (fun _ => isPositive_oneCurrentOf _) (fun _ => isClosedAny_oneCurrentOf _)
    (by intro _ _; exact tendsto_const_nhds) hv
    (fun _ => continuousOn_scalarPuncturedProfile hc)
    (fun _ => tendstoLocallyUniformlyOn_scalarPuncturedProfile_smoothApprox hc)
  have hl := tendsto_integral_traceMeasure_of_weakTendsto hP hP0 hw hg hK hU
  change Tendsto (fun j => ∫ z, g z ∂recursiveMixedTraceMeasure D (v j) (hv j)) atTop
    (𝓝 (∫ z, g z ∂recursiveMixedTraceMeasure D v0
      (fun _ => isLocallyBoundedPshOn_scalarPuncturedProfile hc))) at hl
  have es (j : ℕ) : recursiveMixedTraceMeasure D (v j) (hv j) =
      scalarPuncturedSmoothMeasure (convexOn_finiteConvexSmoothApprox volume hc j)
        (contDiff_finiteConvexSmoothApprox volume hc j) := by
    exact recursiveMixedTraceMeasure_eq_smoothMixedMeasure
      (fun _ => contDiffOn_scalarPuncturedProfile (contDiff_finiteConvexSmoothApprox volume hc j))
      (fun _ => plurisubharmonicOn_scalarPuncturedProfile (convexOn_finiteConvexSmoothApprox volume hc j))
  have et : scalarCanonicalBTMeasure hc = recursiveMixedTraceMeasure D v0
      (fun _ => isLocallyBoundedPshOn_scalarPuncturedProfile hc) :=
    canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure
      (fun _ => isLocallyBoundedPshOn_scalarPuncturedProfile hc)
  simp_rw [es, ← et] at hl
  exact hl

theorem integral_scalarCanonicalBT_eq_radial {h : ℝ → ℝ}
    (hc : ConvexOn ℝ univ h) {g : ComplexModel 1 → ℝ}
    (hg : Continuous g) (hK : HasCompactSupport g) (hU : tsupport g ⊆ D) :
    (∫ z, g z ∂scalarCanonicalBTMeasure hc) =
      ∫ z, g (projectiveModelEquiv z) ∂scalarAlexandrovRadialMeasure h := by
  let η : ℂ → ℝ := g ∘ projectiveModelEquiv
  have hη : Continuous η := hg.comp projectiveModelEquiv.continuous
  have hηK : HasCompactSupport η := hK.comp_homeomorph projectiveModelEquiv.toHomeomorph
  have hzero : (0 : ℂ) ∉ tsupport η := by
    intro hz
    have hmem := hU (tsupport_comp_subset_preimage g projectiveModelEquiv.continuous hz)
    have hne := hmem (0 : Fin 1)
    simp only [map_zero, PiLp.zero_apply] at hne
    exact hne rfl
  have heq (j : ℕ) :
      (∫ z, g z ∂scalarPuncturedSmoothMeasure
        (convexOn_finiteConvexSmoothApprox volume hc j)
        (contDiff_finiteConvexSmoothApprox volume hc j)) =
      ∫ z, η z ∂scalarAlexandrovRadialMeasure (finiteConvexSmoothApprox volume h j) := by
    simpa only [η, scalarAlexandrovRadialMeasure, Function.comp_def, projectiveModelEquiv.apply_symm_apply]
      using integral_scalarPuncturedSmoothMeasure_eq_radial
        (convexOn_finiteConvexSmoothApprox volume hc j)
        (contDiff_finiteConvexSmoothApprox volume hc j) hη hηK hzero
  have hr := tendsto_integral_radialMap_of_convex_compact_convergence hc
    (convexOn_finiteConvexSmoothApprox volume hc)
    (fun _ hcomp => tendstoUniformlyOn_finiteConvexSmoothApprox volume hc hcomp)
    hη hηK hzero
  have hb := tendsto_integral_scalarCanonicalBT_smoothApprox hc hg hK hU
  simp_rw [heq] at hb
  exact tendsto_nhds_unique hb hr

theorem scalarCanonicalBT_eq_map_radial {h : ℝ → ℝ} (hc : ConvexOn ℝ univ h) :
    scalarCanonicalBTMeasure hc = Measure.map projectiveModelEquiv
      (scalarAlexandrovRadialMeasure h) := by
  have hpre : projectiveModelEquiv ⁻¹' (D : Set (ComplexModel 1))ᶜ = ({0} : Set ℂ) := by
    ext z
    change (¬ ∀ i : Fin 1, projectiveModelEquiv z i ≠ 0) ↔ z = 0
    simp only [Fin.forall_fin_one, projectiveModelEquiv_apply_zero, not_not]
  have hν : (Measure.map projectiveModelEquiv (scalarAlexandrovRadialMeasure h))
      (D : Set (ComplexModel 1))ᶜ = 0 := by
    rw [Measure.map_apply projectiveModelEquiv.continuous.measurable
      scalarPuncturedBTDomain.isOpen.measurableSet.compl, hpre,
      scalarAlexandrovRadialMeasure_origin]
  have hνfinite (K : Set (ComplexModel 1)) (hK : IsCompact K) (hKU : K ⊆ D) :
      (Measure.map projectiveModelEquiv (scalarAlexandrovRadialMeasure h)) K < ⊤ := by
    rw [Measure.map_apply projectiveModelEquiv.continuous.measurable hK.isClosed.measurableSet]
    apply scalarAlexandrovRadialMeasure_finiteOn_puncturedCompacts hc
      (projectiveModelEquiv.toHomeomorph.isCompact_preimage.mpr hK)
    intro hz
    have hne := hKU hz (0 : Fin 1)
    exact hne (by simp)
  apply eq_of_forall_testFunction_integral_eq (U := D)
    (canonicalMixedBedfordTaylorMeasure_compl _ _ _) hν
    (fun K hK hKU => canonicalMixedBedfordTaylorMeasure_finiteOnCompacts
      (fun _ => isLocallyBoundedPshOn_scalarPuncturedProfile hc) hK hKU) hνfinite
  intro φ
  rw [integral_map projectiveModelEquiv.continuous.aemeasurable
    φ.continuous.aestronglyMeasurable]
  exact integral_scalarCanonicalBT_eq_radial hc φ.continuous φ.hasCompactSupport
    φ.tsupport_subset

end SGPT.Toric
