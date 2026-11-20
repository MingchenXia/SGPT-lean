import SGPT.Foundations.Analysis.Pending.SingularBalayageMaximalLimit
import SGPT.Foundations.Analysis.Pending.DecreasingTruncationLimit
import SGPT.Foundations.Analysis.Pending.BedfordTaylorFixedWeight
import Mathlib.Topology.Compactness.Lindelof

set_option autoImplicit false

/-! # Actual ordinary boundary maximality implies actual non-pluripolar Monge--Ampere vanishing

This independently proved polydisk-balayage adaptation reuses genuine decreasing
non-pluripolar semicontinuity. No singular strict locus is treated as ordinary open.
-/

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularMaximalNonpluripolarZero

open FirstPass FirstPass.MongeAmpere BedfordTaylor SingularBalayageDataOrder
  SingularBalayageMaximalLimit SingularPerronBoundaryMaximality MongeAmpere

noncomputable section

variable {n : ℕ} {Ω : Opens (ComplexModel n)}

/-- The actual canonical non-pluripolar measure of each genuine truncation balayage on its actual polydisk is zero. -/
theorem truncationLimitMeasure_balayage_eq_zero (hn : 0 < n)
    {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u Ω)
    {c : ComplexModel n} {r : ℝ} (hr : r ≠ 0)
    (hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n))) (j : ℕ) :
    truncationLimitMeasure (scaledPolydiskOpens c r)
      (fun z => (scaledPolydiskBalayage c r (truncationReal u j) z : EReal))
      ((isLocallyBoundedPshOn_balayage_truncation hn hu hr hPΩ j).1.mono
        (fun _ hz => hPΩ (image_mono unitPolydisk_subset_closedUnitPolydisk
          ((mem_scaledPolydisk_iff hr).mpr hz)))) = 0 := by
  have hP : scaledPolydiskOpens c r ≤ Ω := by
    intro z hz
    exact hPΩ (image_mono unitPolydisk_subset_closedUnitPolydisk
      ((mem_scaledPolydisk_iff hr).mpr hz))
  have hb := BedfordTaylor.IsLocallyBoundedPshOn.mono_opens
    (isLocallyBoundedPshOn_balayage_truncation hn hu hr hPΩ j) hP
  rw [truncationLimitMeasure_eq_canonical hb]
  exact eq_zero_of_isBTLimit_scaledPolydiskBalayage hn
    (truncationReal_isLocallyBoundedPshOn hu j) hr hPΩ
    (isBTLimit_canonicalBedfordTaylorMeasure hb)

/-- Genuine decreasing non-pluripolar semicontinuity transfers the actual zero balayage masses to an ordinary maximal singular datum. -/
theorem truncationLimitMeasure_scaledPolydisk_eq_zero (hn : 0 < n)
    {u : ComplexModel n → EReal} (hu : IsBoundaryMaximalPshOn (Ω : Set (ComplexModel n)) u)
    {c : ComplexModel n} {r : ℝ} (hr : r ≠ 0)
    (hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n))) :
    truncationLimitMeasure Ω u hu.2.1 (scaledPolydisk c r) = 0 := by
  have hP : scaledPolydiskOpens c r ≤ Ω := by
    intro z hz
    exact hPΩ (image_mono unitPolydisk_subset_closedUnitPolydisk
      ((mem_scaledPolydisk_iff hr).mpr hz))
  have hv : ∀ j, PlurisubharmonicOn
      (fun z => (scaledPolydiskBalayage c r (truncationReal u j) z : EReal))
      (scaledPolydiskOpens c r) :=
    fun j => (isLocallyBoundedPshOn_balayage_truncation hn hu.2.1 hr hPΩ j).1.mono hP
  have hle := DecreasingTruncationLimit.truncationLimitMeasure_le_liminf_of_antitone hv
    (fun z hz i j hij => EReal.coe_le_coe_iff.mpr
      (scaledPolydiskBalayage_truncation_antitone hn hu.2.1 hr hPΩ (hP hz) hij))
    (hu.2.1.mono hP)
    (fun z hz => tendsto_balayage_of_boundaryMaximal hn hu hr hPΩ (hP hz))
    (scaledPolydiskOpens c r).isOpen (Subset.rfl)
  have hzero : ∀ j, truncationLimitMeasure (scaledPolydiskOpens c r)
      (fun z => (scaledPolydiskBalayage c r (truncationReal u j) z : EReal))
      (hv j) = 0 := fun j => truncationLimitMeasure_balayage_eq_zero hn hu.2.1 hr hPΩ j
  simp only [hzero] at hle
  have hlocal : truncationLimitMeasure (scaledPolydiskOpens c r) u
      (hu.2.1.mono hP) (scaledPolydiskOpens c r) = 0 := by simpa using hle
  rw [← truncationLimitMeasure_restrict_open hP hu.2.1 (hu.2.1.mono hP),
    Measure.restrict_apply (scaledPolydiskOpens c r).isOpen.measurableSet, inter_self,
    coe_scaledPolydiskOpens hr] at hlocal
  exact hlocal

/-- The actual norm bound of the compact closed unit polydisk produces a genuine small scaled polydisk about each actual domain point. -/
theorem exists_scaledPolydisk_closed_subset {z : ComplexModel n} (hz : z ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ polydiskChart z r '' closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n)) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (Ω.isOpen.mem_nhds hz)
  obtain ⟨R, hR⟩ := (isCompact_closedUnitPolydisk (n := n)).exists_bound_of_continuousOn
    (continuous_id.continuousOn : ContinuousOn (fun w : ComplexModel n => w) (closedUnitPolydisk n))
  let r : ℝ := δ / (max R 0 + 1)
  have hden : 0 < max R 0 + 1 := by linarith [le_max_right R 0]
  have hr : 0 < r := div_pos hδ hden
  refine ⟨r, hr, ?_⟩
  rintro x ⟨w, hw, rfl⟩
  apply hball
  rw [mem_ball, dist_eq_norm]
  have hmul : r * (max R 0 + 1) = δ := by
    dsimp [r]
    exact div_mul_cancel₀ δ hden.ne'
  have hnorm : ‖polydiskChart z r w - z‖ = r * ‖w‖ := by
    simp only [polydiskChart, add_sub_cancel_left, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr]
  rw [hnorm]
  have hwR : ‖w‖ ≤ max R 0 := (hR w hw).trans (le_max_left R 0)
  nlinarith

/-- In every positive complex dimension, actual extended-real ordinary boundary maximality internally gives the genuine zero non-pluripolar measure. -/
theorem truncationLimitMeasure_eq_zero_of_boundaryMaximal (hn : 0 < n)
    {u : ComplexModel n → EReal} (hu : IsBoundaryMaximalPshOn (Ω : Set (ComplexModel n)) u) :
    truncationLimitMeasure Ω u hu.2.1 = 0 := by
  have hΩzero : truncationLimitMeasure Ω u hu.2.1 (Ω : Set (ComplexModel n)) = 0 := by
    rw [← compl_mem_ae_iff]
    apply (HereditarilyLindelofSpace.isLindelof (Ω : Set (ComplexModel n))).compl_mem_sets_of_nhdsWithin
    intro z hz
    obtain ⟨r, hr, hPΩ⟩ := exists_scaledPolydisk_closed_subset hz
    have hzP : z ∈ scaledPolydisk z r := by
      refine ⟨0, ?_, ?_⟩
      · intro i
        simp
      · simp [polydiskChart]
    refine ⟨scaledPolydisk z r, ?_, ?_⟩
    · rw [← coe_scaledPolydiskOpens hr.ne']
      exact nhdsWithin_le_nhds ((scaledPolydiskOpens z r).isOpen.mem_nhds
        ((coe_scaledPolydiskOpens hr.ne').symm ▸ hzP))
    · rw [compl_mem_ae_iff]
      exact truncationLimitMeasure_scaledPolydisk_eq_zero hn hu hr.ne' hPΩ
  apply Measure.measure_univ_eq_zero.mp
  simpa only [union_compl_self] using measure_union_null hΩzero (truncationLimitMeasure_compl hu.2.1)

end

end SGPT.Foundations.Analysis.Pending.SingularMaximalNonpluripolarZero
