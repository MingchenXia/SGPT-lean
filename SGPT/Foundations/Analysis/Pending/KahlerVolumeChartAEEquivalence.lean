import SGPT.Foundations.Analysis.Pending.KahlerVolumeSmoothPositive
import SGPT.Foundations.Analysis.Pending.ChartHaarKahlerVolumeAE

set_option autoImplicit false

/-!
# Actual Kahler-volume and chart Haar almost-everywhere equivalence

The actual smooth positive density produces the reverse AE transport.
Actual chart composition recovers the inverse push-forward, and actual
density nonvanishing cancels the density-measure AE implication. The
already proved forward finite-cover transport gives the equivalence.
No density certificate or pluripolarity of arbitrary null sets is assumed.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.KahlerVolumeChartAEEquivalence

open FirstPass FirstPass.PositiveClasses IntegrationCurrent ChartwiseGlobalL1

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Actual positive Kahler density transports arbitrary global AE predicates back to chart Haar measure. -/
theorem ae_chartTarget_of_ae_kahlerVolume (omega : KahlerBackground n M)
    (e : ComplexChart n M) {P : M → Prop}
    (hae : ∀ᵐ x ∂kahlerVolume omega, P x) :
    ∀ᵐ z ∂(volume.restrict e.val.target), P (e.val.symm z) := by
  obtain ⟨ρ, hρ, hpos, hmap⟩ := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega e
  let ν := (volume.restrict e.val.target).withDensity (fun z => ENNReal.ofReal (ρ z))
  have hac : ν ≪ volume.restrict e.val.target := withDensity_absolutelyContinuous _ _
  have hinv : AEMeasurable e.val.symm ν :=
    (e.val.continuousOn_symm.aemeasurable e.val.open_target.measurableSet).mono_ac hac
  have hforward : AEMeasurable e.val ((kahlerVolume omega).restrict e.val.source) :=
    e.val.continuousOn.aemeasurable e.val.open_source.measurableSet
  have hinvmap : AEMeasurable e.val.symm (Measure.map e.val ((kahlerVolume omega).restrict e.val.source)) := by
    rw [hmap]
    exact hinv
  have hleft : (e.val.symm ∘ e.val) =ᵐ[(kahlerVolume omega).restrict e.val.source] id :=
    (ae_restrict_mem e.val.open_source.measurableSet).mono fun x hx => e.val.left_inv hx
  have hν : (kahlerVolume omega).restrict e.val.source = Measure.map e.val.symm ν := by
    calc
      _ = Measure.map id ((kahlerVolume omega).restrict e.val.source) := Measure.map_id.symm
      _ = Measure.map (e.val.symm ∘ e.val) ((kahlerVolume omega).restrict e.val.source) :=
        (Measure.map_congr hleft).symm
      _ = Measure.map e.val.symm (Measure.map e.val ((kahlerVolume omega).restrict e.val.source)) :=
        (hinvmap.map_map_of_aemeasurable hforward).symm
      _ = _ := by rw [hmap]
  have hrestrict : ∀ᵐ x ∂((kahlerVolume omega).restrict e.val.source), P x :=
    hae.filter_mono ae_restrict_le
  rw [hν] at hrestrict
  have hνP : ∀ᵐ z ∂ν, P (e.val.symm z) := ae_of_ae_map hinv hrestrict
  have hd : AEMeasurable (fun z => ENNReal.ofReal (ρ z)) (volume.restrict e.val.target) :=
    (ENNReal.continuous_ofReal.comp_continuousOn hρ.continuousOn).aemeasurable
      e.val.open_target.measurableSet
  have hpred := (ae_withDensity_iff' hd).mp hνP
  filter_upwards [hpred, ae_restrict_mem e.val.open_target.measurableSet] with z hz hzt
  exact hz (ENNReal.ofReal_pos.mpr (hpos z hzt)).ne'

/-- Actual volume AE and all actual chart Haar AE predicates have exactly the same measurable measure class. -/
theorem ae_kahlerVolume_iff_forall_chart_ae (omega : KahlerBackground n M)
    {P : M → Prop} (hP : MeasurableSet {x | P x}) :
    (∀ᵐ x ∂kahlerVolume omega, P x) ↔
      ∀ e : ComplexChart n M, ∀ᵐ z ∂(volume.restrict e.val.target), P (e.val.symm z) :=
  ⟨fun h e => ae_chartTarget_of_ae_kahlerVolume omega e h,
    ChartHaarKahlerVolumeAE.ae_kahlerVolume_of_forall_chart_ae omega hP⟩

end

end SGPT.Foundations.Analysis.Pending.KahlerVolumeChartAEEquivalence
