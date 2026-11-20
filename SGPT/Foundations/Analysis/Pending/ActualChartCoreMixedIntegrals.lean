import SGPT.Foundations.Analysis.Pending.ActualChartCoreMixedMeasure
import SGPT.Foundations.Analysis.Pending.ChartPartition

set_option autoImplicit false

/-! # Actual continuous chart-core test transport for mixed products

Exact measure identity and compact support produce globally continuous
zero extension and the genuine integral identity. Tests need not be smooth.
All dimensions and only actual chart-source boundedness are retained.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ActualChartCoreMixedIntegrals

open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  FirstPass.MixedMongeAmpere FirstPass.GlobalPotentialPatches
  GlobalNonPluripolar GlobalSlotStokes PatchLocalBoundedMeasure
  BedfordTaylor MixedMongeAmpere ChartPartition

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
private theorem continuous_chart_zero_extension (e : ComplexChart n M)
    {h : ComplexModel n → ℝ} (hc : Continuous h) (hk : HasCompactSupport h)
    (ht : tsupport h ⊆ e.val.target) : Continuous (chartExtend e h) := by
  have hK : IsCompact (e.val.symm '' tsupport h) :=
    hk.image_of_continuousOn (e.val.symm.continuousOn.mono ht)
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ e.val.symm '' tsupport h
  · obtain ⟨z, hz, hzx⟩ := hx
    have hxS : x ∈ e.val.source := hzx ▸ e.val.map_target (ht hz)
    have hh : ContinuousAt (fun y => h (e.val y)) x :=
      hc.continuousAt.comp (e.val.continuousAt hxS)
    apply hh.congr
    filter_upwards [e.val.open_source.mem_nhds hxS] with y hy
    exact (chartExtend_of_mem hy).symm
  · apply continuousAt_const.congr
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact (chartExtend_eq_zero_of_notMem_image hy).symm

/-- Natural actual chart core formulas produce both the continuous global
zero extension and the true canonical mixed integral identity. -/
theorem exists_core_mixed_integral_identity
    {η : Fin n → ClosedRealOneOneForm n M} {κ : ClosedRealOneOneForm n M}
    (J : SlotChart η κ) {u : Fin n → M → EReal}
    (hu : ∀ i, IsThetaPshPotential (η i).val (u i))
    (hb : ∀ i, IsBoundedPotentialOn (u i) (J.source : Set M))
    {O : Set M} (hO : IsOpen O) (hOS : O ⊆ (J.source : Set M))
    (f : Fin n → ComplexModel n → ℝ)
    (hcore : ∀ i x, x ∈ O → u i x = ((f i (J.chart.val x) : ℝ) : EReal)) :
    ∃ Q : Opens (ComplexModel n),
      (Q : Set (ComplexModel n)) = (J.domain : Set (ComplexModel n)) ∩ J.chart.val.symm ⁻¹' O ∧
      ∃ hG : IsLocallyBoundedMixedPshOn Q (fun i z => f i z + J.potential i z),
      ∀ h : ComplexModel n → ℝ, Continuous h → HasCompactSupport h → tsupport h ⊆ Q →
        Continuous (chartExtend J.chart h) ∧
        (∫ x, chartExtend J.chart h x ∂globalMixedMeasure η u (fun i => (hu i).1)) =
          ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q
            (fun i z => f i z + J.potential i z) hG := by
  obtain ⟨Q, hQ, hG, hmeasure⟩ :=
    ActualChartCoreMixedMeasure.exists_core_mixed_measure_identity J hu hb hO hOS f hcore
  have hQD : Q ≤ J.domain := by
    intro z hz
    change z ∈ (Q : Set (ComplexModel n)) at hz
    rw [hQ] at hz
    exact hz.1
  have hQt : (Q : Set (ComplexModel n)) ⊆ J.chart.val.target :=
    fun z hz => J.domain_le_target (hQD hz)
  let P : Patch η u := {
    chart := J.chart
    domain := Q
    domain_le_target := hQt
    potential := J.potential
    localPotential := fun i => (J.localPotential i).mono Q.isOpen hQD
    plurisubharmonic := fun i => (J.patch u (fun i => (hu i).1)).plurisubharmonic i |>.mono hQD }
  have hsource : (P.source : Set M) = O := by
    ext x
    constructor
    · intro hx
      have hxQ : J.chart.val x ∈ (Q : Set (ComplexModel n)) := hx.2
      rw [hQ] at hxQ
      have hxO : J.chart.val.symm (J.chart.val x) ∈ O := hxQ.2
      rw [J.chart.val.left_inv hx.1] at hxO
      exact hxO
    · intro hx
      have hxS := hOS hx
      refine ⟨hxS.1, ?_⟩
      change J.chart.val x ∈ (Q : Set (ComplexModel n))
      rw [hQ]
      refine ⟨hxS.2, ?_⟩
      change J.chart.val.symm (J.chart.val x) ∈ O
      rw [J.chart.val.left_inv hxS.1]
      exact hx
  let ν := canonicalMixedBedfordTaylorMeasure Q (fun i z => f i z + J.potential i z) hG
  have hνcompl : ν (Q : Set (ComplexModel n))ᶜ = 0 :=
    canonicalMixedBedfordTaylorMeasure_compl Q (fun i z => f i z + J.potential i z) hG
  have hμglob : (globalMixedMeasure η u (fun i => (hu i).1)).restrict O = P.pushMeasure ν := by
    ext E
    rw [Measure.restrict_apply' hO.measurableSet, Patch.pushMeasure_apply_image]
    change globalMixedMeasure η u (fun i => (hu i).1) (E ∩ O) =
      ν (J.chart.val '' (E ∩ (P.source : Set M)))
    rw [hsource]
    exact hmeasure (E ∩ O) inter_subset_right
  refine ⟨Q, hQ, hG, fun h hc hk ht => ?_⟩
  refine ⟨continuous_chart_zero_extension J.chart hc hk (ht.trans hQt), ?_⟩
  have hzero : ∀ x ∉ O, chartExtend J.chart h x = 0 := by
    intro x hx
    by_cases hxS : x ∈ J.chart.val.source
    · rw [chartExtend_of_mem hxS]
      apply image_eq_zero_of_notMem_tsupport
      intro hxT
      apply hx
      have hxQ : J.chart.val x ∈ (Q : Set (ComplexModel n)) := ht hxT
      rw [hQ] at hxQ
      have hxO : J.chart.val.symm (J.chart.val x) ∈ O := hxQ.2
      rwa [J.chart.val.left_inv hxS] at hxO
    · exact chartExtend_of_notMem hxS
  calc
    _ = ∫ x in O, chartExtend J.chart h x ∂globalMixedMeasure η u (fun i => (hu i).1) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ = ∫ x, chartExtend J.chart h x ∂P.pushMeasure ν := by
      rw [hμglob]
    _ = ∫ z, chartExtend J.chart h (J.chart.val.symm z) ∂ν :=
      Patch.integral_pushMeasure P hνcompl (chartExtend J.chart h)
    _ = ∫ z, h z ∂ν := by
      have hae : ∀ᵐ z ∂ν, z ∈ (Q : Set (ComplexModel n)) := ae_iff.mpr hνcompl
      apply integral_congr_ae
      filter_upwards [hae] with z hz
      rw [chartExtend_of_mem (J.chart.val.map_target (hQt hz)),
        J.chart.val.right_inv (hQt hz)]

end
end SGPT.Foundations.Analysis.Pending.ActualChartCoreMixedIntegrals
