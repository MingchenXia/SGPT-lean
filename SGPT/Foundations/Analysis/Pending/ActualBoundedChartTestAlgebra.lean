import SGPT.Foundations.Analysis.Pending.ActualChartCoreMixedMeasure
import SGPT.Foundations.Analysis.Pending.ActualLocalMixedIntegralSlots
import SGPT.Foundations.Analysis.Pending.ChartPartition

set_option autoImplicit false

/-! # Actual algebra and chart transport for cutoff tests

Bounded measurable compact tests are integrable by genuine compact mass
finiteness. The exact chart-core pushforward also transports arbitrary
supported real tests. No whole-domain mass or inverse-chart ghost
measurability is assumed.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ActualBoundedChartTestAlgebra

open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  FirstPass.MixedMongeAmpere FirstPass.GlobalPotentialPatches
  GlobalNonPluripolar GlobalSlotStokes PatchLocalBoundedMeasure
  BedfordTaylor MixedMongeAmpere LocalBedfordTaylorCalculus ChartPartition

noncomputable section

variable {n : ℕ}

private theorem integrable_compact_test {Q : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (hu : IsLocallyBoundedMixedPshOn Q u)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKQ : K ⊆ Q)
    {h : ComplexModel n → ℝ} (hm : Measurable h) {C : ℝ}
    (hb : ∀ z, |h z| ≤ C) (hz : ∀ z ∉ K, h z = 0) :
    Integrable h (canonicalMixedBedfordTaylorMeasure Q u hu) :=
  integrable_of_bounded_of_support hK.isClosed.measurableSet
    (canonicalMixedBedfordTaylorMeasure_finiteOnCompacts hu hK hKQ)
    hm.stronglyMeasurable hb hz

/-- Actual compact mass finiteness makes bounded measurable cutoff tests
integrable and produces the genuine slot-sum integral identity. -/
theorem integral_slot_add_bounded {Q : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (hu : IsLocallyBoundedMixedPshOn Q u) (k : Fin n)
    {a b : ComplexModel n → ℝ} (ha : IsLocallyBoundedPshOn Q a)
    (hb : IsLocallyBoundedPshOn Q b) :
    ∃ (hA : IsLocallyBoundedMixedPshOn Q (Function.update u k a))
      (hB : IsLocallyBoundedMixedPshOn Q (Function.update u k b))
      (hS : IsLocallyBoundedMixedPshOn Q (Function.update u k (fun z => a z + b z))),
      ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ Q →
      ∀ h : ComplexModel n → ℝ, Measurable h →
      ∀ C : ℝ, (∀ z, |h z| ≤ C) → (∀ z ∉ K, h z = 0) →
        (∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q
          (Function.update u k (fun z => a z + b z)) hS) =
        (∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q (Function.update u k a) hA) +
          ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q (Function.update u k b) hB := by
  classical
  have hupdate (f : ComplexModel n → ℝ) (hf : IsLocallyBoundedPshOn Q f) :
      IsLocallyBoundedMixedPshOn Q (Function.update u k f) := by
    intro i
    by_cases hi : i = k
    · subst hi
      simpa using hf
    · simpa [Function.update_of_ne hi] using hu i
  let hA := hupdate a ha
  let hB := hupdate b hb
  let hS := hupdate (fun z => a z + b z) (isLocallyBoundedPshOn_add ha hb)
  have hlimit (v : Fin n → ComplexModel n → ℝ) (hv : IsLocallyBoundedMixedPshOn Q v) :
      IsBTLimit Q v (canonicalMixedBedfordTaylorMeasure Q v hv) :=
    IsLocalMixedBedfordTaylorMeasure.isBTLimit (canonicalMixedBedfordTaylorMeasure_spec Q v hv)
  have hμ := (hlimit _ hS).add_slot k (hlimit _ hA) (hlimit _ hB)
  refine ⟨hA, hB, hS, fun K hK hKQ h hm C hC hzero => ?_⟩
  rw [hμ, integral_add_measure (integrable_compact_test hA hK hKQ hm hC hzero)
    (integrable_compact_test hB hK hKQ hm hC hzero)]

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The actual chart-core measure producer transports every real supported
test, including discontinuous cutoff tests, by its true patch pushforward. -/
theorem exists_core_arbitrary_test_integrals
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
      ∀ h : ComplexModel n → ℝ, Function.support h ⊆ Q →
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
      rwa [J.chart.val.left_inv hx.1] at hxO
    · intro hx
      have hxS := hOS hx
      refine ⟨hxS.1, ?_⟩
      change J.chart.val x ∈ (Q : Set (ComplexModel n))
      rw [hQ]
      refine ⟨hxS.2, ?_⟩
      change J.chart.val.symm (J.chart.val x) ∈ O
      rwa [J.chart.val.left_inv hxS.1]
  let ν := canonicalMixedBedfordTaylorMeasure Q (fun i z => f i z + J.potential i z) hG
  have hνcompl : ν (Q : Set (ComplexModel n))ᶜ = 0 :=
    canonicalMixedBedfordTaylorMeasure_compl Q (fun i z => f i z + J.potential i z) hG
  have hμ : (globalMixedMeasure η u (fun i => (hu i).1)).restrict O = P.pushMeasure ν := by
    ext E
    rw [Measure.restrict_apply' hO.measurableSet, Patch.pushMeasure_apply_image]
    change globalMixedMeasure η u (fun i => (hu i).1) (E ∩ O) =
      ν (J.chart.val '' (E ∩ (P.source : Set M)))
    rw [hsource]
    exact hmeasure (E ∩ O) inter_subset_right
  refine ⟨Q, hQ, hG, fun h ht => ?_⟩
  have hzero : ∀ x ∉ O, chartExtend J.chart h x = 0 := by
    intro x hx
    by_cases hxS : x ∈ J.chart.val.source
    · rw [chartExtend_of_mem hxS]
      by_contra hn
      have hxQ : J.chart.val x ∈ (Q : Set (ComplexModel n)) := ht hn
      rw [hQ] at hxQ
      have hxO : J.chart.val.symm (J.chart.val x) ∈ O := hxQ.2
      rw [J.chart.val.left_inv hxS] at hxO
      exact hx hxO
    · exact chartExtend_of_notMem hxS
  calc
    _ = ∫ x in O, chartExtend J.chart h x ∂globalMixedMeasure η u (fun i => (hu i).1) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ = ∫ x, chartExtend J.chart h x ∂P.pushMeasure ν := by rw [hμ]
    _ = ∫ z, chartExtend J.chart h (J.chart.val.symm z) ∂ν :=
      Patch.integral_pushMeasure P hνcompl (chartExtend J.chart h)
    _ = ∫ z, h z ∂ν := by
      have hae : ∀ᵐ z ∂ν, z ∈ (Q : Set (ComplexModel n)) := ae_iff.mpr hνcompl
      apply integral_congr_ae
      filter_upwards [hae] with z hz
      rw [chartExtend_of_mem (J.chart.val.map_target (hQt hz)),
        J.chart.val.right_inv (hQt hz)]

end
end SGPT.Foundations.Analysis.Pending.ActualBoundedChartTestAlgebra
