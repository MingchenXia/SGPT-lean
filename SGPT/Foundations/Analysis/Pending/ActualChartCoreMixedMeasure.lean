import SGPT.Foundations.Analysis.Pending.ThetaCapacityChartLocal
import SGPT.Foundations.Analysis.Pending.BedfordTaylorFixedWeight

set_option autoImplicit false

/-! # Actual chart core formulas identify genuine mixed measures

Independent exact core transport. Only boundedness on the actual slot-chart
source is needed. Real locally bounded PSH of the corrected core tuple and
its canonical measure identification are produced, in all dimensions and on
all subsets. The unbounded capacity lower-semicontinuity remains separate.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ActualChartCoreMixedMeasure

open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  FirstPass.MixedMongeAmpere FirstPass.GlobalPotentialPatches
  GlobalNonPluripolar BoundedGlobalProduct GlobalSlotStokes
  PatchLocalBoundedMeasure BedfordTaylor MixedMongeAmpere

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- A literal real core formula internally produces the genuine corrected
Bedford--Taylor tuple and identifies the actual mixed measure on all subsets. -/
theorem exists_core_mixed_measure_identity
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
      ∀ E : Set M, E ⊆ O →
        globalMixedMeasure η u (fun i => (hu i).1) E =
          canonicalMixedBedfordTaylorMeasure Q (fun i z => f i z + J.potential i z) hG
            (J.chart.val '' E) := by
  let P := J.patch u (fun i => (hu i).1)
  have hbP : ∀ i, IsBoundedPotentialOn (u i) (P.source : Set M) := hb
  have hQo : IsOpen ((J.domain : Set (ComplexModel n)) ∩ J.chart.val.symm ⁻¹' O) :=
    (J.chart.val.symm.continuousOn.mono J.domain_le_target).isOpen_inter_preimage
      J.domain.isOpen hO
  let Q : Opens (ComplexModel n) :=
    ⟨(J.domain : Set (ComplexModel n)) ∩ J.chart.val.symm ⁻¹' O, hQo⟩
  have hQD : Q ≤ J.domain := inter_subset_left
  have hF : IsLocallyBoundedMixedPshOn J.domain (correctedReal P) :=
    correctedReal_isLocallyBoundedMixedPshOn_of_boundedOn P hbP
  have hFQ (i : Fin n) : IsLocallyBoundedPshOn Q (correctedReal P i) :=
    BedfordTaylor.IsLocallyBoundedPshOn.mono_opens (hF i) hQD
  have heq (i : Fin n) : EqOn (correctedReal P i)
      (fun z => f i z + J.potential i z) (Q : Set (ComplexModel n)) := by
    intro z hz
    rw [correctedReal_eq_of_boundedOn (hbP i) hz.1]
    change (u i (J.chart.val.symm z)).toReal + J.potential i z = _
    rw [hcore i (J.chart.val.symm z) hz.2, EReal.toReal_coe,
      J.chart.val.right_inv (J.domain_le_target hz.1)]
  have hG : IsLocallyBoundedMixedPshOn Q (fun i z => f i z + J.potential i z) := by
    intro i
    refine ⟨plurisubharmonicOn_congr Q.isOpen (hFQ i).1
      (fun z hz => congrArg (fun t : ℝ => (t : EReal)) (heq i hz)), ?_⟩
    intro z hz
    obtain ⟨V, hzV, hVQ, C, hC⟩ := (hFQ i).2 z hz
    refine ⟨V, hzV, hVQ, C, fun w hw => ?_⟩
    change |f i w + J.potential i w| ≤ C
    have heq' : correctedReal P i w = f i w + J.potential i w := heq i (hVQ hw)
    rw [← heq']
    exact hC w hw
  let ν := canonicalMixedBedfordTaylorMeasure J.domain (correctedReal P) hF
  have hν : IsBTLimit J.domain (correctedReal P) ν :=
    IsLocalMixedBedfordTaylorMeasure.isBTLimit
      (canonicalMixedBedfordTaylorMeasure_spec J.domain (correctedReal P) hF)
  have hνglob : (globalMixedMeasure η u (fun i => (hu i).1)).restrict (J.source : Set M) =
      P.pushMeasure ν :=
    globalMixedMeasure_restrict_patch_eq_canonical_of_boundedOn (fun i => (hu i).1) P hbP
  have hνQ : ν.restrict (Q : Set (ComplexModel n)) =
      canonicalMixedBedfordTaylorMeasure Q (fun i z => f i z + J.potential i z) hG :=
    ((hν.restrict_opens hQD).congr heq).unique
      (IsLocalMixedBedfordTaylorMeasure.isBTLimit
        (canonicalMixedBedfordTaylorMeasure_spec Q (fun i z => f i z + J.potential i z) hG))
  refine ⟨Q, rfl, hG, fun E hEO => ?_⟩
  have hES : E ⊆ (J.source : Set M) := hEO.trans hOS
  have hEQ : J.chart.val '' E ⊆ (Q : Set (ComplexModel n)) := by
    rintro z ⟨x, hx, rfl⟩
    have hxS := hES hx
    refine ⟨hxS.2, ?_⟩
    change J.chart.val.symm (J.chart.val x) ∈ O
    rw [J.chart.val.left_inv hxS.1]
    exact hEO hx
  calc
    _ = ((globalMixedMeasure η u (fun i => (hu i).1)).restrict (J.source : Set M)) E := by
      rw [Measure.restrict_apply' J.source.isOpen.measurableSet,
        inter_eq_self_of_subset_left hES]
    _ = P.pushMeasure ν E := congrArg (fun μ : Measure M => μ E) hνglob
    _ = ν (J.chart.val '' E) := by
      rw [Patch.pushMeasure_apply_image]
      change ν (J.chart.val '' (E ∩ (J.source : Set M))) = _
      rw [inter_eq_self_of_subset_left hES]
    _ = (ν.restrict (Q : Set (ComplexModel n))) (J.chart.val '' E) := by
      rw [Measure.restrict_apply' Q.isOpen.measurableSet, inter_eq_self_of_subset_left hEQ]
    _ = _ := congrArg (fun μ : Measure (ComplexModel n) => μ (J.chart.val '' E)) hνQ

end
end SGPT.Foundations.Analysis.Pending.ActualChartCoreMixedMeasure
