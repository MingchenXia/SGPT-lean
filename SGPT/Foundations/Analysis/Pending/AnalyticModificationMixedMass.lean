import SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback
import SGPT.Foundations.Analysis.Pending.ModificationMassInvariance

set_option autoImplicit false

/-! # Genuine total mixed mass under actual general analytic modifications -/

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.AnalyticModificationMixedMass

open FirstPass FirstPass.PositiveClasses AnalyticModificationLocalDiscrepancy
  AnalyticModificationStrongPullback ModificationMassInvariance GlobalPotentialPullback
  GlobalNonPluripolar

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [MeasurableSpace Y] [BorelSpace Y]

/-- Total mass of the actual independent mixed product is invariant;
upstairs compactness and the pulled-back PSH tuple are internally supplied. -/
theorem globalMixedMeasure_univ_pullback_of_isAnalyticModification
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    {θ : Fin n → ClosedRealOneOneForm n X} {u : Fin n → X → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) :
    letI : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
    globalMixedMeasure (pullbackTuple hπ.1 θ) (fun i y => u i (π y))
        (fun i => thetaPlurisubharmonic_comp hπ.1 (hu i)) univ =
      globalMixedMeasure θ u hu univ := by
  classical
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  let hu' : ∀ i, ThetaPlurisubharmonic (pullbackTuple hπ.1 θ i).val
      (fun y => u i (π y)) := fun i => thetaPlurisubharmonic_comp hπ.1 (hu i)
  rcases isEmpty_or_nonempty Y with hY | hY
  · have : IsEmpty X := ⟨fun x => by
      obtain ⟨y, -⟩ := surjective_of_isAnalyticModification hπ x
      exact hY.false y⟩
    rw [Set.univ_eq_empty_iff.mpr hY, Set.univ_eq_empty_iff.mpr ‹IsEmpty X›,
      measure_empty, measure_empty]
  obtain ⟨B, hBc, hBa, hBi, hprea, hprei, hiso⟩ :=
    exists_isIsomorphismOver_of_isAnalyticModification hπ
  let N : Set X := Bᶜ
  have hN : IsOpen N := hBc.isOpen_compl
  let μY := globalMixedMeasure (pullbackTuple hπ.1 θ) (fun i y => u i (π y)) hu'
  let μX := globalMixedMeasure θ u hu
  have hBpol : ManifoldLocallyPluripolar (n := n) B :=
    manifoldLocallyPluripolar_of_isComplexAnalyticSubset hBa hBi
  have hprepol : ManifoldLocallyPluripolar (n := n) (π ⁻¹' B) :=
    manifoldLocallyPluripolar_of_isComplexAnalyticSubset hprea hprei
  have hX0 : μX B = 0 := globalMixedMeasure_doesNotChargeManifoldPluripolar hu B hBpol
  have hY0 : μY (π ⁻¹' B) = 0 :=
    globalMixedMeasure_doesNotChargeManifoldPluripolar hu' _ hprepol
  have h1 : μY univ = μY (π ⁻¹' N) := by
    refine le_antisymm ?_ (measure_mono (subset_univ _))
    calc μY univ ≤ μY (π ⁻¹' N ∪ π ⁻¹' B) := measure_mono fun y _ => by
            by_cases h : π y ∈ B
            · exact Or.inr h
            · exact Or.inl h
      _ ≤ μY (π ⁻¹' N) + μY (π ⁻¹' B) := measure_union_le _ _
      _ = μY (π ⁻¹' N) := by rw [hY0, add_zero]
  have h2 : μX univ = μX N := by
    refine le_antisymm ?_ (measure_mono (subset_univ _))
    calc μX univ ≤ μX (N ∪ B) := measure_mono fun x _ => by
            by_cases h : x ∈ B
            · exact Or.inr h
            · exact Or.inl h
      _ ≤ μX N + μX B := measure_union_le _ _
      _ = μX N := by rw [hX0, add_zero]
  have hinvm : AEMeasurable (invOver π N) (μX.restrict N) :=
    (continuousOn_invOver hπ.1 hN hiso).aemeasurable hN.measurableSet
  have h3 : μY (π ⁻¹' N) = μX N := by
    have h : (μY.restrict (π ⁻¹' N)) univ =
        ((μX.restrict N).map (invOver π N)) univ := by
      rw [globalMixedMeasure_restrict_preimage_eq_map hπ.1 hN hiso hu hu']
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Measure.map_apply_of_aemeasurable hinvm MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply MeasurableSet.univ, univ_inter] at h
    exact h
  change μY univ = μX univ
  rw [h1, h3, h2]

/-- Genuine diagonal pullback mass, with strong upstairs nondegeneracy
internally proved rather than supplied as a caller's hypothesis. -/
theorem diagonalPotentialMass_pullback_of_isAnalyticModification
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    (θ : ClosedRealOneOneForm n X) {u : X → EReal}
    (hu : IsThetaPshPotential θ.val u) :
    letI : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
    DiagonalMass.diagonalPotentialMass (ClosedRealOneOneForm.pullback hπ.1 θ)
        (fun y => u (π y)) (isThetaPshPotential_comp_of_isAnalyticModification hπ θ hu) =
      DiagonalMass.diagonalPotentialMass θ u hu := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  exact globalMixedMeasure_univ_pullback_of_isAnalyticModification hπ
    (θ := fun _ => θ) (u := fun _ => u) (fun _ => hu.1)

end
end SGPT.Foundations.Analysis.Pending.AnalyticModificationMixedMass
