import SGPT.Foundations.Analysis.Pending.AnalyticModificationPotentialDescent
import SGPT.Foundations.Analysis.Pending.AnalyticModificationMixedMass
import SGPT.Foundations.Analysis.FirstPass.ThetaPshEnvelopes
import SGPT.Foundations.Analysis.Pending.RelativeEnergy
import SGPT.Foundations.Analysis.Pending.UniformBoundedGlobalMass

set_option autoImplicit false

/-! # Literal minimal references and endpoint masses under general modifications -/

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.AnalyticModificationMinimalMixedPullback

open FirstPass FirstPass.PositiveClasses AnalyticModificationLocalDiscrepancy
  AnalyticModificationStrongPullback AnalyticModificationPotentialDescent
  AnalyticModificationMixedMass GlobalPotentialPullback ModificationMassInvariance
  RelativeEnergy GlobalNonPluripolar

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- Literal minimal reference identity from a natural genuine potential
witness and actual descent, without a Big or positive-mass assumption. -/
theorem thetaPshSupremum_pullback_eq
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    (θ : ClosedRealOneOneForm n X) (hne : ∃ u, IsThetaPshPotential θ.val u) (y : Y) :
    thetaPshSupremum (ClosedRealOneOneForm.pullback hπ.1 θ).val y =
      thetaPshSupremum θ.val (π y) := by
  let : Nonempty Y := ⟨y⟩
  let : Nonempty X := ⟨π y⟩
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  obtain ⟨u, hu⟩ := hne
  have hV := FirstPass.thetaPshSupremum_isThetaPshPotential θ.val θ.2.1 θ.2.2
    hu.1.hasSmoothLocalPotentials ⟨u, hu⟩
  have hVp := isThetaPshPotential_comp_of_isAnalyticModification hπ θ hV
  have hV0 : (fun z => thetaPshSupremum θ.val (π z)) ≤ 0 :=
    fun z => thetaPshSupremum_le_zero θ.val (π z)
  let β := ClosedRealOneOneForm.pullback hπ.1 θ
  have hW : IsThetaPshPotential β.val (thetaPshSupremum β.val) :=
    FirstPass.thetaPshSupremum_isThetaPshPotential β.val β.2.1 β.2.2
      hVp.1.hasSmoothLocalPotentials ⟨_, hVp⟩
  obtain ⟨s, hs, he⟩ := exists_descent_of_isAnalyticModification hπ θ hW
  have hs0 : s ≤ 0 := by
    intro x
    obtain ⟨z, rfl⟩ := surjective_of_isAnalyticModification hπ x
    rw [he z]
    exact thetaPshSupremum_le_zero β.val z
  exact le_antisymm ((he y).symm ▸ le_thetaPshSupremum hs hs0 (π y))
    (le_thetaPshSupremum hVp hV0 y)

/-- Actual endpoint masses, before realification, with both upstairs
strong predicates and upstairs compactness internally supplied. -/
theorem endpointMixedMass_pullback_of_isAnalyticModification
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    (θ : ClosedRealOneOneForm n X) {p a : X → EReal}
    (hp : IsThetaPshPotential θ.val p) (ha : IsThetaPshPotential θ.val a)
    (j : Fin (n + 1)) :
    letI : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
    endpointMixedMass (ClosedRealOneOneForm.pullback hπ.1 θ)
        (fun y => p (π y)) (fun y => a (π y))
        (isThetaPshPotential_comp_of_isAnalyticModification hπ θ hp)
        (isThetaPshPotential_comp_of_isAnalyticModification hπ θ ha) j =
      endpointMixedMass θ p a hp ha j := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  have h := globalMixedMeasure_univ_pullback_of_isAnalyticModification hπ
    (θ := fun _ => θ) (endpointMixedPotential_thetaPlurisubharmonic θ j a p ha hp)
  have ht : (fun i y => endpointMixedPotential j a p i (π y)) =
      endpointMixedPotential j (fun y => a (π y)) (fun y => p (π y)) := by
    funext i y
    dsimp only [endpointMixedPotential]
    split_ifs <;> rfl
  have he := UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple ht
    (fun i => thetaPlurisubharmonic_comp hπ.1
      (endpointMixedPotential_thetaPlurisubharmonic θ j a p ha hp i))
    (endpointMixedPotential_thetaPlurisubharmonic
      (ClosedRealOneOneForm.pullback hπ.1 θ) j
      (fun y => a (π y)) (fun y => p (π y))
      (isThetaPshPotential_comp_of_isAnalyticModification hπ θ ha)
      (isThetaPshPotential_comp_of_isAnalyticModification hπ θ hp))
  exact (congrArg (fun μ : Measure Y => μ univ) he).symm.trans h

end
end SGPT.Foundations.Analysis.Pending.AnalyticModificationMinimalMixedPullback
