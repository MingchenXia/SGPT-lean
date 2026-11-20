import SGPT.Foundations.Analysis.Pending.GlobalMixedMassMonotone
import SGPT.Foundations.Analysis.Pending.SingularGlobalPMaximum
import SGPT.Foundations.Analysis.Pending.SingularGlobalPMixedMassEquality

set_option autoImplicit false

/-! # Actual independent mixed mass monotonicity for global P-order

SGPT PDF0216--0217 Proposition 6.1.4, in the full independent original
backgrounds. Actual slotwise maxima and the proved global source maximum
characterization produce original mixed mass preservation; true ordinary
singularity monotonicity then proves the original inequality. All original
masses may vanish, and dimension zero uses the actual empty tuple.
-/

open Set

namespace SGPT.Foundations.Analysis.Pending.ActualMixedMassGlobalPMonotone

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar MixedMass
  SingularGlobalPOrder SingularGlobalPMaximum SingularGlobalPMixedMassEquality
  GlobalMixedMassMonotone

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual source order in each independent slot produces original mixed
mass monotonicity through genuine maximum equivalences, including zero masses. -/
theorem globalMixedMass_mono_of_sourcePOrder (omega : KahlerBackground n M)
    {θ : Fin n → ClosedRealOneOneForm n M} {u v : Fin n → M → EReal}
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    (hv : ∀ i, IsThetaPshPotential (θ i).val (v i))
    (huv : ∀ i, SourcePOrder (n := n) (u i) (v i)) :
    globalMixedMass θ u (fun i => (hu i).1) ≤
      globalMixedMass θ v (fun i => (hv i).1) := by
  let w : Fin n → M → EReal := fun i x => max (u i x) (v i x)
  have hw : ∀ i, IsThetaPshPotential (θ i).val (w i) := fun i =>
    IsThetaPshPotential.max (hu i) (hv i)
  have hrel : ∀ i, SourcePEquivalent (n := n) (w i) (v i) := fun i =>
    (sourcePOrder_iff_sourcePEquivalent_max omega (hu i) (hv i)).mp (huv i)
  have hmass := globalMixedMass_eq_of_sourcePEquivalent omega hw hv hrel
  exact (globalMixedMass_mono_of_isThetaPshPotential omega hu hw
    (fun _ => MoreSingularOn.of_le fun _ _ => le_max_left _ _)).trans_eq hmass

end

end SGPT.Foundations.Analysis.Pending.ActualMixedMassGlobalPMonotone
