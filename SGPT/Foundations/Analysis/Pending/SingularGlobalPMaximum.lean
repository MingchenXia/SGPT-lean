import SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
import SGPT.Foundations.Analysis.Pending.RooftopMassDiamondEnvelopeMax

set_option autoImplicit false

/-! # Actual maximum characterization of the source P-order -/

namespace SGPT.Foundations.Analysis.Pending.SingularGlobalPMaximum

open FirstPass FirstPass.PositiveClasses FirstPass.POrder DiagonalMass
  SingularGlobalPOrder SingularPositiveCommonBackgroundExistence

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- The actual positive enlarged background, genuine maximum mass identity and proved positive-mass source criterion internally identify the maximum's source class; no zero-background envelope comparison is assumed. -/
theorem sourcePOrder_iff_sourcePEquivalent_max (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v) :
    SourcePOrder (n := n) u v ↔ SourcePEquivalent (n := n) (fun x => max (u x) (v x)) v := by
  have hw : IsThetaPshPotential θ.val (fun x => max (u x) (v x)) :=
    IsThetaPshPotential.max hu hv
  constructor
  · intro huv
    let Θ := θ + omega.form
    have huΘ : IsThetaPshPotential Θ.val u :=
      LocalPotentials.isThetaPshPotential_add_of_semipositive hu omega.isSemipositive
    have hvΘ : IsThetaPshPotential Θ.val v :=
      LocalPotentials.isThetaPshPotential_add_of_semipositive hv omega.isSemipositive
    have hwΘ : IsThetaPshPotential Θ.val (fun x => max (u x) (v x)) :=
      IsThetaPshPotential.max huΘ hvΘ
    have hupΘ : HasPositivePotentialMass Θ u huΘ := by
      simpa only [one_smul] using hasPositivePotentialMass_add_smul omega hu zero_lt_one
    have hvpΘ : HasPositivePotentialMass Θ v hvΘ := by
      simpa only [one_smul] using hasPositivePotentialMass_add_smul omega hv zero_lt_one
    have hwpΘ : HasPositivePotentialMass Θ (fun x => max (u x) (v x)) hwΘ :=
      lt_of_lt_of_le hvpΘ (diagonalPotentialMass_mono_of_kahler omega hvΘ hwΘ
        (MoreSingularOn.of_le fun x _ => le_max_right _ _))
    have hfixed := (sourcePOrder_iff_pOrderWith omega Θ huΘ hvΘ hupΘ hvpΘ).mp huv
    have hPu := singularityEnvelope_isThetaPshPotential Θ.val Θ.property.1 Θ.property.2
      huΘ.1.hasSmoothLocalPotentials u huΘ
    have hPv := singularityEnvelope_isThetaPshPotential Θ.val Θ.property.1 Θ.property.2
      hvΘ.1.hasSmoothLocalPotentials v hvΘ
    have hmaxP := IsThetaPshPotential.max hPu hPv
    have heq : (fun x => max (singularityEnvelope Θ.val u x)
        (singularityEnvelope Θ.val v x)) = singularityEnvelope Θ.val v :=
      funext fun x => max_eq_right (hfixed x)
    have hmass : diagonalPotentialMass Θ (fun x => max (u x) (v x)) hwΘ =
        diagonalPotentialMass Θ v hvΘ := by
      calc
        _ = diagonalPotentialMass Θ
            (fun x => max (singularityEnvelope Θ.val u x) (singularityEnvelope Θ.val v x))
              hmaxP := (diagonalPotentialMass_max_singularityEnvelope_eq omega Θ
                huΘ hvΘ hwΘ hmaxP).symm
        _ = diagonalPotentialMass Θ (singularityEnvelope Θ.val v) hPv :=
          diagonalPotentialMass_congr heq hmaxP hPv
        _ = diagonalPotentialMass Θ v hvΘ := singularityEnvelopeMassPreserving omega Θ v hvΘ hPv
    have hvw : SourcePOrder (n := n) v (fun x => max (u x) (v x)) :=
      sourcePOrder_of_moreSingularOn omega θ θ hv hw
        (MoreSingularOn.of_le fun x _ => le_max_right _ _)
    have h := (sourcePEquivalent_iff_diagonalPotentialMass_eq_of_sourcePOrder omega Θ
      hvΘ hwΘ hvpΘ hwpΘ hvw).mpr hmass.symm
    exact ⟨h.2, h.1⟩
  · intro h
    exact (sourcePOrder_of_moreSingularOn omega θ θ hu hw
      (MoreSingularOn.of_le fun x _ => le_max_left _ _)).trans omega h.1

end

end SGPT.Foundations.Analysis.Pending.SingularGlobalPMaximum
