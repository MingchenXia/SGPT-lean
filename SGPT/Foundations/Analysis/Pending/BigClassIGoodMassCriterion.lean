import SGPT.Foundations.Analysis.Pending.IGood
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicsFullMassGeneral

set_option autoImplicit false

/-! # Actual cohomological-big I-good mass-volume criterion -/

namespace SGPT.Foundations.Analysis.Pending.BigClassIGoodMassCriterion

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  DiagonalMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- The true class-bigness and genuine PSH witnesses supply every auxiliary
potential-based and local-potential input of the actual mass criterion. -/
theorem iGoodWith_iff_actual_mass_eq_iVolume
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hpos : HasPositivePotentialMass θ u hu) :
    IGoodWith θ u hu ↔
      diagonalPotentialMass θ u hu = iVolume θ hu.1.hasSmoothLocalPotentials u hu :=
  iGoodWith_iff_mass_eq_iVolume omega θ
    (FiniteGeodesicsFullMassGeneral.bigWithRespectToViaPotentials_of_isBigClass omega θ hbig)
    hu.1.hasSmoothLocalPotentials u hu hpos

end

end SGPT.Foundations.Analysis.Pending.BigClassIGoodMassCriterion
