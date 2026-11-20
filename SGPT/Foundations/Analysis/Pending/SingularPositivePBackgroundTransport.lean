import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeIdempotencePositive
import SGPT.Foundations.Analysis.Pending.AmbientMassBackgroundMonotone
import SGPT.Foundations.Analysis.FirstPass.POrder

set_option autoImplicit false

/-! # Actual positive-mass P-envelope composition and forward background transport -/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularPositivePBackgroundTransport

open FirstPass FirstPass.PositiveClasses FirstPass.POrder DiagonalMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual background mass monotonicity internally produces positive mass in the larger background; genuine envelope order and the existing proved positive-mass envelope theorem then produce actual composition. -/
theorem singularityEnvelope_comp_add_semipositive (omega : KahlerBackground n M)
    (θ η : ClosedRealOneOneForm n M) (hη : η.val.IsSemipositive)
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hpos : HasPositivePotentialMass θ u hu) :
    singularityEnvelope (θ + η).val (singularityEnvelope θ.val u) =
      singularityEnvelope (θ + η).val u := by
  have hu' := LocalPotentials.isThetaPshPotential_add_of_semipositive hu hη
  have huone : IsThetaPshPotential (θ + (1 : ℝ) • η).val u := by
    simpa only [one_smul] using hu'
  have hm : diagonalPotentialMass θ u hu ≤ diagonalPotentialMass (θ + η) u hu' := by
    simpa only [one_smul] using
      AmbientMassBackgroundMonotone.diagonalPotentialMass_le_add_smul hη
        (c := (1 : ℝ)) zero_lt_one hu huone
  have hpos' : HasPositivePotentialMass (θ + η) u hu' := lt_of_lt_of_le hpos hm
  have hbackground : singularityEnvelope θ.val u ≤ singularityEnvelope (θ + η).val u := by
    apply uscRegularization_mono
    apply sSup_le_sSup
    intro w hw
    exact ⟨⟨LocalPotentials.isThetaPshPotential_add_of_semipositive hw.1.1 hη,
      hw.1.2⟩, hw.2⟩
  apply le_antisymm
  · exact (singularityEnvelope_mono (θ := (θ + η).val)
      (MoreSingularOn.of_le fun x _ => hbackground x)).trans_eq
        (RooftopEnvelopeIdempotence.singularityEnvelope_idempotent_of_positive_mass
          omega (θ + η) u hu' hpos')
  · exact singularityEnvelope_mono (moreSingularOn_singularityEnvelope hu)

/-- Applying genuine envelope monotonicity to the original ordered envelopes and internally proved composition produces forward P-order transport to the actual semipositive larger background. -/
theorem pOrderWith_add_semipositive (omega : KahlerBackground n M)
    (θ η : ClosedRealOneOneForm n M) (hη : η.val.IsSemipositive)
    {u v : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (hupos : HasPositivePotentialMass θ u hu)
    (hvpos : HasPositivePotentialMass θ v hv) (huv : POrderWith θ u v) :
    POrderWith (θ + η) u v := by
  change singularityEnvelope (θ + η).val u ≤ singularityEnvelope (θ + η).val v
  rw [← singularityEnvelope_comp_add_semipositive omega θ η hη hu hupos,
    ← singularityEnvelope_comp_add_semipositive omega θ η hη hv hvpos]
  exact singularityEnvelope_mono (MoreSingularOn.of_le fun x _ => huv x)

end

end SGPT.Foundations.Analysis.Pending.SingularPositivePBackgroundTransport
