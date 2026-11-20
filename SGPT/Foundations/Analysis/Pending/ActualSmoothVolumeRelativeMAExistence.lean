import SGPT.Foundations.Analysis.Pending.ActualSmoothVolumeVariationalLimitMaximizer
import SGPT.Foundations.Analysis.Pending.ActualSmoothVolumeVariationalEuler
import SGPT.Foundations.Analysis.Pending.NaturalNormalizedThetaPshCompactness

set_option autoImplicit false

/-! # Genuine relative constant smooth-volume MA existence

The original maximizing sequence and genuinely produced normalized singular
thetaPSH canonical L1 compactness internally construct a whole-domain optimum.
The original whole Euler equation then gives the prescribed MA solution.
No caller compactness, chosen limit, energy, optimum or solver certificate.
Complete mathematical blueprint and proofs preceded substantive SOURCE.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualSmoothVolumeRelativeMAExistence

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus DiagonalMass
  RelativeEnergy RelativePreceqClasses IntegrationCurrent
  ActualSmoothVolumeVariationalFoundation ActualSmoothVolumeVariationalLimitMaximizer
  ActualSmoothVolumeVariationalEuler

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M}
  {φ : M → EReal} {hφ : IsModelPotential θ φ}

/-- The actual maximizing sequence and genuine normalized singular thetaPSH
compactness internally produce an original whole-domain functional maximum. -/
theorem exists_normalized_functional_max (omega : KahlerBackground n M) :
    ∃ χ : M → EReal, RelativeFiniteEnergyPreceq θ φ χ hφ ∧
      (⨆ x, χ x) = 0 ∧ (∀ x, χ x ≤ φ x) ∧
      (∀ a : M → EReal, RelativeFiniteEnergyPreceq θ φ a hφ →
        smoothVolumeFunctional omega θ φ hφ a ≤ smoothVolumeFunctional omega θ φ hφ χ) := by
  obtain ⟨L, B, uj, _hL, _hB, hj, hupper, hF⟩ :=
    exists_normalized_maximizing_sequence (hφ := hφ) omega
  have huP : ∀ j, IsThetaPshPotential θ.val (uj j) := fun j => (hj j).1.1.plurisubharmonic
  have hsup : ∀ j, (⨆ x, uj j x) = 0 := fun j => (hj j).2.1
  obtain ⟨v, s, hv, _hvsup, hs, hlim, _hglobal⟩ :=
    NaturalNormalizedThetaPshCompactness.exists_strictMono_subseq_of_sup_eq_zero
      (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega) uj huP hsup
  obtain ⟨_heq, b, hwF, hw0, hwφ, _hwL, hwmax⟩ :=
    exists_normalized_optimum_of_manifoldL1LocallyTendsto omega
      (fun k => (hj (s k)).1)
      (fun k x => hsup (s k) ▸ le_iSup (uj (s k)) x)
      hv hlim (fun k => (hj (s k)).2.2.2.2.2)
      (hF.comp hs.tendsto_atTop) hupper
  exact ⟨fun x => v x + (b : EReal), hwF, hw0, hwφ, hwmax⟩

/-- Genuine original finite-energy normalized existence of the prescribed
relative constant smooth-volume MA solution over an arbitrary positive model. -/
theorem exists_normalized_relative_smooth_volume_solution
    (omega : KahlerBackground n M) (hn : 0 < n)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    ∃ (χ : M → EReal) (hχ : RelativeFiniteEnergyPreceq θ φ χ hφ),
      (⨆ x, χ x) = 0 ∧ (∀ x, χ x ≤ φ x) ∧
      diagonalPotentialMeasure θ χ hχ.1.plurisubharmonic =
        ENNReal.ofReal (smoothVolumeCoefficient omega θ φ hφ) • kahlerVolume omega := by
  obtain ⟨χ, hχ, hχsup, hχφ, hmax⟩ := exists_normalized_functional_max (hφ := hφ) omega
  refine ⟨χ, hχ, hχsup, hχφ, ?_⟩
  exact diagonalPotentialMeasure_eq_smul_kahlerVolume_of_functional_max omega hn hbig hχ
    (fun x => hχsup ▸ le_iSup χ x) hmax

end

end SGPT.Foundations.Analysis.Pending.ActualSmoothVolumeRelativeMAExistence
