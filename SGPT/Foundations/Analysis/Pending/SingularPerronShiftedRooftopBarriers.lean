import SGPT.Foundations.Analysis.Pending.SingularModelFiniteRealEnergy
import SGPT.Foundations.Analysis.FirstPass.FiniteGeodesicRooftopEndpoint

set_option autoImplicit false

/-! # Actual shifted rooftop competitors bound general singular Perron energies -/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularPerronShiftedRooftopBarriers

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M}
  {φ u₀ u₁ : M → EReal} {hφ : IsModelPotential θ φ}

/-- Genuine E1 rooftop closure and its two actual obstacle bounds internally produce the left affine Perron competitor. -/
theorem shifted_rooftop_affine_lower_left (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ) (C t : ℝ) :
    (fun x => rooftop θ u₀ (fun y => u₁ y + (C : EReal)) x +
      (((-C) * t : ℝ) : EReal)) ≤ finiteGeodesic θ.val u₀ u₁ t := by
  have hv := hu₁.add_const omega C
  have hw := relativeFiniteEnergyPreceq_rooftop omega hu₀ hv
  exact affineRooftopLower_le_finiteGeodesic hw.1.plurisubharmonic
    (rooftop_le_left hu₀.1.plurisubharmonic hv.1.plurisubharmonic)
    (rooftop_le_right hu₀.1.plurisubharmonic hv.1.plurisubharmonic) t

/-- Exchanging the actual endpoints and reversing Perron time produces the right shifted rooftop barrier, preserving poles. -/
theorem shifted_rooftop_affine_lower_right (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ) (C t : ℝ) :
    (fun x => rooftop θ u₁ (fun y => u₀ y + (C : EReal)) x +
      (((-C) * (1 - t) : ℝ) : EReal)) ≤ finiteGeodesic θ.val u₀ u₁ t := by
  have h := shifted_rooftop_affine_lower_left omega hu₁ hu₀ C (1 - t)
  rwa [finiteGeodesic_timeReversal, sub_sub_cancel] at h

/-- Actual finite-energy monotonicity and the true singular-model energy translation turn the left genuine Perron barrier into its real energy lower bound. -/
theorem toReal_energy_shifted_rooftop_lower_left (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ) (C : ℝ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (energy θ φ hφ (rooftop θ u₀ (fun x => u₁ x + (C : EReal)))).toReal -
      C * t * modelVolume θ φ hφ ≤
        (energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t)).toReal := by
  have hw := relativeFiniteEnergyPreceq_rooftop omega hu₀ (hu₁.add_const omega C)
  have h := SingularModelFiniteRealEnergy.toReal_energy_mono omega
    (hw.add_const omega ((-C) * t))
    (relativeFiniteEnergyPreceq_finiteGeodesic omega hu₀ hu₁ ht)
    (shifted_rooftop_affine_lower_left omega hu₀ hu₁ C t)
  rw [SingularModelFiniteRealEnergy.toReal_energy_add_const omega hw] at h
  simpa only [neg_mul, sub_eq_add_neg] using h

/-- The second actual affine competitor gives the corresponding real energy lower bound at the terminal endpoint. -/
theorem toReal_energy_shifted_rooftop_lower_right (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ) (C : ℝ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (energy θ φ hφ (rooftop θ u₁ (fun x => u₀ x + (C : EReal)))).toReal -
      C * (1 - t) * modelVolume θ φ hφ ≤
        (energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t)).toReal := by
  have hw := relativeFiniteEnergyPreceq_rooftop omega hu₁ (hu₀.add_const omega C)
  have h := SingularModelFiniteRealEnergy.toReal_energy_mono omega
    (hw.add_const omega ((-C) * (1 - t)))
    (relativeFiniteEnergyPreceq_finiteGeodesic omega hu₀ hu₁ ht)
    (shifted_rooftop_affine_lower_right omega hu₀ hu₁ C t)
  rw [SingularModelFiniteRealEnergy.toReal_energy_add_const omega hw] at h
  simpa only [neg_mul, sub_eq_add_neg] using h

end

end SGPT.Foundations.Analysis.Pending.SingularPerronShiftedRooftopBarriers
