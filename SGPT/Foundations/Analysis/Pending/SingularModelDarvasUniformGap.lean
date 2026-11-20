import SGPT.Foundations.Analysis.Pending.SingularModelFiniteRealEnergy
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasMetricSpace

set_option autoImplicit false

/-!
# Actual uniform finite extended-gap energy and Darvas control

An independent quantitative adaptation of Xia SGPT PDF0118's energy
translation/order and PDF0172's finite affine barriers. Actual translated
E1 membership, actual energy order, and the genuine rooftop universal
property produce the actual energy bound and a factor-three Darvas bound.
No model boundedness or pointwise finiteness is imposed.
-/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularModelDarvasUniformGap

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal} {hφ : IsModelPotential θ φ}

omit [ConnectedSpace M] in
/-- Actual finite model energy is controlled by actual finite extended barriers. -/
theorem abs_toReal_energy_sub_le_of_extended_barriers (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    {ε : ℝ} (hl : ∀ x, u x + ((-ε : ℝ) : EReal) ≤ v x)
    (hh : ∀ x, v x ≤ u x + (ε : EReal)) :
    |(energy θ φ hφ v).toReal - (energy θ φ hφ u).toReal| ≤
      ε * modelVolume θ φ hφ := by
  have hlo := SingularModelFiniteRealEnergy.toReal_energy_mono omega
    (hu.add_const omega (-ε)) hv hl
  have hhi := SingularModelFiniteRealEnergy.toReal_energy_mono omega
    hv (hu.add_const omega ε) hh
  rw [SingularModelFiniteRealEnergy.toReal_energy_add_const omega hu] at hlo hhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Actual uniform extended barriers produce an actual Darvas bound, with no target-distance premise. -/
theorem relativeD1_le_of_extended_barriers (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    {ε : ℝ} (hε : 0 ≤ ε) (hl : ∀ x, u x + ((-ε : ℝ) : EReal) ≤ v x)
    (hh : ∀ x, v x ≤ u x + (ε : EReal)) :
    relativeD1 θ φ hφ u v ≤ 3 * ε * modelVolume θ φ hφ := by
  have hr := relativeFiniteEnergyPreceq_rooftop omega hu hv
  have hminus := hu.add_const omega (-ε)
  have hlow : (fun x => u x + ((-ε : ℝ) : EReal)) ≤ rooftop θ u v := by
    apply (le_rooftop_iff hu.1.plurisubharmonic hv.1.plurisubharmonic
      hminus.1.plurisubharmonic).mpr
    refine ⟨?_, hl⟩
    intro x
    calc
      _ ≤ u x + (0 : EReal) := add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (neg_nonpos.mpr hε))
      _ = u x := add_zero _
  have hro := SingularModelFiniteRealEnergy.toReal_energy_mono omega hminus hr hlow
  have hhi := SingularModelFiniteRealEnergy.toReal_energy_mono omega hv (hu.add_const omega ε) hh
  rw [SingularModelFiniteRealEnergy.toReal_energy_add_const omega hu] at hro hhi
  unfold relativeD1
  linarith

end

end SGPT.Foundations.Analysis.Pending.SingularModelDarvasUniformGap
