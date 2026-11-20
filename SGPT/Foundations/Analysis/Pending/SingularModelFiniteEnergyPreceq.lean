import SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergy
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyExtendedTranslation

set_option autoImplicit false

/-!
# Finite energy on Xia's singularity-order full-mass domain

Xia SGPT PDF0121--0122, Proposition 3.1.17. Actual finite translations
preserve the genuine full-mass class and finiteness of its canonical gap
integral. The actual singular-reference energy translation formula then
transfers the normalized characterization to the source domain `u ⪯ φ`.
-/

namespace SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyPreceq

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] {θ : ClosedRealOneOneForm n M} {φ u : M → EReal}
  {hφ : IsModelPotential θ φ}

/-- Within Xia's actual full-mass singularity-order class, finite energy is
equivalent to extended energy greater than negative infinity for any model. -/
theorem relativeFiniteEnergyPreceq_iff_bot_lt_energy (omega : KahlerBackground n M)
    (hfull : RelativeFullMassPreceq θ φ u hφ) :
    RelativeFiniteEnergyPreceq θ φ u hφ ↔ ⊥ < energy θ φ hφ u := by
  obtain ⟨C, hC⟩ := hfull.relativePSHPreceq.exists_add_le
  have hnormalized := hfull.relativeFullMass_add (hC C le_rfl)
  have hiff := SingularModelFiniteEnergy.relativeFiniteEnergy_iff_bot_lt_energy
    omega θ hφ hnormalized
  rw [SingularModelEnergyExtendedTranslation.energy_add_const omega u C,
    bot_lt_add_coe_iff] at hiff
  constructor
  · intro hf
    exact hiff.mp (hf.relativeFiniteEnergy_add omega (hC C le_rfl))
  · intro hbot
    exact relativeFiniteEnergyPreceq_of_add omega
      (preceq_of_relativeFiniteEnergy (hiff.mpr hbot))

/-- A genuine finite-energy potential over an arbitrarily singular model
has extended energy greater than negative infinity. -/
theorem bot_lt_energy (omega : KahlerBackground n M)
    (hfinite : RelativeFiniteEnergyPreceq θ φ u hφ) : ⊥ < energy θ φ hφ u :=
  (relativeFiniteEnergyPreceq_iff_bot_lt_energy omega hfinite.1).mp hfinite

/-- Both infinite values are excluded by the actual finite-energy class,
so its defining energy agrees with its real value for a singular model. -/
theorem coe_toReal_energy (omega : KahlerBackground n M)
    (hfinite : RelativeFiniteEnergyPreceq θ φ u hφ) :
    ((energy θ φ hφ u).toReal : EReal) = energy θ φ hφ u :=
  EReal.coe_toReal (energy_ne_top_of_preceq hfinite.1.relativePSHPreceq)
    (bot_lt_energy omega hfinite).ne'

end

end SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyPreceq
