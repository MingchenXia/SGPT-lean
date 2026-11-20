import SGPT.Foundations.Analysis.Pending.SingularModelEnergyTranslation
import SGPT.Foundations.Analysis.Pending.RelativePreceqClasses

set_option autoImplicit false

/-!
# Extended energy translation for singular models

Xia SGPT PDF0118, equation (3.31). Finite-type energy translation acts on
the actual same-type majorants by a genuine bijection. Their infima therefore
translate by the actual model volume. No boundedness of the model is assumed.
-/

open Set MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyExtendedTranslation

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar RelativeEnergy
  RelativeDarvasDistance RelativePreceqClasses DiagonalMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] {θ : ClosedRealOneOneForm n M} {φ : M → EReal}
  {hφ : IsModelPotential θ φ}

/-- Actual same-type majorant energy translates for an arbitrarily singular model. -/
theorem relativeEnergyOfMinimalType_add_const (omega : KahlerBackground n M)
    {v : M → EReal} (hv : RelativeEInfinity θ φ v) (c : ℝ)
    (hvc : RelativeEInfinity θ φ (fun x => v x + (c : EReal))) :
    relativeEnergyOfMinimalType θ φ _ hφ.plurisubharmonic hvc.1 =
      relativeEnergyOfMinimalType θ φ v hφ.plurisubharmonic hv.1 + c * modelVolume θ φ hφ := by
  have e : (fun x => v x - ((-c : ℝ) : EReal)) = fun x => v x + (c : EReal) := by
    funext x
    rw [sub_eq_add_neg, EReal.coe_neg, neg_neg]
  have h := SingularModelEnergyTranslation.relativeEnergyOfMinimalType_sub_const
    omega θ hφ.plurisubharmonic hv.1 hv.2 (-c)
  rw [relativeEnergyOfMinimalType_congr hφ.plurisubharmonic e _ hvc.1] at h
  rw [h, modelVolume]
  simp only [diagonalPotentialMeasure]
  ring

/-- Actual translated majorants give one inequality between the energy infima. -/
theorem energy_add_coe_le (omega : KahlerBackground n M)
    (u : M → EReal) (c : ℝ) :
    energy θ φ hφ u + ((c * modelVolume θ φ hφ : ℝ) : EReal) ≤
      energy θ φ hφ (fun x => u x + (c : EReal)) := by
  refine le_sInf ?_
  rintro e ⟨w, hw, huw, rfl⟩
  have hv := RelativePreceqClasses.RelativeEInfinity.add_const hw (-c)
  have huv : u ≤ fun x => w x + ((-c : ℝ) : EReal) :=
    fun x => (add_coe_le_iff _ _ c).1 (huw x)
  have hle : energy θ φ hφ u ≤
      (relativeEnergyOfMinimalType θ φ _ hφ.plurisubharmonic hv.1 : EReal) :=
    sInf_le ⟨_, hv, huv, rfl⟩
  have hw' : RelativeEInfinity θ φ (fun x => (w x + ((-c : ℝ) : EReal)) + (c : EReal)) := by
    simpa only [show ((c : ℝ) : EReal) = ((-(-c) : ℝ) : EReal) by rw [neg_neg],
      translate_translate_neg] using hw
  have hE := relativeEnergyOfMinimalType_add_const (hφ := hφ) omega hv c hw'
  have ew : (fun x => (w x + ((-c : ℝ) : EReal)) + (c : EReal)) = w := by
    simpa only [neg_neg] using translate_translate_neg w (-c)
  rw [relativeEnergyOfMinimalType_congr hφ.plurisubharmonic ew hw'.1 hw.1] at hE
  rw [hE, EReal.coe_add]
  exact add_le_add hle le_rfl

/-- The full extended energy translation formula for singular models. -/
theorem energy_add_const (omega : KahlerBackground n M) (u : M → EReal) (c : ℝ) :
    energy θ φ hφ (fun x => u x + (c : EReal)) =
      energy θ φ hφ u + ((c * modelVolume θ φ hφ : ℝ) : EReal) := by
  refine le_antisymm ?_ (energy_add_coe_le omega u c)
  have h := energy_add_coe_le (hφ := hφ) omega (fun x => u x + (c : EReal)) (-c)
  rw [translate_translate_neg, show -c * modelVolume θ φ hφ = -(c * modelVolume θ φ hφ) by ring,
    add_coe_le_iff, neg_neg] at h
  exact h

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyExtendedTranslation
