import SGPT.Foundations.Analysis.Pending.ModelRaySupremum
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasBasic
import SGPT.Foundations.Analysis.Pending.RelativePreceqStatements

set_option autoImplicit false

/-!
# Actual lower bounds on genuine suprema from Darvas boundedness

The actual model difference supremum (Xia SGPT PDF0103) and the actual
energy and metric laws (PDF0160--0161) independently produce the one-sided
estimate -mass(model) * sup u <= d1(u, model). Distance boundedness then
produces a uniform lower bound on the actual finite global suprema.
The opposite quantitative supremum inequality and completeness are separate.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelDarvasSupremumLowerBound

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses DiagonalMass FiniteUpperGapGeodesicSupremum

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ u : M → EReal} {hφ : IsModelPotential θ φ}

omit [ConnectedSpace M] in
private theorem energy_model_eq_zero (omega : KahlerBackground n M) :
    energy θ φ hφ φ = 0 := by
  rw [SingularModelEnergyCocycle.energy_eq_of_relativeEInfinity omega θ hφ
    ⟨hφ.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩,
    relativeEnergyOfMinimalType_self, EReal.coe_zero]

omit [ConnectedSpace M] in
private theorem modelVolume_pos (omega : KahlerBackground n M) :
    0 < modelVolume θ φ hφ := by
  let := DiagonalMeasureRegularity.isFiniteMeasure_diagonalPotentialMeasure
    omega θ hφ.plurisubharmonic
  exact ENNReal.toReal_pos hφ.positive_mass.ne' (measure_ne_top _ _)

/-- Actual model distance bounds the negative genuine global supremum for every singular model. -/
theorem neg_modelVolume_mul_iSup_le_relativeD1 (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) :
    -(modelVolume θ φ hφ) * (⨆ x, u x).toReal ≤ relativeD1 θ φ hφ u φ := by
  let : Nonempty M := ModelRaySupremum.nonempty_of_modelPotential hφ
  let S : ℝ := (⨆ x, u x).toReal
  have hSf := ModelRaySupremum.iSup_ne_top_ne_bot hu.1.plurisubharmonic
  have hS : (S : EReal) = ⨆ x, u x := EReal.coe_toReal hSf.1 hSf.2
  have hle : u ≤ fun x => φ x + (S : EReal) := by
    have h := le_add_differenceSup hφ.plurisubharmonic hu.1.relativePSHPreceq.2
    rw [ModelRaySupremum.differenceSup_eq_iSup hφ hu.1.relativePSHPreceq, ← hS] at h
    exact h
  have hφfinite : RelativeFiniteEnergyPreceq θ φ φ hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      ⟨hφ.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩
  have hEφ := energy_model_eq_zero (θ := θ) (φ := φ) (hφ := hφ) omega
  by_cases hs : S ≤ 0
  · have huleφ : u ≤ φ := fun x => (hle x).trans
      (add_le_of_nonpos_right (EReal.coe_nonpos.mpr hs))
    have hEshift : energy θ φ hφ (fun x => φ x + (S : EReal)) =
        ((S * modelVolume θ φ hφ : ℝ) : EReal) := by
      rw [SingularModelEnergyExtendedTranslation.energy_add_const omega φ S, hEφ, zero_add]
    have hEorder : (energy θ φ hφ u).toReal ≤ S * modelVolume θ φ hφ := by
      have he := energy_mono_of_le (hφ := hφ) hle
      rw [hEshift] at he
      simpa only [EReal.toReal_coe] using
        EReal.toReal_le_toReal he (SingularModelFiniteEnergyPreceq.bot_lt_energy omega hu).ne'
          (EReal.coe_ne_top _)
    rw [relativeD1_eq_sub_of_le hu.1.plurisubharmonic huleφ, hEφ, EReal.toReal_zero, zero_sub]
    change -(modelVolume θ φ hφ) * S ≤ -(energy θ φ hφ u).toReal
    nlinarith
  · have hm : 0 ≤ modelVolume θ φ hφ := (modelVolume_pos omega).le
    exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hm) (not_le.mp hs).le).trans
      (SingularModelDarvasBasic.relativeD1_nonneg omega hu hφfinite)

/-- A distance-bounded actual finite-energy family has a produced uniform genuine supremum lower bound. -/
theorem iSup_toReal_ge_neg_div_of_relativeD1_le {I : Type*}
    (omega : KahlerBackground n M) {ui : I → M → EReal}
    (hui : ∀ i, RelativeFiniteEnergyPreceq θ φ (ui i) hφ) {R : ℝ}
    (hR : ∀ i, relativeD1 θ φ hφ (ui i) φ ≤ R) (i : I) :
    -R / modelVolume θ φ hφ ≤ (⨆ x, ui i x).toReal := by
  have h := (neg_modelVolume_mul_iSup_le_relativeD1 omega (hui i)).trans (hR i)
  apply (div_le_iff₀ (modelVolume_pos omega)).mpr
  nlinarith

end

end SGPT.Foundations.Analysis.Pending.SingularModelDarvasSupremumLowerBound
