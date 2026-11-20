import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRayEnergy

set_option autoImplicit false

/-! # Actual radial energy for Xia's rays from arbitrarily singular models -/

open Set Filter
open scoped Topology NNReal

namespace SGPT.Foundations.Analysis.Pending.SingularModelOriginRayEnergy

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativePreceqRays SingularModelGeodesicRays

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M}
  {φ : M → EReal} {hφ : IsModelPotential θ φ} {ℓ : ℝ → M → EReal}

omit [ConnectedSpace M] in
private theorem model_origin_reader_eq (omega : KahlerBackground n M)
    (hℓ : IsFiniteEnergyRayFromModel θ φ hφ ℓ) {t : ℝ} (ht : 0 ≤ t) :
    (ModelFiniteEnergyGeodesicRay.ofFiniteEnergyRayFromModel omega hℓ).rawCurve t = ℓ t := by
  change ℓ (max t 0) = ℓ t
  rw [max_eq_left ht]

omit [ConnectedSpace M] in
private theorem energy_model_eq_zero (omega : KahlerBackground n M) :
    energy θ φ hφ φ = 0 := by
  rw [SingularModelEnergyCocycle.energy_eq_of_relativeEInfinity omega θ hφ
    ⟨hφ.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩,
    relativeEnergyOfMinimalType_self, EReal.coe_zero]

/-- The original genuine source R1 ray has a convergent defining radial integrand, with no bounded-model or affinity premise. -/
theorem tendsto_radialEnergy (omega : KahlerBackground n M)
    (hℓ : IsFiniteEnergyRayFromModel θ φ hφ ℓ) :
    Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : EReal) * energy θ φ hφ (ℓ t)) atTop
      (𝓝 (energy θ φ hφ (ℓ 1))) := by
  let L := ModelFiniteEnergyGeodesicRay.ofFiniteEnergyRayFromModel omega hℓ
  have hlim := SingularModelGeodesicRayEnergy.tendsto_radialEnergy omega L
  have h0 : L.rawCurve 0 = φ := (model_origin_reader_eq omega hℓ le_rfl).trans hℓ.2
  have h1 : L.rawCurve 1 = ℓ 1 := model_origin_reader_eq omega hℓ zero_le_one
  rw [h0, h1, energy_model_eq_zero omega, EReal.toReal_zero, sub_zero,
    SingularModelFiniteEnergyPreceq.coe_toReal_energy omega (hℓ.1.2 1 zero_lt_one)] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [model_origin_reader_eq omega hℓ ht.le]

/-- The existing radial-energy value of a genuine source ray from any singular model is its actual defining energy at time one. -/
theorem radialEnergy_eq_energy_one (omega : KahlerBackground n M)
    (hℓ : IsFiniteEnergyRayFromModel θ φ hφ ℓ) :
    RelativeGeodesicRays.radialEnergy θ φ hφ ℓ = energy θ φ hφ (ℓ 1) :=
  (tendsto_radialEnergy omega hℓ).limUnder_eq

/-- The original actual source R1 contract internally yields defining energy scaling by the existing radial energy, for every nonnegative time and arbitrary singular model. -/
theorem energy_ray_eq_mul_radialEnergy (omega : KahlerBackground n M)
    (hℓ : IsFiniteEnergyRayFromModel θ φ hφ ℓ) {t : ℝ} (ht : 0 ≤ t) :
    energy θ φ hφ (ℓ t) =
      (t : EReal) * RelativeGeodesicRays.radialEnergy θ φ hφ ℓ := by
  let L := ModelFiniteEnergyGeodesicRay.ofFiniteEnergyRayFromModel omega hℓ
  have h := SingularModelGeodesicRayEnergy.energy_ray omega L ht
  rw [model_origin_reader_eq omega hℓ ht, model_origin_reader_eq omega hℓ le_rfl,
    model_origin_reader_eq omega hℓ zero_le_one, hℓ.2, energy_model_eq_zero omega,
    sub_zero, zero_add] at h
  rw [radialEnergy_eq_energy_one omega hℓ]
  exact h

end

end SGPT.Foundations.Analysis.Pending.SingularModelOriginRayEnergy
