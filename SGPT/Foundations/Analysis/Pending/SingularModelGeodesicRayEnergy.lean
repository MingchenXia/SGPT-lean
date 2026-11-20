import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRays

set_option autoImplicit false

/-! # Actual energy and radial energy of arbitrary singular-model native rays -/

open Set Filter
open scoped Topology NNReal

namespace SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRayEnergy

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelGeodesicRays

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M}
  {φ : M → EReal} {hφ : IsModelPotential θ φ}

/-- Actual finite-interval energy affinity is produced from the ray's genuine Perron geometry and the proved general singular E1 segment theorem. -/
theorem toReal_energy_combination (omega : KahlerBackground n M)
    (L : ModelFiniteEnergyGeodesicRay θ φ hφ) (a b : ℝ≥0) (hab : a < b)
    (s : Icc (0 : ℝ) 1) :
    (energy θ φ hφ (L.rawCurve ((1 - s.val) * a + s.val * b))).toReal =
      (1 - s.val) * (energy θ φ hφ (L.rawCurve a)).toReal +
        s.val * (energy θ φ hφ (L.rawCurve b)).toReal := by
  rw [L.rawCurve_segment_eq a b hab s]
  exact SingularGeodesicGeneralEnergyAffinity.toReal_energy_closedSubgeodesicSlice_eq_chord
    omega (L.finiteEnergy_rawCurve a) (L.finiteEnergy_rawCurve b) s.property

/-- The defining extended energy obeys the actual finite-interval ray chord formula. -/
theorem energy_combination (omega : KahlerBackground n M)
    (L : ModelFiniteEnergyGeodesicRay θ φ hφ) (a b : ℝ≥0) (hab : a < b)
    (s : Icc (0 : ℝ) 1) :
    energy θ φ hφ (L.rawCurve ((1 - s.val) * a + s.val * b)) =
      ((1 - s.val : ℝ) : EReal) * energy θ φ hφ (L.rawCurve a) +
        (s.val : EReal) * energy θ φ hφ (L.rawCurve b) := by
  rw [L.rawCurve_segment_eq a b hab s]
  exact SingularGeodesicGeneralEnergyAffinity.energy_closedSubgeodesicSlice_eq_chord
    omega (L.finiteEnergy_rawCurve a) (L.finiteEnergy_rawCurve b) s.property

/-- A genuine native E1 ray has linear real energy from its arbitrary actual initial point, without a bounded-model or same-type hypothesis. -/
theorem toReal_energy_ray (omega : KahlerBackground n M)
    (L : ModelFiniteEnergyGeodesicRay θ φ hφ) {t : ℝ} (ht : 0 ≤ t) :
    (energy θ φ hφ (L.rawCurve t)).toReal =
      (energy θ φ hφ (L.rawCurve 0)).toReal +
        t * ((energy θ φ hφ (L.rawCurve 1)).toReal -
          (energy θ φ hφ (L.rawCurve 0)).toReal) := by
  rcases le_or_gt t 1 with h1 | h1
  · have h := toReal_energy_combination omega L 0 1 (by norm_num) ⟨t, ht, h1⟩
    simp only [NNReal.coe_zero, NNReal.coe_one, mul_zero, zero_add, mul_one] at h
    rw [h]
    ring
  · have htpos : 0 < t := zero_lt_one.trans h1
    let b : ℝ≥0 := ⟨t, ht⟩
    have h := toReal_energy_combination omega L 0 b htpos
      ⟨1 / t, by positivity, (div_le_one htpos).2 h1.le⟩
    change (energy θ φ hφ (L.rawCurve ((1 - 1 / t) * 0 + (1 / t) * t))).toReal =
      (1 - 1 / t) * (energy θ φ hφ (L.rawCurve 0)).toReal +
        (1 / t) * (energy θ φ hφ (L.rawCurve t)).toReal at h
    rw [show (1 - 1 / t) * 0 + (1 / t) * t = (1 : ℝ) by
      rw [mul_zero, zero_add, one_div, inv_mul_cancel₀ htpos.ne']] at h
    rw [h]
    field_simp
    ring

/-- Genuine finite energy realifies the ray's actual linear energy identity in the defining extended-real energy. -/
theorem energy_ray (omega : KahlerBackground n M)
    (L : ModelFiniteEnergyGeodesicRay θ φ hφ) {t : ℝ} (ht : 0 ≤ t) :
    energy θ φ hφ (L.rawCurve t) = energy θ φ hφ (L.rawCurve 0) +
      (t : EReal) * (energy θ φ hφ (L.rawCurve 1) - energy θ φ hφ (L.rawCurve 0)) := by
  rw [← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega (L.finiteEnergy_rawCurve t),
    ← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega (L.finiteEnergy_rawCurve 0),
    ← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega (L.finiteEnergy_rawCurve 1),
    ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_add, toReal_energy_ray omega L ht]

/-- The defining radial-energy integrand actually converges to the finite energy slope over an arbitrary singular model. -/
theorem tendsto_radialEnergy (omega : KahlerBackground n M)
    (L : ModelFiniteEnergyGeodesicRay θ φ hφ) :
    Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : EReal) * energy θ φ hφ (L.rawCurve t)) atTop
      (𝓝 (((energy θ φ hφ (L.rawCurve 1)).toReal -
        (energy θ φ hφ (L.rawCurve 0)).toReal : ℝ) : EReal)) := by
  set e0 := (energy θ φ hφ (L.rawCurve 0)).toReal
  set m := (energy θ φ hφ (L.rawCurve 1)).toReal - e0
  have hlim : Tendsto (fun t : ℝ => t⁻¹ * e0 + m) atTop (𝓝 m) := by
    simpa using (tendsto_inv_atTop_zero.mul_const e0).add_const m
  refine (EReal.tendsto_coe.2 hlim).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega (L.finiteEnergy_rawCurve t),
    ← EReal.coe_mul, toReal_energy_ray omega L ht.le]
  congr 1
  field_simp
  ring

/-- The existing radial energy definition equals the genuine finite slope, by the actual convergent defining integrand. -/
theorem radialEnergy_eq (omega : KahlerBackground n M)
    (L : ModelFiniteEnergyGeodesicRay θ φ hφ) :
    RelativeGeodesicRays.radialEnergy θ φ hφ L.rawCurve =
      (((energy θ φ hφ (L.rawCurve 1)).toReal -
        (energy θ φ hφ (L.rawCurve 0)).toReal : ℝ) : EReal) :=
  (tendsto_radialEnergy omega L).limUnder_eq

end

end SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRayEnergy
