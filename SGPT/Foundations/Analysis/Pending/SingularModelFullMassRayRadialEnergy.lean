import SGPT.Foundations.Analysis.Pending.SingularModelSourceRayDistance
import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRayOrderedDistance

set_option autoImplicit false

/-!
# Actual extended radial energy of every full-mass source ray

Xia SGPT PDF0175 Definition 4.3.6 and equation (4.38), with an
independently proved extension to arbitrary full-mass initial points.
Actual canonical extended energy affinity classifies the finite and
negative-infinite cases internally and supplies genuine defining limits.
No bounded model, normalization, model origin, all-time E1, affinity or
radial-limit certificate is assumed.
-/

open Set Filter
open scoped Topology NNReal

namespace SGPT.Foundations.Analysis.Pending.SingularModelFullMassRayRadialEnergy

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativePreceqRays RelativeGeodesicRays SingularModelGeodesicRays
  SingularModelSourceRayInitialEnergy

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M}
  {φ : M → EReal} {hφ : IsModelPotential θ φ} {ℓ : ℝ → M → EReal}

/-- A genuine finite slice at any positive time internally forces finite energy of the actual full-mass initial source slice. -/
theorem relativeFiniteEnergyPreceq_ray_zero_of_finite_time (omega : KahlerBackground n M)
    (hℓ : IsRelativeGeodesicRayPreceq θ φ hφ ℓ) {t : ℝ} (ht : 0 < t)
    (hf : RelativeFiniteEnergyPreceq θ φ (ℓ t) hφ) :
    RelativeFiniteEnergyPreceq θ φ (ℓ 0) hφ := by
  refine (SingularModelFiniteEnergyPreceq.relativeFiniteEnergyPreceq_iff_bot_lt_energy
    omega (hℓ.1 0 le_rfl)).2 ?_
  by_contra hbot
  rw [not_lt, le_bot_iff] at hbot
  have h := SingularModelSourceRayInitialEnergy.energy_ray_preceq omega hℓ le_rfl
    (b := 2 * t) (by positivity) (s := 1 / 2) ⟨by norm_num, by norm_num⟩
  rw [show (0 : ℝ) + 1 / 2 * (2 * t - 0) = t by ring,
    hbot, EReal.coe_mul_bot_of_pos (by norm_num), EReal.bot_add] at h
  have hb := SingularModelFiniteEnergyPreceq.bot_lt_energy omega hf
  rw [h] at hb
  exact lt_irrefl _ hb

/-- Genuine finite energy at time one produces the entire original positive-time E1 source ray contract from actual full-mass geometry. -/
theorem isFiniteEnergyRayPreceq_of_finite_one (omega : KahlerBackground n M)
    (hℓ : IsRelativeGeodesicRayPreceq θ φ hφ ℓ)
    (h1 : RelativeFiniteEnergyPreceq θ φ (ℓ 1) hφ) :
    IsFiniteEnergyRayPreceq θ φ hφ ℓ := by
  have h0 := relativeFiniteEnergyPreceq_ray_zero_of_finite_time omega hℓ zero_lt_one h1
  refine ⟨hℓ, fun t ht => ?_⟩
  refine (SingularModelFiniteEnergyPreceq.relativeFiniteEnergyPreceq_iff_bot_lt_energy
    omega (hℓ.1 t ht.le)).2 ?_
  rcases le_or_gt t 1 with ht1 | ht1
  · have h := SingularModelSourceRayInitialEnergy.energy_ray_preceq omega hℓ le_rfl
      zero_lt_one (s := t) ⟨ht.le, ht1⟩
    rw [show (0 : ℝ) + t * (1 - 0) = t by ring,
      ← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega h0,
      ← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega h1,
      ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at h
    rw [h]
    exact EReal.bot_lt_coe _
  · by_contra hbot
    rw [not_lt, le_bot_iff] at hbot
    have h := SingularModelSourceRayInitialEnergy.energy_ray_preceq omega hℓ le_rfl ht
      (s := 1 / t) ⟨by positivity, (div_le_one ht).mpr ht1.le⟩
    rw [show (0 : ℝ) + 1 / t * (t - 0) = 1 by field_simp; ring,
      hbot, EReal.coe_mul_bot_of_pos (by positivity), EReal.add_bot] at h
    have hb := SingularModelFiniteEnergyPreceq.bot_lt_energy omega h1
    rw [h] at hb
    exact lt_irrefl _ hb

/-- Every actual full-mass source ray has its genuine defining extended radial energy limit, with the finite or negative-infinite case internally determined by its actual time-one energy. -/
theorem tendsto_radialEnergy_of_fullMass (omega : KahlerBackground n M)
    (hℓ : IsRelativeGeodesicRayPreceq θ φ hφ ℓ) :
    Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : EReal) * energy θ φ hφ (ℓ t)) atTop
      (𝓝 (if energy θ φ hφ (ℓ 1) = ⊥ then ⊥ else
        (((energy θ φ hφ (ℓ 1)).toReal - (energy θ φ hφ (ℓ 0)).toReal : ℝ) : EReal))) := by
  by_cases h1 : energy θ φ hφ (ℓ 1) = ⊥
  · rw [if_pos h1]
    have htail (t : ℝ) (ht : 1 ≤ t) : energy θ φ hφ (ℓ t) = ⊥ := by
      by_contra hne
      have htpos : 0 < t := zero_lt_one.trans_le ht
      have hf : RelativeFiniteEnergyPreceq θ φ (ℓ t) hφ :=
        (SingularModelFiniteEnergyPreceq.relativeFiniteEnergyPreceq_iff_bot_lt_energy
          omega (hℓ.1 t htpos.le)).2 (lt_of_le_of_ne bot_le (Ne.symm hne))
      have h0 := relativeFiniteEnergyPreceq_ray_zero_of_finite_time omega hℓ htpos hf
      have h := SingularModelSourceRayInitialEnergy.energy_ray_preceq omega hℓ le_rfl htpos
        (s := 1 / t) ⟨by positivity, (div_le_one htpos).mpr ht⟩
      rw [show (0 : ℝ) + 1 / t * (t - 0) = 1 by field_simp; ring,
        ← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega h0,
        ← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega hf,
        ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at h
      have hb : ⊥ < energy θ φ hφ (ℓ 1) := by
        rw [h]
        exact EReal.bot_lt_coe _
      rw [h1] at hb
      exact lt_irrefl _ hb
    refine (tendsto_const_nhds : Tendsto (fun _ : ℝ => (⊥ : EReal)) atTop (𝓝 ⊥)).congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    rw [htail t ht.le, EReal.coe_mul_bot_of_pos (inv_pos.mpr (zero_lt_one.trans ht))]
  · rw [if_neg h1]
    have hf1 : RelativeFiniteEnergyPreceq θ φ (ℓ 1) hφ :=
      (SingularModelFiniteEnergyPreceq.relativeFiniteEnergyPreceq_iff_bot_lt_energy
        omega (hℓ.1 1 zero_le_one)).2 (lt_of_le_of_ne bot_le (Ne.symm h1))
    have hF := isFiniteEnergyRayPreceq_of_finite_one omega hℓ hf1
    have hT := SingularModelGeodesicRayEnergy.tendsto_radialEnergy omega (nativeRay omega hF)
    rw [nativeRay_reader_eq omega hF zero_le_one, nativeRay_reader_eq omega hF le_rfl] at hT
    refine hT.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [nativeRay_reader_eq omega hF ht.le]

/-- The existing defining radial energy of every genuine full-mass source ray is its actual extended limit, including the genuinely negative-infinite case. -/
theorem radialEnergy_eq_of_fullMass (omega : KahlerBackground n M)
    (hℓ : IsRelativeGeodesicRayPreceq θ φ hφ ℓ) :
    radialEnergy θ φ hφ ℓ =
      if energy θ φ hφ (ℓ 1) = ⊥ then ⊥ else
        (((energy θ φ hφ (ℓ 1)).toReal - (energy θ φ hφ (ℓ 0)).toReal : ℝ) : EReal) :=
  (tendsto_radialEnergy_of_fullMass omega hℓ).limUnder_eq

private theorem source_distance_eq_readers (omega : KahlerBackground n M)
    {ℓ ℓ' : ℝ → M → EReal}
    (hℓ : IsFiniteEnergyRayPreceq θ φ hφ ℓ)
    (hℓ' : IsFiniteEnergyRayPreceq θ φ hφ ℓ') :
    rayD1 θ φ hφ ℓ ℓ' = rayD1 θ φ hφ
      (nativeRay omega hℓ).rawCurve (nativeRay omega hℓ').rawCurve := by
  unfold rayD1 Filter.limUnder
  apply congrArg Filter.lim
  apply Filter.map_congr
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [nativeRay_reader_eq omega hℓ ht.le, nativeRay_reader_eq omega hℓ' ht.le]

private theorem source_radialEnergy_eq_reader (omega : KahlerBackground n M)
    (hℓ : IsFiniteEnergyRayPreceq θ φ hφ ℓ) :
    radialEnergy θ φ hφ ℓ = radialEnergy θ φ hφ (nativeRay omega hℓ).rawCurve := by
  have hN := SingularModelGeodesicRayEnergy.tendsto_radialEnergy omega (nativeRay omega hℓ)
  have hs : Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : EReal) * energy θ φ hφ (ℓ t)) atTop
      (𝓝 (((energy θ φ hφ ((nativeRay omega hℓ).rawCurve 1)).toReal -
        (energy θ φ hφ ((nativeRay omega hℓ).rawCurve 0)).toReal : ℝ) : EReal)) := by
    refine hN.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [nativeRay_reader_eq omega hℓ ht.le]
  exact hs.limUnder_eq.trans hN.limUnder_eq.symm

/-- Actual ordered original positive-time E1 source rays obey the defining radial distance identity, with arbitrary initial slices and internally produced initial finite energy. -/
theorem rayD1_eq_radialEnergy_sub (omega : KahlerBackground n M)
    {ℓ ℓ' : ℝ → M → EReal}
    (hℓ : IsFiniteEnergyRayPreceq θ φ hφ ℓ)
    (hℓ' : IsFiniteEnergyRayPreceq θ φ hφ ℓ')
    (hle : ∀ t : ℝ, 0 ≤ t → ℓ t ≤ ℓ' t) :
    rayD1 θ φ hφ ℓ ℓ' = radialEnergy θ φ hφ ℓ' - radialEnergy θ φ hφ ℓ := by
  have horder : ∀ t : ℝ, 0 ≤ t → (nativeRay omega hℓ).rawCurve t ≤
      (nativeRay omega hℓ').rawCurve t := by
    intro t ht
    rw [nativeRay_reader_eq omega hℓ ht, nativeRay_reader_eq omega hℓ' ht]
    exact hle t ht
  rw [source_distance_eq_readers omega hℓ hℓ',
    source_radialEnergy_eq_reader omega hℓ', source_radialEnergy_eq_reader omega hℓ]
  exact SingularModelGeodesicRayOrderedDistance.rayD1_eq_radialEnergy_sub omega
    (nativeRay omega hℓ) (nativeRay omega hℓ') horder

end

end SGPT.Foundations.Analysis.Pending.SingularModelFullMassRayRadialEnergy
