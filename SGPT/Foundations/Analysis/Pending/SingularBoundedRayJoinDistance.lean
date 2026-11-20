import SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinEnergy
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasMaximumSumBound
import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRayOrderedDistance
import SGPT.Foundations.Analysis.Pending.SingularModelOriginRayDistance

set_option autoImplicit false

/-! # The actual bounded ray join and its precise source distance control -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinDistance

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativePreceqRays RelativeGeodesicRays
  SingularBoundedRayJoinStages SingularBoundedRayJoinSlices
  SingularBoundedRayJoinRay SingularBoundedRayJoinEnergy SingularModelGeodesicRays

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M}
  {φ : M → EReal} {hφ : IsModelPotential θ φ} {ℓ ℓ' : ℝ → M → EReal}

omit [ConnectedSpace M] in
private theorem finiteEnergyRayFromModel_of_bounded (omega : KahlerBackground n M)
    {η : ℝ → M → EReal} (hη : IsBoundedRayFromModel θ φ hφ η) :
    IsFiniteEnergyRayFromModel θ φ hφ η :=
  ⟨⟨hη.1.1, fun t ht =>
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      (hη.1.2 t ht.le)⟩, hη.2⟩

private theorem tendsto_max_terminal_distance_div (omega : KahlerBackground n M)
    (hℓ : IsBoundedRayFromModel θ φ hφ ℓ)
    (hℓ' : IsBoundedRayFromModel θ φ hφ ℓ')
    {η : ℝ → M → EReal} (hη : IsFiniteEnergyRayFromModel θ φ hφ η)
    (hle : ∀ T : ℝ, 0 < T → η T ≤ fun x => max (ℓ T x) (ℓ' T x)) :
    Tendsto (fun T : ℝ => relativeD1 θ φ hφ
      (fun x => max (ℓ T x) (ℓ' T x)) (η T) / T) atTop
      (𝓝 ((energy θ φ hφ (joinSlice θ φ ℓ ℓ' 1)).toReal -
        (energy θ φ hφ (η 1)).toReal)) := by
  have hlim := (tendsto_toReal_terminal_max_energy_div omega hℓ hℓ').sub_const
    (energy θ φ hφ (η 1)).toReal
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hlin := congrArg EReal.toReal
    (SingularModelOriginRayEnergy.energy_ray_eq_mul_radialEnergy omega hη hT.le)
  rw [SingularModelOriginRayEnergy.radialEnergy_eq_energy_one omega hη,
    ← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega (hη.1.2 1 zero_lt_one),
    ← EReal.coe_mul, EReal.toReal_coe] at hlin
  rw [relativeD1_comm θ φ hφ _ (η T),
    relativeD1_eq_sub_of_le (hη.1.2 T hT).1.plurisubharmonic (hle T hT), hlin,
    sub_div, mul_div_cancel_left₀ _ hT.ne', div_eq_mul_inv]
  rw [mul_comm]

/-- Genuine source geometry, the actual terminal-maximum energy limit and the actual finite-energy maximum sum estimate internally give Xia's exact two-sided defining ray-distance control. -/
theorem rayD1_join_two_sided (omega : KahlerBackground n M)
    (hℓ : IsBoundedRayFromModel θ φ hφ ℓ)
    (hℓ' : IsBoundedRayFromModel θ φ hφ ℓ') :
    rayD1 θ φ hφ ℓ ℓ' ≤ rayD1 θ φ hφ ℓ (joinSlice θ φ ℓ ℓ') +
      rayD1 θ φ hφ ℓ' (joinSlice θ φ ℓ ℓ') ∧
    rayD1 θ φ hφ ℓ (joinSlice θ φ ℓ ℓ') +
      rayD1 θ φ hφ ℓ' (joinSlice θ φ ℓ ℓ') ≤
        ((3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1) : ℝ) : EReal) *
          rayD1 θ φ hφ ℓ ℓ' := by
  have hf := finiteEnergyRayFromModel_of_bounded omega hℓ
  have hf' := finiteEnergyRayFromModel_of_bounded omega hℓ'
  have hJ := isBoundedRayFromModel_joinSlice omega hℓ hℓ'
  have hfJ := finiteEnergyRayFromModel_of_bounded omega hJ
  have hdom (t : ℝ) (ht : 0 ≤ t) : ℓ t ≤ joinSlice θ φ ℓ ℓ' t :=
    fun x => (le_max_left _ _).trans (max_le_joinSlice hℓ hℓ' ht x)
  have hdom' (t : ℝ) (ht : 0 ≤ t) : ℓ' t ≤ joinSlice θ φ ℓ ℓ' t :=
    fun x => (le_max_right _ _).trans (max_le_joinSlice hℓ hℓ' ht x)
  have hlaws := SingularModelOriginRayDistance.rayD1_isMetric_of_model_origin
    (θ := θ) (φ := φ) (hφ := hφ) omega
  constructor
  · have htri := hlaws.2.2.2.1 ℓ (joinSlice θ φ ℓ ℓ') ℓ' hf hfJ hf'
    rw [hlaws.2.2.1 (joinSlice θ φ ℓ ℓ') ℓ'] at htri
    exact htri
  · let L := ModelFiniteEnergyGeodesicRay.ofFiniteEnergyRayFromModel omega hf
    let K := ModelFiniteEnergyGeodesicRay.ofFiniteEnergyRayFromModel omega hf'
    have hreader (t : ℝ) (ht : 0 ≤ t) : L.rawCurve t = ℓ t := by
      change ℓ (max t 0) = ℓ t
      rw [max_eq_left ht]
    have hreader' (t : ℝ) (ht : 0 ≤ t) : K.rawCurve t = ℓ' t := by
      change ℓ' (max t 0) = ℓ' t
      rw [max_eq_left ht]
    have h0 : L.rawCurve 0 = K.rawCurve 0 :=
      (hreader 0 le_rfl).trans (hf.2.trans (hf'.2.symm.trans (hreader' 0 le_rfl).symm))
    obtain ⟨m, _, hT, _, he⟩ :=
      SingularModelGeodesicRayDistance.exists_tendsto_rayD1 omega L K h0
    have hm : rayD1 θ φ hφ ℓ ℓ' = (m : EReal) :=
      (SingularModelOriginRayDistance.rayD1_eq_native_readers omega hf hf').trans he
    have hsource : Tendsto (fun T : ℝ => relativeD1 θ φ hφ (ℓ T) (ℓ' T) / T)
        atTop (𝓝 m) := by
      refine hT.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hpos
      rw [hreader T hpos.le, hreader' T hpos.le]
    have hleft := tendsto_max_terminal_distance_div omega hℓ hℓ' hf
      (fun _ _ _ => le_max_left _ _)
    have hright := tendsto_max_terminal_distance_div omega hℓ hℓ' hf'
      (fun _ _ _ => le_max_right _ _)
    have hbound :
        ((energy θ φ hφ (joinSlice θ φ ℓ ℓ' 1)).toReal - (energy θ φ hφ (ℓ 1)).toReal) +
          ((energy θ φ hφ (joinSlice θ φ ℓ ℓ' 1)).toReal - (energy θ φ hφ (ℓ' 1)).toReal) ≤
            (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)) * m := by
      refine le_of_tendsto_of_tendsto (hleft.add hright)
        (hsource.const_mul (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1))) ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hpos
      rw [← add_div, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right
        (SingularModelDarvasMaximumSumBound.relativeD1_max_sum_le_mul omega
          (hf.1.2 T hpos) (hf'.1.2 T hpos)) hpos.le
    have hordered := SingularModelGeodesicRayOrderedDistance.rayD1_eq_radialEnergy_sub_of_model_origin
      omega hf hfJ hdom
    have hordered' := SingularModelGeodesicRayOrderedDistance.rayD1_eq_radialEnergy_sub_of_model_origin
      omega hf' hfJ hdom'
    have hfiniteJ := hfJ.1.2 1 zero_lt_one
    rw [SingularModelOriginRayEnergy.radialEnergy_eq_energy_one omega hfJ,
      SingularModelOriginRayEnergy.radialEnergy_eq_energy_one omega hf,
      ← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega hfiniteJ,
      ← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega (hf.1.2 1 zero_lt_one),
      ← EReal.coe_sub] at hordered
    rw [SingularModelOriginRayEnergy.radialEnergy_eq_energy_one omega hfJ,
      SingularModelOriginRayEnergy.radialEnergy_eq_energy_one omega hf',
      ← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega hfiniteJ,
      ← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega (hf'.1.2 1 zero_lt_one),
      ← EReal.coe_sub] at hordered'
    rw [hordered, hordered', hm, ← EReal.coe_add, ← EReal.coe_mul,
      EReal.coe_le_coe_iff]
    exact hbound

/-- The actual least bounded join is the genuine regularized increasing stage supremum and internally has both the original radial-energy limit and the exact original distance control. -/
theorem exists_boundedRayJoin_with_energy_distance (omega : KahlerBackground n M)
    (hℓ : IsBoundedRayFromModel θ φ hφ ℓ)
    (hℓ' : IsBoundedRayFromModel θ φ hφ ℓ') :
    ∃ J : ℝ → M → EReal, J = joinSlice θ φ ℓ ℓ' ∧
      IsBoundedRayFromModel θ φ hφ J ∧
      (∀ t, 0 ≤ t → (fun x => max (ℓ t x) (ℓ' t x)) ≤ J t) ∧
      (∀ L : ℝ → M → EReal, IsBoundedRayFromModel θ φ hφ L →
        (∀ t, 0 ≤ t → ℓ t ≤ L t) → (∀ t, 0 ≤ t → ℓ' t ≤ L t) →
          ∀ t, 0 ≤ t → J t ≤ L t) ∧
      radialEnergy θ φ hφ J = limUnder atTop (fun T : ℝ => ((T⁻¹ : ℝ) : EReal) *
        energy θ φ hφ (fun x => max (ℓ T x) (ℓ' T x))) ∧
      rayD1 θ φ hφ ℓ ℓ' ≤ rayD1 θ φ hφ ℓ J + rayD1 θ φ hφ ℓ' J ∧
      rayD1 θ φ hφ ℓ J + rayD1 θ φ hφ ℓ' J ≤
        ((3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1) : ℝ) : EReal) *
          rayD1 θ φ hφ ℓ ℓ' := by
  refine ⟨joinSlice θ φ ℓ ℓ', rfl, isBoundedRayFromModel_joinSlice omega hℓ hℓ',
    fun _ ht => max_le_joinSlice hℓ hℓ' ht, ?_,
    radialEnergy_joinSlice_eq_limUnder_terminal_max omega hℓ hℓ',
    (rayD1_join_two_sided omega hℓ hℓ').1, (rayD1_join_two_sided omega hℓ hℓ').2⟩
  intro L hL hle hle' t ht
  exact joinSlice_le_upperRay ⟨hL.1.1, hL.2⟩ hle hle' ht

end

end SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinDistance
