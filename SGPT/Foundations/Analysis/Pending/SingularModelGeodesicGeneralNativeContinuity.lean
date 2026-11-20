import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRestriction
import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicEndpointDistance

set_option autoImplicit false

/-!
# Actual general finite-energy geodesics are natively continuous

Xia SGPT PDF0155--0156's actual restriction and PDF0172--0173's actual
endpoint energy producers, followed by independent genuine metric
consequences. True closed-subinterval restriction and true endpoint
Darvas limits produce two-sided interior distance continuity. Actual
native endpoint continuity then gives native continuity of the whole
closed segment and actual real/extended energy continuity, without
same-type endpoints or an energy-affinity premise.
-/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelGeodesicGeneralNativeContinuity

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelGeodesicRestriction SingularModelGeodesicEndpointDistance
  SingularModelDarvasMetricSpace SingularModelGeodesicNativeContinuity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ u₀ u₁ : M → EReal} {hφ : IsModelPotential θ φ}

/-- True Perron restriction and true endpoint Darvas limits produce genuine two-sided interior distance continuity. -/
theorem relativeD1_finiteGeodesic_tendsto_zero_of_interior (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ) {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun t : ℝ => relativeD1 θ φ hφ
      (finiteGeodesic θ.val u₀ u₁ t) (finiteGeodesic θ.val u₀ u₁ c)) (𝓝 c) (𝓝 0) := by
  have hC := relativeFiniteEnergyPreceq_finiteGeodesic omega hu₀ hu₁ hc
  have hleft : Tendsto (fun t : ℝ => relativeD1 θ φ hφ
      (finiteGeodesic θ.val u₀ u₁ t) (finiteGeodesic θ.val u₀ u₁ c)) (𝓝[<] c) (𝓝 0) := by
    have htime : Tendsto (fun t : ℝ => t / c) (𝓝[<] c) (𝓝[<] (1 : ℝ)) := by
      apply tendsto_nhdsWithin_iff.2
      constructor
      · have hid : Tendsto (fun t : ℝ => t) (𝓝[<] c) (𝓝 c) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        simpa only [div_self (ne_of_gt hc.1)] using hid.div_const c
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact (div_lt_one hc.1).mpr ht
    have h := (relativeD1_finiteGeodesic_right_tendsto_zero omega hu₀ hC).comp htime
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hc.1)] with t ht hpos
    have hr := finiteGeodesic_closed_interval_restriction_eq omega hu₀.1 hu₁.1
      (a := 0) (b := c) (by norm_num) hc.2.le hc.1 ⟨hpos, ht⟩
    have hid : finiteGeodesic θ.val u₀ (finiteGeodesic θ.val u₀ u₁ c) (t / c) =
        finiteGeodesic θ.val u₀ u₁ t := by
      simpa only [closedSubgeodesicSlice_zero, closedSubgeodesicSlice_eq_curve hc, sub_zero] using hr
    change relativeD1 θ φ hφ (finiteGeodesic θ.val u₀ (finiteGeodesic θ.val u₀ u₁ c) (t / c))
      (finiteGeodesic θ.val u₀ u₁ c) = _
    rw [hid]
  have hright : Tendsto (fun t : ℝ => relativeD1 θ φ hφ
      (finiteGeodesic θ.val u₀ u₁ t) (finiteGeodesic θ.val u₀ u₁ c)) (𝓝[>] c) (𝓝 0) := by
    have htime : Tendsto (fun t : ℝ => (t - c) / (1 - c)) (𝓝[>] c) (𝓝[>] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_iff.2
      constructor
      · have hid : Tendsto (fun t : ℝ => t) (𝓝[>] c) (𝓝 c) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        simpa only [sub_self, zero_div] using (hid.sub_const c).div_const (1 - c)
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact div_pos (sub_pos.mpr ht) (sub_pos.mpr hc.2)
    have h := (relativeD1_finiteGeodesic_left_tendsto_zero omega hC hu₁).comp htime
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hc.2)] with t ht hlt
    have hr := finiteGeodesic_closed_interval_restriction_eq omega hu₀.1 hu₁.1
      (a := c) (b := 1) hc.1.le (by norm_num) hc.2 ⟨ht, hlt⟩
    have hid : finiteGeodesic θ.val (finiteGeodesic θ.val u₀ u₁ c) u₁ ((t - c) / (1 - c)) =
        finiteGeodesic θ.val u₀ u₁ t := by
      simpa only [closedSubgeodesicSlice_eq_curve hc, closedSubgeodesicSlice_one] using hr
    change relativeD1 θ φ hφ
      (finiteGeodesic θ.val (finiteGeodesic θ.val u₀ u₁ c) u₁ ((t - c) / (1 - c)))
      (finiteGeodesic θ.val u₀ u₁ c) = _
    rw [hid]
  have hself : relativeD1 θ φ hφ (finiteGeodesic θ.val u₀ u₁ c)
      (finiteGeodesic θ.val u₀ u₁ c) = 0 := relativeD1_self hC.1.plurisubharmonic
  have hcont : ContinuousAt (fun t : ℝ => relativeD1 θ φ hφ
      (finiteGeodesic θ.val u₀ u₁ t) (finiteGeodesic θ.val u₀ u₁ c)) c := by
    apply continuousAt_iff_continuous_left'_right'.2
    constructor
    · simpa only [ContinuousWithinAt, hself] using hleft
    · simpa only [ContinuousWithinAt, hself] using hright
  simpa only [hself] using hcont.tendsto

/-- The actual endpoint-completed general E1 segment is continuous throughout the closed interval in its native topology. -/
theorem continuous_finiteEnergyGeodesicSegment (omega : KahlerBackground n M)
    (u₀ u₁ : ModelFiniteEnergyPotential θ φ hφ) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    letI : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    Continuous (finiteEnergyGeodesicSegment omega u₀ u₁) := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  let : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  apply continuous_iff_continuousAt.mpr
  intro c
  by_cases hc0 : c.val = 0
  · have heq : c = (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) := Subtype.ext hc0
    rw [heq]
    exact continuousAt_finiteEnergyGeodesicSegment_zero omega u₀ u₁
  by_cases hc1 : c.val = 1
  · have heq : c = (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) := Subtype.ext hc1
    rw [heq]
    exact continuousAt_finiteEnergyGeodesicSegment_one omega u₀ u₁
  have hc : c.val ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne c.property.1 (Ne.symm hc0), lt_of_le_of_ne c.property.2 hc1⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hval : Tendsto (fun t : Icc (0 : ℝ) 1 => t.val) (𝓝 c) (𝓝 c.val) :=
    continuous_subtype_val.continuousAt.tendsto
  have h := (relativeD1_finiteGeodesic_tendsto_zero_of_interior omega u₀.property u₁.property hc).comp hval
  apply h.congr'
  filter_upwards [hval.eventually (isOpen_Ioo.mem_nhds hc)] with t ht
  change relativeD1 θ φ hφ (finiteGeodesic θ.val u₀.val u₁.val t.val)
    (finiteGeodesic θ.val u₀.val u₁.val c.val) =
      relativeD1 θ φ hφ
        (closedSubgeodesicSlice (finiteGeodesic θ.val u₀.val u₁.val) u₀.val u₁.val t.val)
        (closedSubgeodesicSlice (finiteGeodesic θ.val u₀.val u₁.val) u₀.val u₁.val c.val)
  rw [closedSubgeodesicSlice_eq_curve ht, closedSubgeodesicSlice_eq_curve hc]

/-- Genuine native segment continuity gives actual real model-energy continuity for arbitrary E1 endpoints. -/
theorem continuousOn_toReal_energy_closedSubgeodesicSlice (omega : KahlerBackground n M)
    (u₀ u₁ : ModelFiniteEnergyPotential θ φ hφ) :
    ContinuousOn (fun t : ℝ => (energy θ φ hφ
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀.val u₁.val) u₀.val u₁.val t)).toReal)
      (Icc (0 : ℝ) 1) := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  let : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact (energy_continuous (θ := θ) (φ := φ) (hφ := hφ) omega).comp
    (continuous_finiteEnergyGeodesicSegment omega u₀ u₁)

/-- Actual E1 realification gives defining extended-energy continuity on the whole general closed segment. -/
theorem continuousOn_energy_closedSubgeodesicSlice (omega : KahlerBackground n M)
    (u₀ u₁ : ModelFiniteEnergyPotential θ φ hφ) :
    ContinuousOn (fun t : ℝ => energy θ φ hφ
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀.val u₁.val) u₀.val u₁.val t))
      (Icc (0 : ℝ) 1) := by
  have hreal := continuousOn_toReal_energy_closedSubgeodesicSlice omega u₀ u₁
  have h := continuous_coe_real_ereal.comp_continuousOn hreal
  apply h.congr
  intro t ht
  exact (SingularModelFiniteEnergyPreceq.coe_toReal_energy omega
    (finiteEnergyGeodesicSegment omega u₀ u₁ ⟨t, ht⟩).property).symm

end

end SGPT.Foundations.Analysis.Pending.SingularModelGeodesicGeneralNativeContinuity
