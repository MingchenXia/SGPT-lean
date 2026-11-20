import SGPT.Foundations.Analysis.Pending.SingularPerronGeneralEndpointEnergyContinuity
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasBasic
import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicNativeContinuity

set_option autoImplicit false

/-!
# Actual general finite-energy Perron curves recover their endpoints in Darvas distance

An independent metric consequence of Xia SGPT PDF0134--0135's actual
shifted rooftop exhaustion and PDF0172--0173's genuine endpoint energy
producers. Actual affine competitors and actual finite-energy rooftop
closure give a quantitative endpoint distance bound. Actual rooftop
energy exhaustion and actual general endpoint energy limits then give
both defining Darvas distance limits without energy affinity or equal
singularity types of the endpoints. The actual endpoint-completed segment
is consequently continuous at both endpoints in the explicit native topology.
-/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelGeodesicEndpointDistance

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularPerronShiftedRooftopBarriers
  SingularModelEnergyShiftedRooftopContinuity SingularModelDarvasMetricSpace
  SingularModelGeodesicNativeContinuity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ u₀ u₁ : M → EReal} {hφ : IsModelPotential θ φ}

/-- Genuine shifted rooftop competitors bound the actual defining initial Darvas distance. -/
theorem relativeD1_finiteGeodesic_left_le_shifted_rooftop (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ) {C : ℝ} (hC : 0 ≤ C)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    relativeD1 θ φ hφ u₀ (finiteGeodesic θ.val u₀ u₁ t) ≤
      (energy θ φ hφ u₀).toReal + (energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t)).toReal -
        2 * (energy θ φ hφ (rooftop θ u₀ (fun x => u₁ x + (C : EReal)))).toReal +
          2 * C * t * modelVolume θ φ hφ := by
  have hU := relativeFiniteEnergyPreceq_finiteGeodesic omega hu₀ hu₁ ht
  have hW := relativeFiniteEnergyPreceq_rooftop omega hu₀ (hu₁.add_const omega C)
  have hshift := hW.add_const omega ((-C) * t)
  have hleft : (fun x => rooftop θ u₀ (fun y => u₁ y + (C : EReal)) x +
      (((-C) * t : ℝ) : EReal)) ≤ u₀ := fun x =>
    (add_le_of_nonpos_right (EReal.coe_nonpos.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hC) ht.1.le))).trans
      (rooftop_le_left hu₀.1.plurisubharmonic (hu₁.add_const omega C).1.plurisubharmonic x)
  have hright := shifted_rooftop_affine_lower_left omega hu₀ hu₁ C t
  have hroof := relativeFiniteEnergyPreceq_rooftop omega hu₀ hU
  have hle : (fun x => rooftop θ u₀ (fun y => u₁ y + (C : EReal)) x +
      (((-C) * t : ℝ) : EReal)) ≤ rooftop θ u₀ (finiteGeodesic θ.val u₀ u₁ t) :=
    (le_rooftop_iff hu₀.1.plurisubharmonic hU.1.plurisubharmonic
      hshift.1.plurisubharmonic).2 ⟨hleft, hright⟩
  have he := SingularModelFiniteRealEnergy.toReal_energy_mono omega hshift hroof hle
  rw [SingularModelFiniteRealEnergy.toReal_energy_add_const omega hW] at he
  rw [relativeD1]
  linarith

/-- True shifted rooftop energy exhaustion and true general endpoint energy give the actual initial distance limit. -/
theorem relativeD1_finiteGeodesic_left_tendsto_zero (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ) :
    Tendsto (fun t : ℝ => relativeD1 θ φ hφ (finiteGeodesic θ.val u₀ u₁ t) u₀)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have htime : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hE := SingularPerronGeneralEndpointEnergyContinuity.tendsto_toReal_energy_finiteGeodesic_left
    omega hu₀ hu₁
  have htimes : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1))] with t ht0 ht1
    exact ⟨ht0, ht1⟩
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [htimes] with t ht
    exact ha.trans_le (SingularModelDarvasBasic.relativeD1_nonneg omega
      (relativeFiniteEnergyPreceq_finiteGeodesic omega hu₀ hu₁ ht) hu₀)
  · intro a ha
    have hlevel : (energy θ φ hφ u₀).toReal - a / 2 < (energy θ φ hφ u₀).toReal := by linarith
    obtain ⟨C, hC, hCW⟩ := ((eventually_ge_atTop (0 : ℝ)).and
      ((toReal_energy_rooftop_add_const_tendsto omega hu₀ hu₁).eventually_const_lt hlevel)).exists
    have hlim : Tendsto (fun t : ℝ =>
        (energy θ φ hφ u₀).toReal + (energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t)).toReal -
          2 * (energy θ φ hφ (rooftop θ u₀ (fun x => u₁ x + (C : EReal)))).toReal +
            2 * C * t * modelVolume θ φ hφ) (𝓝[>] (0 : ℝ))
        (𝓝 (2 * ((energy θ φ hφ u₀).toReal -
          (energy θ φ hφ (rooftop θ u₀ (fun x => u₁ x + (C : EReal)))).toReal))) := by
      have h := (((tendsto_const_nhds (x := (energy θ φ hφ u₀).toReal)).add hE).sub_const
        (2 * (energy θ φ hφ (rooftop θ u₀ (fun x => u₁ x + (C : EReal)))).toReal)).add
          ((htime.const_mul (2 * C)).mul_const (modelVolume θ φ hφ))
      have hid : (energy θ φ hφ u₀).toReal + (energy θ φ hφ u₀).toReal -
          2 * (energy θ φ hφ (rooftop θ u₀ (fun x => u₁ x + (C : EReal)))).toReal +
            2 * C * 0 * modelVolume θ φ hφ =
          2 * ((energy θ φ hφ u₀).toReal -
            (energy θ φ hφ (rooftop θ u₀ (fun x => u₁ x + (C : EReal)))).toReal) := by ring
      rwa [hid] at h
    have hsmall : 2 * ((energy θ φ hφ u₀).toReal -
        (energy θ φ hφ (rooftop θ u₀ (fun x => u₁ x + (C : EReal)))).toReal) < a := by linarith
    filter_upwards [htimes, hlim.eventually_lt_const hsmall] with t ht hta
    rw [relativeD1_comm θ φ hφ]
    exact lt_of_le_of_lt (relativeD1_finiteGeodesic_left_le_shifted_rooftop omega hu₀ hu₁ hC ht) hta

/-- Genuine Perron time reversal transfers the actual initial limit to the actual terminal distance. -/
theorem relativeD1_finiteGeodesic_right_tendsto_zero (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ) :
    Tendsto (fun t : ℝ => relativeD1 θ φ hφ (finiteGeodesic θ.val u₀ u₁ t) u₁)
      (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have hrev : Tendsto (fun t : ℝ => 1 - t) (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · simpa using (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun t : ℝ => 1 - t) (𝓝[<] (1 : ℝ)) (𝓝 (1 - 1)))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change t < 1 at ht
      change 0 < 1 - t
      linarith
  have h := (relativeD1_finiteGeodesic_left_tendsto_zero omega hu₁ hu₀).comp hrev
  have hid : (fun t : ℝ => relativeD1 θ φ hφ (finiteGeodesic θ.val u₁ u₀ (1 - t)) u₁) =
      fun t : ℝ => relativeD1 θ φ hφ (finiteGeodesic θ.val u₀ u₁ t) u₁ := by
    funext t
    rw [finiteGeodesic_timeReversal θ.val u₀ u₁ (1 - t), sub_sub_cancel]
  change Tendsto (fun t : ℝ => relativeD1 θ φ hφ (finiteGeodesic θ.val u₁ u₀ (1 - t)) u₁)
    (𝓝[<] (1 : ℝ)) (𝓝 0) at h
  rwa [hid] at h

/-- The actual endpoint-completed E1 segment is genuinely continuous at its initial endpoint in the native topology. -/
theorem continuousAt_finiteEnergyGeodesicSegment_zero (omega : KahlerBackground n M)
    (u₀ u₁ : ModelFiniteEnergyPotential θ φ hφ) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    letI : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    ContinuousAt (finiteEnergyGeodesicSegment omega u₀ u₁)
      (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  let : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp
    ((relativeD1_finiteGeodesic_left_tendsto_zero omega u₀.property u₁.property).eventually_lt_const hε)
  refine ⟨min δ 1, lt_min hδ zero_lt_one, ?_⟩
  intro t ht
  by_cases ht0 : t.val = 0
  · have heq : t = (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) := Subtype.ext ht0
    simpa only [heq, dist_self] using hε
  have htdist : dist t.val (0 : ℝ) < min δ 1 := ht
  have htδ : dist t.val (0 : ℝ) < δ := htdist.trans_le (min_le_left _ _)
  have ht1 : t.val < 1 := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg t.property.1] using
      htdist.trans_le (min_le_right δ 1)
  have htpos : 0 < t.val := lt_of_le_of_ne t.property.1 (Ne.symm ht0)
  have h := hball ⟨htδ, htpos⟩
  change relativeD1 θ φ hφ
    (closedSubgeodesicSlice (finiteGeodesic θ.val u₀.val u₁.val) u₀.val u₁.val t.val)
    (closedSubgeodesicSlice (finiteGeodesic θ.val u₀.val u₁.val) u₀.val u₁.val 0) < ε
  rw [closedSubgeodesicSlice_zero, closedSubgeodesicSlice_eq_curve ⟨htpos, ht1⟩]
  exact h

/-- The same actual one-sided distance producer gives native continuity at the terminal endpoint of the completed segment. -/
theorem continuousAt_finiteEnergyGeodesicSegment_one (omega : KahlerBackground n M)
    (u₀ u₁ : ModelFiniteEnergyPotential θ φ hφ) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    letI : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    ContinuousAt (finiteEnergyGeodesicSegment omega u₀ u₁)
      (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  let : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp
    ((relativeD1_finiteGeodesic_right_tendsto_zero omega u₀.property u₁.property).eventually_lt_const hε)
  refine ⟨min δ 1, lt_min hδ zero_lt_one, ?_⟩
  intro t ht
  by_cases ht1 : t.val = 1
  · have heq : t = (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) := Subtype.ext ht1
    simpa only [heq, dist_self] using hε
  have htdist : dist t.val (1 : ℝ) < min δ 1 := ht
  have htδ : dist t.val (1 : ℝ) < δ := htdist.trans_le (min_le_left _ _)
  have ht0 : 0 < t.val := by
    have habs : |t.val - 1| < 1 := by
      simpa only [Real.dist_eq] using htdist.trans_le (min_le_right δ 1)
    have h := (abs_lt.mp habs).1
    linarith
  have htlt : t.val < 1 := lt_of_le_of_ne t.property.2 ht1
  have h := hball ⟨htδ, htlt⟩
  change relativeD1 θ φ hφ
    (closedSubgeodesicSlice (finiteGeodesic θ.val u₀.val u₁.val) u₀.val u₁.val t.val)
    (closedSubgeodesicSlice (finiteGeodesic θ.val u₀.val u₁.val) u₀.val u₁.val 1) < ε
  rw [closedSubgeodesicSlice_one, closedSubgeodesicSlice_eq_curve ⟨ht0, htlt⟩]
  exact h

end

end SGPT.Foundations.Analysis.Pending.SingularModelGeodesicEndpointDistance
