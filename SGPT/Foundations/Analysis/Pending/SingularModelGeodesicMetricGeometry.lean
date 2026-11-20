import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicDarvasConvexity

set_option autoImplicit false

/-!
# Actual metric geometry of singular finite-energy Perron segments

Independent metric consequences of Xia SGPT PDF0174 Proposition 4.3.5.
Actual distance convexity, actual Perron restriction and the true Darvas
triangle inequality give constant speed. Actual endpoint interpolation
contracts the maximum product distance; true native closed-segment
continuity then gives joint native continuity. No bounded model,
same-type restriction or target energy or metric identity is assumed.
-/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelGeodesicMetricGeometry

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelGeodesicDarvasConvexity
  SingularModelGeodesicRestriction SingularModelGeodesicNativeContinuity
  SingularModelDarvasMetricSpace

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ u₀ u₁ : M → EReal}
  {hφ : IsModelPotential θ φ}

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem completed_constant {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    closedSubgeodesicSlice (finiteGeodesic θ.val u u) u u t = u := by
  by_cases ht0 : t = 0
  · simp only [ht0, closedSubgeodesicSlice_zero]
  by_cases ht1 : t = 1
  · simp only [ht1, closedSubgeodesicSlice_one]
  have hti : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
  rw [closedSubgeodesicSlice_eq_curve hti]
  funext x
  have h0 : ∀ y, u y ≤ u y + ((0 : ℝ) : EReal) := by simp only [EReal.coe_zero, add_zero, le_refl, implies_true]
  have h := FiniteGeodesicSingularBarriers.finiteGeodesic_extended_barriers hu hu h0 h0 hti x
  simp only [neg_zero, zero_mul, EReal.coe_zero, add_zero] at h
  exact le_antisymm h.1.2 h.1.1

private theorem endpoint_distances (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    relativeD1 θ φ hφ u₀
        (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ t) =
      t * relativeD1 θ φ hφ u₀ u₁ ∧
    relativeD1 θ φ hφ
        (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ t) u₁ =
      (1 - t) * relativeD1 θ φ hφ u₀ u₁ := by
  have h0 := relativeD1_closedGeodesics_le_endpoint_chord omega hu₀ hu₁ hu₀ hu₀ ht
  have h1 := relativeD1_closedGeodesics_le_endpoint_chord omega hu₀ hu₁ hu₁ hu₁ ht
  rw [completed_constant hu₀.1.plurisubharmonic ht,
    relativeD1_self hu₀.1.plurisubharmonic, mul_zero, zero_add,
    relativeD1_comm θ φ hφ u₁ u₀,
    relativeD1_comm θ φ hφ
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ t) u₀] at h0
  rw [completed_constant hu₁.1.plurisubharmonic ht,
    relativeD1_self hu₁.1.plurisubharmonic, mul_zero, add_zero] at h1
  have hU : RelativeFiniteEnergyPreceq θ φ
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ t) hφ :=
    (finiteEnergyGeodesicSegment omega ⟨u₀, hu₀⟩ ⟨u₁, hu₁⟩ ⟨t, ht⟩).property
  have htri := SingularModelDarvasContraction.relativeD1_triangle omega hu₀ hu₁ hU
  constructor <;> nlinarith

private theorem ordered_speed (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s < t) :
    relativeD1 θ φ hφ
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ s)
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ t) =
      (t - s) * relativeD1 θ φ hφ u₀ u₁ := by
  by_cases ht1 : t = 1
  · subst t
    rw [closedSubgeodesicSlice_one, (endpoint_distances omega hu₀ hu₁ hs).2]
  have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
  have hslt : s < 1 := hst.trans htlt
  have hq : (t - s) / (1 - s) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (sub_pos.mpr hst) (sub_pos.mpr hslt),
      (div_lt_one (sub_pos.mpr hslt)).mpr (by linarith)⟩
  have hUs : RelativeFiniteEnergyPreceq θ φ
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ s) hφ :=
    (finiteEnergyGeodesicSegment omega ⟨u₀, hu₀⟩ ⟨u₁, hu₁⟩ ⟨s, hs⟩).property
  have hUt : RelativeFiniteEnergyPreceq θ φ
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ t) hφ :=
    (finiteEnergyGeodesicSegment omega ⟨u₀, hu₀⟩ ⟨u₁, hu₁⟩ ⟨t, ht⟩).property
  have hupper := relativeD1_closedGeodesics_le_endpoint_chord omega hUs hu₁ hUs hUs
    (Ioo_subset_Icc_self hq)
  rw [completed_constant hUs.1.plurisubharmonic (Ioo_subset_Icc_self hq),
    relativeD1_self hUs.1.plurisubharmonic, mul_zero, zero_add,
    relativeD1_comm θ φ hφ u₁
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ s)] at hupper
  have hr := finiteGeodesic_closed_interval_restriction_eq omega hu₀.1 hu₁.1
    hs.1 (le_refl (1 : ℝ)) hslt ⟨hst, htlt⟩
  simp only [closedSubgeodesicSlice_one] at hr
  have htclosed : closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ t =
      finiteGeodesic θ.val u₀ u₁ t := closedSubgeodesicSlice_eq_curve ⟨hs.1.trans_lt hst, htlt⟩
  rw [closedSubgeodesicSlice_eq_curve hq, hr, ← htclosed,
    relativeD1_comm θ φ hφ
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ t)
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ s),
    (endpoint_distances omega hu₀ hu₁ hs).2] at hupper
  have hcoeff : (t - s) / (1 - s) * ((1 - s) * relativeD1 θ φ hφ u₀ u₁) =
      (t - s) * relativeD1 θ φ hφ u₀ u₁ := by
    field_simp [ne_of_gt (sub_pos.mpr hslt)]
  rw [hcoeff] at hupper
  have htri := SingularModelDarvasContraction.relativeD1_triangle omega hu₀ hUt hUs
  rw [(endpoint_distances omega hu₀ hu₁ ht).1,
    (endpoint_distances omega hu₀ hu₁ hs).1] at htri
  linarith

/-- Actual distance convexity, actual restriction, and the actual triangle inequality force exact constant Darvas speed on a general singular finite-energy segment. -/
theorem relativeD1_closedGeodesic_eq_abs_mul (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    relativeD1 θ φ hφ
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ s)
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ t) =
      |s - t| * relativeD1 θ φ hφ u₀ u₁ := by
  rcases lt_trichotomy s t with hst | heq | hts
  · rw [ordered_speed omega hu₀ hu₁ hs ht hst, abs_of_neg (sub_neg.mpr hst)]
    ring
  · subst t
    have hU : RelativeFiniteEnergyPreceq θ φ
        (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ s) hφ :=
      (finiteEnergyGeodesicSegment omega ⟨u₀, hu₀⟩ ⟨u₁, hu₁⟩ ⟨s, hs⟩).property
    simp only [sub_self, abs_zero, zero_mul]
    exact relativeD1_self hU.1.plurisubharmonic
  · rw [relativeD1_comm θ φ hφ
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ s)
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ t),
      ordered_speed omega hu₀ hu₁ ht hs hts, abs_of_pos (sub_pos.mpr hts)]

/-- Actual fixed-time interpolation is one-Lipschitz for the maximum product of native Darvas metrics. -/
theorem lipschitzWith_endpoint_interpolation (omega : KahlerBackground n M)
    (t : Icc (0 : ℝ) 1) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    letI : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    LipschitzWith 1 (fun p : ModelFiniteEnergyPotential θ φ hφ ×
      ModelFiniteEnergyPotential θ φ hφ => finiteEnergyGeodesicSegment omega p.1 p.2 t) := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  let : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simp only [NNReal.coe_one, one_mul, Prod.dist_eq, dist_eq_relativeD1]
  have h := relativeD1_closedGeodesics_le_endpoint_chord omega
    p.1.property p.2.property q.1.property q.2.property t.property
  change relativeD1 θ φ hφ
      (closedSubgeodesicSlice (finiteGeodesic θ.val p.1.val p.2.val) p.1.val p.2.val t.val)
      (closedSubgeodesicSlice (finiteGeodesic θ.val q.1.val q.2.val) q.1.val q.2.val t.val) ≤ _
  have hmax : (1 - t.val) * relativeD1 θ φ hφ p.1.val q.1.val +
      t.val * relativeD1 θ φ hφ p.2.val q.2.val ≤
      max (relativeD1 θ φ hφ p.1.val q.1.val) (relativeD1 θ φ hφ p.2.val q.2.val) := by
    have h0 := mul_le_mul_of_nonneg_left
      (le_max_left (relativeD1 θ φ hφ p.1.val q.1.val) (relativeD1 θ φ hφ p.2.val q.2.val))
      (sub_nonneg.mpr t.property.2)
    have h1 := mul_le_mul_of_nonneg_left
      (le_max_right (relativeD1 θ φ hφ p.1.val q.1.val) (relativeD1 θ φ hφ p.2.val q.2.val))
      t.property.1
    nlinarith
  exact h.trans hmax

/-- True uniform endpoint contraction and true native closed-segment continuity give joint native continuity for general singular finite-energy interpolation. -/
theorem continuous_endpoint_time_interpolation (omega : KahlerBackground n M) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    letI : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    Continuous (fun p : (ModelFiniteEnergyPotential θ φ hφ ×
      ModelFiniteEnergyPotential θ φ hφ) × Icc (0 : ℝ) 1 =>
      finiteEnergyGeodesicSegment omega p.1.1 p.1.2 p.2) := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  let : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hend : Tendsto (fun q : (ModelFiniteEnergyPotential θ φ hφ ×
      ModelFiniteEnergyPotential θ φ hφ) × Icc (0 : ℝ) 1 => dist q.1 p.1)
      (𝓝 p) (𝓝 0) := by
    simpa only [dist_self] using
      (continuous_fst.tendsto p).dist (tendsto_const_nhds (x := p.1))
  have htime : Tendsto (fun q : (ModelFiniteEnergyPotential θ φ hφ ×
      ModelFiniteEnergyPotential θ φ hφ) × Icc (0 : ℝ) 1 =>
      dist (finiteEnergyGeodesicSegment omega p.1.1 p.1.2 q.2)
        (finiteEnergyGeodesicSegment omega p.1.1 p.1.2 p.2)) (𝓝 p) (𝓝 0) := by
    have h : Continuous (fun q : (ModelFiniteEnergyPotential θ φ hφ ×
        ModelFiniteEnergyPotential θ φ hφ) × Icc (0 : ℝ) 1 =>
        finiteEnergyGeodesicSegment omega p.1.1 p.1.2 q.2) :=
      (SingularModelGeodesicGeneralNativeContinuity.continuous_finiteEnergyGeodesicSegment
        omega p.1.1 p.1.2).comp continuous_snd
    simpa only [dist_self] using (h.tendsto p).dist
      (tendsto_const_nhds (x := finiteEnergyGeodesicSegment omega p.1.1 p.1.2 p.2))
  have hupper (q : (ModelFiniteEnergyPotential θ φ hφ ×
      ModelFiniteEnergyPotential θ φ hφ) × Icc (0 : ℝ) 1) :
      dist (finiteEnergyGeodesicSegment omega q.1.1 q.1.2 q.2)
        (finiteEnergyGeodesicSegment omega p.1.1 p.1.2 p.2) ≤
      dist q.1 p.1 + dist (finiteEnergyGeodesicSegment omega p.1.1 p.1.2 q.2)
        (finiteEnergyGeodesicSegment omega p.1.1 p.1.2 p.2) := by
    have h := (lipschitzWith_endpoint_interpolation omega q.2).dist_le_mul q.1 p.1
    simp only [NNReal.coe_one, one_mul] at h
    exact (dist_triangle _ _ _).trans (add_le_add h le_rfl)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using hend.add htime) (fun _ => dist_nonneg) hupper

end

end SGPT.Foundations.Analysis.Pending.SingularModelGeodesicMetricGeometry
