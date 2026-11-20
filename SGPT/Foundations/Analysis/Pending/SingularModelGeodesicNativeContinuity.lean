import SGPT.Foundations.Analysis.Pending.SingularGeodesicUniformTimeBounds
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasUniformGap

set_option autoImplicit false

/-!
# Actual native continuity of same-type singular finite-energy geodesics

Xia SGPT PDF0172--0173's finite-gap time argument, followed by the actual
factor-three Darvas relaxation and genuine native energy continuity.
Actual slice membership defines the closed finite-energy segment; actual
time increments produce its native Lipschitz bound. Energy continuity
throughout the closed interval is produced without energy affinity.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelGeodesicNativeContinuity

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelDarvasMetricSpace FiniteGeodesicSingularBarriers

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}

/-- Actual slice membership produces the actual finite-energy endpoint-completed Perron segment. -/
def finiteEnergyGeodesicSegment (omega : KahlerBackground n M)
    (u₀ u₁ : ModelFiniteEnergyPotential θ φ hφ) (t : Icc (0 : ℝ) 1) :
    ModelFiniteEnergyPotential θ φ hφ :=
  ⟨closedSubgeodesicSlice (finiteGeodesic θ.val u₀.val u₁.val) u₀.val u₁.val t.val, by
    by_cases ht0 : t.val = 0
    · simpa only [ht0, closedSubgeodesicSlice_zero] using u₀.property
    by_cases ht1 : t.val = 1
    · simpa only [ht1, closedSubgeodesicSlice_one] using u₁.property
    have ht : t.val ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0), lt_of_le_of_ne t.property.2 ht1⟩
    simpa only [closedSubgeodesicSlice_eq_curve ht] using
      relativeFiniteEnergyPreceq_finiteGeodesic omega u₀.property u₁.property ht⟩

/-- Actual finite obstacle differences give a native Lipschitz bound on the whole closed segment. -/
theorem lipschitzWith_finiteEnergyGeodesicSegment (omega : KahlerBackground n M)
    (u₀ u₁ : ModelFiniteEnergyPotential θ φ hφ) {C : ℝ} (hC : 0 ≤ C)
    (hC₁ : ∀ x, u₁.val x ≤ u₀.val x + (C : EReal))
    (hC₀ : ∀ x, u₀.val x ≤ u₁.val x + (C : EReal)) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    letI : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    LipschitzWith (3 * C * modelVolume θ φ hφ).toNNReal
      (finiteEnergyGeodesicSegment omega u₀ u₁) := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  let : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  apply LipschitzWith.of_dist_le_mul
  intro s t
  let ε : ℝ := C * |s.val - t.val|
  have hε : 0 ≤ ε := mul_nonneg hC (abs_nonneg _)
  have hmutual (x : M) : (finiteEnergyGeodesicSegment omega u₀ u₁ s).val x ≤
      (finiteEnergyGeodesicSegment omega u₀ u₁ t).val x + (ε : EReal) :=
    SingularGeodesicUniformTimeBounds.closedSubgeodesicSlice_le_add_mul_abs
      u₀.property.1.plurisubharmonic u₁.property.1.plurisubharmonic hC hC₁ hC₀
      s.property t.property x
  have hl (x : M) : (finiteEnergyGeodesicSegment omega u₀ u₁ s).val x +
      ((-ε : ℝ) : EReal) ≤ (finiteEnergyGeodesicSegment omega u₀ u₁ t).val x := by
    apply (EReal.addLECancellable_coe ε).add_le_add_iff_right.mp
    have hcancel (a : EReal) : (a + ((-ε : ℝ) : EReal)) + (ε : EReal) = a := by
      cases a with
      | bot => simp
      | top => simp
      | coe a =>
        rw [← EReal.coe_add, ← EReal.coe_add]
        congr 1
        ring
    rw [hcancel]
    exact hmutual x
  have hh (x : M) : (finiteEnergyGeodesicSegment omega u₀ u₁ t).val x ≤
      (finiteEnergyGeodesicSegment omega u₀ u₁ s).val x + (ε : EReal) := by
    change closedSubgeodesicSlice (finiteGeodesic θ.val u₀.val u₁.val) u₀.val u₁.val t.val x ≤
      closedSubgeodesicSlice (finiteGeodesic θ.val u₀.val u₁.val) u₀.val u₁.val s.val x + (ε : EReal)
    simpa only [ε, abs_sub_comm] using
      SingularGeodesicUniformTimeBounds.closedSubgeodesicSlice_le_add_mul_abs
        u₀.property.1.plurisubharmonic u₁.property.1.plurisubharmonic hC hC₁ hC₀
        t.property s.property x
  have hbound := SingularModelDarvasUniformGap.relativeD1_le_of_extended_barriers omega
    (finiteEnergyGeodesicSegment omega u₀ u₁ s).property
    (finiteEnergyGeodesicSegment omega u₀ u₁ t).property hε hl hh
  have hcoef : 0 ≤ 3 * C * modelVolume θ φ hφ :=
    mul_nonneg (mul_nonneg (by norm_num) hC) measureReal_nonneg
  rw [dist_eq_relativeD1 omega, Real.coe_toNNReal _ hcoef, Subtype.dist_eq, Real.dist_eq]
  calc
    _ ≤ 3 * ε * modelVolume θ φ hφ := hbound
    _ = _ := by dsimp [ε]; ring

/-- Actual same singularity type produces genuine native continuity of the whole segment. -/
theorem continuous_finiteEnergyGeodesicSegment (omega : KahlerBackground n M)
    (u₀ u₁ : ModelFiniteEnergyPotential θ φ hφ)
    (htype : SameSingularityTypeOn u₀.val u₁.val univ) :
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
  obtain ⟨C, hC, hC₁, hC₀⟩ := exists_nonneg_le_add_of_sameSingularityType htype
  exact (lipschitzWith_finiteEnergyGeodesicSegment omega u₀ u₁ hC hC₁ hC₀).continuous

/-- Actual finite real geodesic energy is continuous throughout the closed interval without energy affinity. -/
theorem continuousOn_toReal_energy_closedSubgeodesicSlice (omega : KahlerBackground n M)
    (u₀ u₁ : ModelFiniteEnergyPotential θ φ hφ)
    (htype : SameSingularityTypeOn u₀.val u₁.val univ) :
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
    (continuous_finiteEnergyGeodesicSegment omega u₀ u₁ htype)

/-- Actual defining extended geodesic energy is continuous throughout the same closed interval. -/
theorem continuousOn_energy_closedSubgeodesicSlice (omega : KahlerBackground n M)
    (u₀ u₁ : ModelFiniteEnergyPotential θ φ hφ)
    (htype : SameSingularityTypeOn u₀.val u₁.val univ) :
    ContinuousOn (fun t : ℝ => energy θ φ hφ
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀.val u₁.val) u₀.val u₁.val t))
      (Icc (0 : ℝ) 1) := by
  have hreal := continuousOn_toReal_energy_closedSubgeodesicSlice omega u₀ u₁ htype
  have h := continuous_coe_real_ereal.comp_continuousOn hreal
  apply h.congr
  intro t ht
  exact (SingularModelFiniteEnergyPreceq.coe_toReal_energy omega
    (finiteEnergyGeodesicSegment omega u₀ u₁ ⟨t, ht⟩).property).symm

end

end SGPT.Foundations.Analysis.Pending.SingularModelGeodesicNativeContinuity
