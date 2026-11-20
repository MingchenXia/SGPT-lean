import SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityGentle

set_option autoImplicit false

/-! # Source gentle existence, with a genuinely constructed zero-dimensional branch

The positive-dimensional sequence retains the SAME original squared density.
In dimension zero the source's existence assertion uses the original potential
as a constant sequence, without assuming or constructing a fixed Bergman cover.
The complete blueprint statements and proofs precede this SOURCE.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff ENNReal Classical
universe u
namespace SGPT.Foundations.Analysis.Pending.ActualAllDimensionGentleQea
open FirstPass FirstPass.PositiveClasses FirstPass.HolomorphicMaps
  FirstPass.HolomorphicIdealSheaves FirstPass.GlobalAnalyticSingularities
  FirstPass.QuasiEquisingularApproximation AnalyticModificationLocalDiscrepancy
  ActualOriginalSquaredDensityGentle QuantitativeRegularizationFixedCover

variable {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel 0) X] [IsComplexManifold 0 X]

private theorem finite_of_dim_zero {θ : SmoothRealForm 0 X 2} {u : X → EReal}
    (hu : IsThetaPshPotential θ u) (x : X) : u x = ((u x).toReal : EReal) := by
  have hx := isOpen_singleton_of_dim_zero x
  have hbot : u x ≠ ⊥ := by
    obtain ⟨y, hy, hfin⟩ := hu.2 x {x} hx rfl
    rwa [mem_singleton_iff.mp hy] at hfin
  exact (EReal.coe_toReal (hu.1.quasiPlurisubharmonic.ne_top x) hbot).symm

private theorem smooth_of_dim_zero (h : X → ℝ) : ChartSmooth (n := 0) h := by
  intro e
  have heq : (fun z : ComplexModel 0 => h (e.val.symm z)) =
      fun _ => h (e.val.symm 0) := by
    funext z
    rw [Subsingleton.elim z (0 : ComplexModel 0)]
  rw [heq]
  exact contDiffOn_const

private theorem multiplier_integrable_zero
    [MeasurableSpace (ComplexModel 0)] [BorelSpace (ComplexModel 0)] {θ : SmoothRealForm 0 X 2}
    {u : X → EReal} (hu : IsThetaPshPotential θ u) (e : ComplexChart 0 X)
    {c : ℝ} (hc : 0 < c) (f : ComplexModel 0 → ℂ) (z : ComplexModel 0) :
    MultiplierIntegrableAt (chartFunction u e) c f z volume := by
  have huval : ∀ t : ComplexModel 0,
      chartFunction u e t = ((u (e.val.symm z)).toReal : EReal) := by
    intro t
    rw [chartFunction, Subsingleton.elim t z]
    exact finite_of_dim_zero hu _
  have hfval : f = fun _ => f z := by
    funext t
    rw [Subsingleton.elim t z]
  have hdens : multiplierDensity (chartFunction u e) c (fun _ => f z) =
      fun _ => ENNReal.ofReal (‖f z‖ ^ 2 * Real.exp (-(c * (u (e.val.symm z)).toReal))) := by
    funext t
    simp only [multiplierDensity, huval t, multiplierWeight_coe]
    rw [ENNReal.ofReal_mul (sq_nonneg _)]
  rw [hfval]
  refine ⟨hc, ball z 1, isOpen_ball, mem_ball_self one_pos, differentiableOn_const _, ?_, ?_⟩
  · rw [hdens]
    exact aemeasurable_const
  · rw [hdens, lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

private theorem multiplier_mem_zero {θ : SmoothRealForm 0 X 2} {u : X → EReal}
    (hu : IsThetaPshPotential θ u) {d : ℝ} (hd : 0 < d) (x : X) (h : X → ℂ) :
    (multiplierIdeal (n := 0) d u).mem x h ↔ HolomorphicAt 0 h x := by
  refine ⟨fun hh => hh.1, fun hh => ?_⟩
  exact ⟨hh, multiplier_integrable_zero hu (complexChartAt (n := 0) x) hd _ _⟩

omit [IsComplexManifold 0 X] in
private theorem unit_span (x : X) (h : X → ℂ) :
    HolomorphicAt 0 h x ↔ IsInSpanAt (n := 0) (· = (fun _ : X => (1 : ℂ))) x h := by
  refine ⟨fun hh => ?_, fun hh => hh.1⟩
  exact isInSpanAt_eq_iff.mpr ⟨hh, h, hh, Eventually.of_forall (fun z => by simp)⟩

private def zeroDivisor : EffectiveDivisor 0 X where
  ideal := ⟨fun x h => HolomorphicAt 0 h x⟩
  isInvertible x := by
    refine ⟨univ, isOpen_univ, mem_univ x, fun _ => 1, mdifferentiableOn_const, ?_, ?_⟩
    · intro W _ _ hW
      obtain ⟨y, hy⟩ := hW
      exact ⟨y, hy, one_ne_zero⟩
    · intro y _ h
      exact unit_span y h

private theorem identity_modification : IsAnalyticModification (n := 0) (id : X → X) := by
  refine ⟨contMDiff_id, isProperMap_id, ∅, ∅, id,
    isClosed_empty, isComplexAnalyticSubset_empty, ?_,
    isClosed_empty, isComplexAnalyticSubset_empty, ?_, ?_,
    contMDiff_id.contMDiffOn, fun _ _ => rfl, fun _ _ => rfl⟩ <;> simp

private def zeroCoordinates (p : ComplexModel 0) : LocalHolomorphicEquivAt (n := 0) p where
  source := univ
  target := univ
  isOpen_source := isOpen_univ
  isOpen_target := isOpen_univ
  center_mem_source := mem_univ p
  toFun := id
  invFun := id
  toFun_holomorphic := differentiableOn_id
  invFun_holomorphic := differentiableOn_id
  mapsTo_toFun := mapsTo_id _
  mapsTo_invFun := mapsTo_id _
  left_inv _ _ := rfl
  right_inv _ _ := rfl

private theorem analytic_type_zero {θ : SmoothRealForm 0 X 2} {u : X → EReal}
    (hu : IsThetaPshPotential θ u) {c : ℚ} (hc : 0 < c) {d : ℝ} (hd : 0 < d) :
    HasAnalyticSingularitiesOfType (n := 0) u c (multiplierIdeal (n := 0) d u) := by
  let one : Fin 1 → X → ℂ := fun _ _ => 1
  have hspan : ∀ y h, (multiplierIdeal (n := 0) d u).mem y h ↔
      IsInSpanAt (n := 0) (· ∈ range one) y h := by
    intro y h
    rw [multiplier_mem_zero hu hd]
    constructor
    · intro hh
      exact ⟨hh, 1, one, fun _ => h, fun _ => ⟨0, rfl⟩, fun _ => hh,
        Eventually.of_forall fun z => by simp [one]⟩
    · exact fun hh => hh.1
  have hone : ∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel 0) 𝓘(ℂ, ℂ) (one i) univ :=
    fun _ => mdifferentiableOn_const
  refine ⟨hc, fun x => ⟨univ, isOpen_univ, mem_univ x, 1, one, hone,
    fun y _ h => hspan y h⟩, fun x => ?_⟩
  refine ⟨{x}, isOpen_singleton_of_dim_zero x, rfl, 1, one,
    fun i => (hone i).mono (subset_univ _), fun y _ h => hspan y h,
    fun _ => (u x).toReal, |(u x).toReal|, fun _ _ => le_rfl, fun y hy => ?_⟩
  rw [mem_singleton_iff.mp hy]
  have hlog : generatorLog one x = 0 := by
    rw [generatorLog_eq_log_sum]
    simp [one]
  rw [hlog, mul_zero, zero_add]
  exact finite_of_dim_zero hu x

private theorem gentle_zero (omega : KahlerBackground 0 X)
    {θ : SmoothRealForm 0 X 2} {u : X → EReal} (hu : IsThetaPshPotential θ u)
    {c : ℚ} (hc : 0 < c) {d : ℝ} (hd : 0 < d) :
    HasGentleAnalyticSingularitiesOfType (n := 0) u c (multiplierIdeal (n := 0) d u) := by
  refine ⟨⟨hu.1.quasiPlurisubharmonic, hu.2⟩, analytic_type_zero hu hc hd, ?_,
    smooth_of_dim_zero _, X, inferInstance, inferInstance, inferInstance,
    id, zeroDivisor, identity_modification, ⟨omega⟩, ?_⟩
  · intro x
    rw [finite_of_dim_zero hu x, ← EReal.coe_mul, EReal.exp_coe]
    exact ENNReal.ofReal_ne_top
  · intro y
    let e := complexChartAt (n := 0) y
    let Φ := zeroCoordinates (e.val y)
    have he : y ∈ e.val.source := mem_complexChartAt_source y
    have hsrc : Φ.source ⊆ e.val.target := by
      intro z _
      rw [Subsingleton.elim z (e.val y)]
      exact e.val.map_source he
    have hT : ∀ z : ComplexModel 0, e.val.symm (Φ.invFun z) = y := by
      intro z
      rw [Subsingleton.elim (Φ.invFun z) (e.val y), e.val.left_inv he]
    refine ⟨{y}, isOpen_singleton_of_dim_zero y, rfl, fun _ => 1,
      mdifferentiableOn_const, ?_, fun t _ a => unit_span t a, Φ, hsrc,
      Subsingleton.elim _ _, fun _ => (u y).toReal, 1, one_pos,
      fun _ _ => mem_univ _, contDiffOn_const, ?_⟩
    · intro W _ _ hW
      obtain ⟨t, ht⟩ := hW
      exact ⟨t, ht, one_ne_zero⟩
    · intro z _
      change e.val.symm (Φ.invFun z) ∈ {y} ∧
        u (e.val.symm (Φ.invFun z)) =
          ((c : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (‖(1 : ℂ)‖ ^ 2)) + _
      rw [hT z]
      constructor
      · rfl
      · simpa using finite_of_dim_zero hu y

/-- The zero-dimensional sequence is the SAME original potential itself;
finite values and actual multiplier integrals are internally established. -/
theorem constant_gentle_qea_zero (omega : KahlerBackground 0 X)
    (θ : ClosedRealOneOneForm 0 X) {u : X → EReal} (hu : IsThetaPshPotential θ.val u) :
    IsQuasiEquisingularApproximation omega θ u (fun _ => 0) (fun _ => u) ∧
      ∀ ℓ : ℕ, HasGentleAnalyticSingularitiesOfType (n := 0) u
        (((2 ^ ℓ : ℕ) : ℚ)⁻¹) (multiplierIdeal (n := 0) ((2 ^ ℓ : ℕ) : ℝ) u) := by
  have htype : ∀ ℓ : ℕ, HasAnalyticSingularitiesOfType (n := 0) u
      (((2 ^ ℓ : ℕ) : ℚ)⁻¹) (multiplierIdeal (n := 0) ((2 ^ ℓ : ℕ) : ℝ) u) :=
    fun ℓ => analytic_type_zero hu (by positivity) (by positivity)
  refine ⟨⟨hu, ⟨fun _ => le_rfl, fun _ _ _ => le_rfl, tendsto_const_nhds⟩,
    fun _ => ?_, fun ℓ => (htype ℓ).hasManifoldAnalyticSingularityType,
    ⟨fun _ _ _ _ => le_rfl, fun _ => tendsto_const_nhds⟩, ?_⟩,
    fun ℓ => gentle_zero omega hu (by positivity) (by positivity)⟩
  · simpa using hu
  · intro c d hc _
    let : MeasurableSpace (ComplexModel 0) := borel _
    let : BorelSpace (ComplexModel 0) := ⟨rfl⟩
    exact Eventually.of_forall fun _ e z _ f _ _ => multiplier_integrable_zero hu e hc f z

/-- Source existence in ALL ambient dimensions: positive dimension keeps the
literal original squared density; dimension zero uses its actual constant branch. -/
theorem exists_all_dimension_gentle_qea {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [CompactSpace X] (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    {u : X → EReal} (hu : IsThetaPshPotential θ.val u) :
    ∃ (ε : ℕ → ℝ) (v : ℕ → X → EReal),
      IsQuasiEquisingularApproximation omega θ u ε v ∧
      ∀ ℓ : ℕ, HasGentleAnalyticSingularitiesOfType (n := n) (v ℓ)
        (((2 ^ ℓ : ℕ) : ℚ)⁻¹) (multiplierIdeal (n := n) ((2 ^ ℓ : ℕ) : ℝ) u) := by
  cases n with
  | zero => exact ⟨fun _ => 0, fun _ => u, constant_gentle_qea_zero omega θ hu⟩
  | succ m =>
    obtain ⟨F, C, E, _, _, hF⟩ := exists_fixed_cover_full_gentle_qea omega
    obtain ⟨ρ, _, hqea, hgentle⟩ := hF θ u hu
    exact ⟨fun ℓ => C * ((2 : ℝ) ^ ℓ)⁻¹,
      fun ℓ x => ActualOriginalSquaredDensityThetaPsh.originalWeight F ρ u (2 ^ ℓ) x +
        ((E * ((2 : ℝ) ^ ℓ)⁻¹ : ℝ) : EReal), hqea, hgentle⟩

end SGPT.Foundations.Analysis.Pending.ActualAllDimensionGentleQea
