import SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityAnalyticType
import SGPT.Foundations.Analysis.FirstPass.FiniteTranslation

set_option autoImplicit false

/-! # The SAME original squared density is a full QEA, with a true zero branch

Zero-dimensional original multiplier germs are integrated directly in their
actual coordinate model. The uniform original enlarged-background and dyadic
producers then give every QEA field for the SAME prescribed density.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff ENNReal Classical
namespace SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityFullQea
open FirstPass FirstPass.PositiveClasses FirstPass.HolomorphicMaps
  FirstPass.HolomorphicIdealSheaves FirstPass.GlobalAnalyticSingularities
  FirstPass.QuasiEquisingularApproximation
  QuantitativeRegularizationFixedCover QuantitativeRegularizationChartBranch
  ActualOriginalSquaredDensityThetaPsh ActualOriginalSquaredDensityDyadicConvergence
  ActualOriginalSquaredDensityAnalyticType

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

private theorem finite_of_dim_zero {Z : Type*} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel 0) Z] [IsComplexManifold 0 Z]
    {θ : SmoothRealForm 0 Z 2} {u : Z → EReal} (hu : IsThetaPshPotential θ u) (x : Z) :
    u x = ((u x).toReal : EReal) := by
  have hx := isOpen_singleton_of_dim_zero x
  have hbot : u x ≠ ⊥ := by
    obtain ⟨y, hy, hfin⟩ := hu.2 x {x} hx rfl
    rwa [mem_singleton_iff.mp hy] at hfin
  exact (EReal.coe_toReal (hu.1.quasiPlurisubharmonic.ne_top x) hbot).symm

private theorem multiplierIdeal_mem_iff_holomorphic_zero {Z : Type*}
    [TopologicalSpace Z] [ChartedSpace (ComplexModel 0) Z] [IsComplexManifold 0 Z]
    {θ : SmoothRealForm 0 Z 2} {u : Z → EReal} (hu : IsThetaPshPotential θ u)
    {c : ℝ} (hc : 0 < c) (x : Z) (h : Z → ℂ) :
    (multiplierIdeal (n := 0) c u).mem x h ↔ HolomorphicAt 0 h x := by
  refine ⟨fun hh => hh.1, fun hh => ?_⟩
  let e : ComplexChart 0 Z := complexChartAt (n := 0) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have huval : ∀ z : ComplexModel 0, chartFunction u e z = ((u x).toReal : EReal) := by
    intro z
    have hz : z = e.val x := Subsingleton.elim _ _
    change u (e.val.symm z) = _
    rw [hz, e.val.left_inv hx]
    exact finite_of_dim_zero hu x
  have hhval : (fun z : ComplexModel 0 => h (e.val.symm z)) = fun _ => h x := by
    funext z
    rw [Subsingleton.elim z (e.val x), e.val.left_inv hx]
  have hdens : multiplierDensity (chartFunction u e) c (fun _ => h x) =
      fun _ => ENNReal.ofReal (‖h x‖ ^ 2 * Real.exp (-(c * (u x).toReal))) := by
    funext z
    simp only [multiplierDensity, huval z, multiplierWeight_coe]
    rw [ENNReal.ofReal_mul (sq_nonneg _)]
  refine ⟨hh, hc, ball (e.val x) 1, isOpen_ball, mem_ball_self one_pos, ?_, ?_, ?_⟩
  · change DifferentiableOn ℂ (fun z : ComplexModel 0 => h (e.val.symm z)) _
    rw [hhval]
    exact differentiableOn_const _
  · change AEMeasurable (multiplierDensity (chartFunction u e) c
      (fun z => h (e.val.symm z))) _
    rw [hhval, hdens]
    exact aemeasurable_const
  · change (∫⁻ z in ball (e.val x) 1,
      multiplierDensity (chartFunction u e) c (fun z => h (e.val.symm z)) z) < ⊤
    rw [hhval, hdens, lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

/-- A genuine zero-dimensional original potential has the actual unit
multiplier ideal. The SAME density is finite by its internally produced
genuine PSH condition, so its residual is constructed on open singletons. -/
theorem hasAnalyticSingularitiesOfType_originalWeight_zero {Z : Type*}
    [TopologicalSpace Z] [ChartedSpace (ComplexModel 0) Z] [IsComplexManifold 0 Z]
    [CompactSpace Z] (F : FixedChartCover 0 Z) (omega : KahlerBackground 0 Z)
    (θ : ClosedRealOneOneForm 0 Z) (ρ : F.t → ComplexModel 0 → ℝ)
    (hρ : ∀ j, IsSmoothLocalPotential θ.val (F.chart j)
      (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {u : Z → EReal} (hu : IsThetaPshPotential θ.val u) {m : ℕ} (hm : 0 < m) (a : ℝ) :
    HasAnalyticSingularitiesOfType (n := 0)
      (fun x => originalWeight F ρ u m x + (a : EReal)) ((m : ℚ)⁻¹)
      (multiplierIdeal (n := 0) (m : ℝ) u) := by
  classical
  let one : Fin 1 → Z → ℂ := fun _ _ => 1
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hspan : ∀ y h, (multiplierIdeal (n := 0) (m : ℝ) u).mem y h ↔
      IsInSpanAt (n := 0) (· ∈ range one) y h := by
    intro y h
    rw [multiplierIdeal_mem_iff_holomorphic_zero hu hmR]
    constructor
    · intro hh
      exact ⟨hh, 1, one, fun _ => h, fun _ => ⟨0, rfl⟩, fun _ => hh,
        Eventually.of_forall fun z => by simp [one]⟩
    · exact fun hh => hh.1
  have hone : ∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel 0) 𝓘(ℂ, ℂ) (one i) univ :=
    fun _ => mdifferentiableOn_const
  have hcoh : (multiplierIdeal (n := 0) (m : ℝ) u).IsCoherent := fun x =>
    ⟨univ, isOpen_univ, mem_univ x, 1, one, hone, fun y _ h => hspan y h⟩
  obtain ⟨C, -, hpsh⟩ := exists_uniform_original_density_theta_psh F omega
  have hv := (hpsh θ ρ hρ u hu m hm).add_const a
  refine ⟨inv_pos.mpr (Nat.cast_pos.mpr hm), hcoh, fun x => ?_⟩
  have hx := isOpen_singleton_of_dim_zero x
  refine ⟨{x}, hx, rfl, 1, one, fun i => (hone i).mono (subset_univ _),
    fun y _ h => hspan y h, fun _ => (originalWeight F ρ u m x + (a : EReal)).toReal,
    |(originalWeight F ρ u m x + (a : EReal)).toReal|,
    fun y _ => le_rfl, fun y hy => ?_⟩
  rw [mem_singleton_iff.mp hy]
  have hlog : generatorLog one x = 0 := by
    rw [generatorLog_eq_log_sum]
    simp [one]
  rw [hlog, mul_zero, zero_add]
  exact finite_of_dim_zero hv x

private theorem exact_type_alln [CompactSpace X] (F : FixedChartCover n X)
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (ρ : F.t → ComplexModel n → ℝ)
    (hρ : ∀ j, IsSmoothLocalPotential θ.val (F.chart j)
      (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {u : X → EReal} (hu : IsThetaPshPotential θ.val u) {m : ℕ} (hm : 0 < m) (a : ℝ) :
    HasAnalyticSingularitiesOfType (n := n)
      (fun x => originalWeight F ρ u m x + (a : EReal)) ((m : ℚ)⁻¹)
      (multiplierIdeal (n := n) (m : ℝ) u) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact hasAnalyticSingularitiesOfType_originalWeight_zero F omega θ ρ hρ hu hm a
  · exact hasAnalyticSingularitiesOfType_originalWeight_add_const hn F θ ρ hρ hu hm a

/-- Uniform constants before ALL original data give every literal QEA field
for the SAME original squared density, including its true ambientzero axis. -/
theorem exists_uniform_original_density_full_qea [CompactSpace X]
    (F : FixedChartCover n X) (omega : KahlerBackground n X) :
    ∃ C E : ℝ, 0 < C ∧ 0 ≤ E ∧ ∀ (θ : ClosedRealOneOneForm n X)
      (ρ : F.t → ComplexModel n → ℝ),
      (∀ j, IsSmoothLocalPotential θ.val (F.chart j)
        (ball (F.center j) (F.potentialRadius j)) (ρ j)) →
      ∀ (u : X → EReal), IsThetaPshPotential θ.val u →
        (∀ ℓ : ℕ, HasAnalyticSingularitiesOfType (n := n)
          (fun x => originalWeight F ρ u (2 ^ ℓ) x +
            ((E * ((2 : ℝ) ^ ℓ)⁻¹ : ℝ) : EReal)) (((2 ^ ℓ : ℕ) : ℚ)⁻¹)
          (multiplierIdeal (n := n) ((2 ^ ℓ : ℕ) : ℝ) u)) ∧
        IsQuasiEquisingularApproximation omega θ u
          (fun ℓ => C * ((2 : ℝ) ^ ℓ)⁻¹)
          (fun ℓ x => originalWeight F ρ u (2 ^ ℓ) x +
            ((E * ((2 : ℝ) ^ ℓ)⁻¹ : ℝ) : EReal)) := by
  obtain ⟨C, hC, hpsh⟩ := exists_uniform_original_density_theta_psh F omega
  obtain ⟨E, hE, hconv⟩ := exists_uniform_original_density_dyadic_convergence F
  refine ⟨C, E, hC, hE, ?_⟩
  intro θ ρ hρ u hu
  have htype : ∀ ℓ : ℕ, HasAnalyticSingularitiesOfType (n := n)
      (fun x => originalWeight F ρ u (2 ^ ℓ) x +
        ((E * ((2 : ℝ) ^ ℓ)⁻¹ : ℝ) : EReal)) (((2 ^ ℓ : ℕ) : ℚ)⁻¹)
      (multiplierIdeal (n := n) ((2 ^ ℓ : ℕ) : ℝ) u) :=
    fun ℓ => exact_type_alln F omega θ ρ hρ hu (by positivity) _
  have hseq := hconv θ ρ hρ u hu
  refine ⟨htype, hu, ⟨fun ℓ => by positivity, ?_, ?_⟩, ?_,
    fun ℓ => (htype ℓ).hasManifoldAnalyticSingularityType,
    ⟨fun x => (hseq x).1, fun x => (hseq x).2⟩, ?_⟩
  · intro a b hab
    apply mul_le_mul_of_nonneg_left _ hC.le
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hab)
  · have ht := (tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))).const_mul C
    simpa only [Function.comp_def, mul_zero] using ht
  · intro ℓ
    have hp := (hpsh θ ρ hρ u hu (2 ^ ℓ) (by positivity)).add_const
      (E * ((2 : ℝ) ^ ℓ)⁻¹)
    simpa only [Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv] using hp
  · intro c d hc hcd
    have hdc : 0 < d - c := sub_pos.mpr hcd
    have hlevels : Tendsto (fun ℓ : ℕ => ((2 ^ ℓ : ℕ) : ℝ)) atTop atTop := by
      have hp := tendsto_pow_atTop_atTop_of_one_lt (one_lt_two : (1 : ℝ) < 2)
      exact hp.congr fun ℓ => by push_cast; rfl
    filter_upwards [hlevels.eventually_ge_atTop (c * d / (d - c))] with ℓ hℓ
    have hmcd : c * d ≤ ((2 ^ ℓ : ℕ) : ℝ) * (d - c) := (div_le_iff₀ hdc).mp hℓ
    have hle : ∀ x, u x ≤ originalWeight F ρ u (2 ^ ℓ) x +
        ((E * ((2 : ℝ) ^ ℓ)⁻¹ : ℝ) : EReal) :=
      fun x => (hseq x).1.le_of_tendsto (hseq x).2 ℓ
    exact QuasiEquisingularApproximationDemailly.multiplierIdealIncluded_of_hasAnalyticSingularitiesOfType
      hu.1.quasiPlurisubharmonic hle (by positivity) (htype ℓ) hc hcd hmcd

end SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityFullQea
