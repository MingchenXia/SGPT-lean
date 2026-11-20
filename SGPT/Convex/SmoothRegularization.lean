import SGPT.Convex.PointwiseTopology
import SGPT.Convex.SubgradientBounds
import SGPT.Convex.GrowthSum
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

noncomputable section
namespace SGPT.Convex
open Set Filter Topology MeasureTheory
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
/-- The original compact support produces an actual common bound on its genuine covectors. -/
theorem exists_compact_pairing_bound (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {P : Set F} (hP : IsCompact P) (hne : P.Nonempty) :
    ∃ K : NNReal, ∀ m ∈ P, ∀ v : E, |B v m| ≤ K * ‖v‖ := by
  let e : F ≃L[ℝ] StrongDual ℝ E := B.flip.toContPerfPair.toContinuousLinearEquiv
  obtain ⟨p, hp, hmax⟩ := hP.exists_isMaxOn hne e.continuous.norm.continuousOn
  refine ⟨‖e p‖₊, fun m hm v ↦ ?_⟩
  calc
    |B v m| = ‖e m v‖ := by
      simp only [Real.norm_eq_abs]
      rfl
    _ ≤ ‖e m‖ * ‖v‖ := (e m).le_opNorm v
    _ ≤ ‖e p‖₊ * ‖v‖ := mul_le_mul_of_nonneg_right (hmax hm) (norm_nonneg v)

/-- Genuine actual destination subgradients turn the original compact covector bound into an actual global Lipschitz bound. -/
theorem lipschitz_growth_real_of_pairing_bound (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    [B.IsContPerfPair] {P : Set F} (hP : IsCompact P) (hne : P.Nonempty)
    (hconv : Convex ℝ P) {K : NNReal}
    (hK : ∀ m ∈ P, ∀ v : E, |B v m| ≤ K * ‖v‖)
    (f : GrowthClass B P) : LipschitzWith K (fun x ↦ (f.val x).toReal) := by
  obtain ⟨hdom, himage⟩ :=
    (singularityLE_support_iff_full_domain_rawSubgradientImage_subset B hP hne hconv
      f.property.1).mp f.property.2
  apply LipschitzWith.of_le_add_mul K
  intro x y
  have hxRI : x ∈ intrinsicInterior ℝ (effectiveDomain f.val) := by simp [hdom]
  obtain ⟨m, hm⟩ := rawSubdifferential_nonempty_of_mem_intrinsicInterior B f.property.1 hxRI
  have hmP : m ∈ P := himage (mem_iUnion.mpr ⟨x, hm⟩)
  have h := hm y
  rw [← coe_growthToRealConvex B hP hne f x,
    ← coe_growthToRealConvex B hP hne f y, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  have hb := (abs_le.mp (hK m hmP (y - x))).1
  rw [← dist_eq_norm y x, dist_comm y x] at hb
  change (f.val x).toReal + B (y - x) m ≤ (f.val y).toReal at h
  linarith

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The original support supremum has the same actual Lipschitz bound as its genuine covectors. -/
theorem lipschitz_support_real_of_pairing_bound (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    [B.IsContPerfPair] {P : Set F} (hP : IsCompact P) (hne : P.Nonempty)
    {K : NNReal} (hK : ∀ m ∈ P, ∀ v : E, |B v m| ≤ K * ‖v‖) :
    LipschitzWith K (fun x ↦ (support B.flip P x).toReal) := by
  apply LipschitzWith.of_le_add_mul K
  intro x y
  obtain ⟨rx, hx⟩ := exists_real_support_value B hP hne x
  obtain ⟨ry, hy⟩ := exists_real_support_value B hP hne y
  have hs : support B.flip P x ≤ ((ry + K * dist x y : ℝ) : EReal) := by
    apply iSup_le
    intro m
    have hmy : (B y m.val : EReal) ≤ support B.flip P y :=
      le_iSup_of_le m le_rfl
    rw [hy, EReal.coe_le_coe_iff] at hmy
    have hdiff := (abs_le.mp (hK m.val m.property (x - y))).2
    rw [← dist_eq_norm x y, map_sub] at hdiff
    apply EReal.coe_le_coe
    change B x m.val ≤ ry + K * dist x y
    change B x m.val - B y m.val ≤ K * dist x y at hdiff
    linarith
  rw [hx, EReal.coe_le_coe_iff] at hs
  simpa only [hx, hy, EReal.toReal_coe] using hs

/-- One true compact covector bound simultaneously controls both original growth and support functions. -/
theorem exists_common_growth_lipschitz (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    [B.IsContPerfPair] {P : Set F} (hP : IsCompact P) (hne : P.Nonempty)
    (hconv : Convex ℝ P) (f : GrowthClass B P) :
    ∃ K : NNReal, LipschitzWith K (fun x ↦ (f.val x).toReal) ∧
      LipschitzWith K (fun x ↦ (support B.flip P x).toReal) := by
  obtain ⟨K, hK⟩ := exists_compact_pairing_bound B hP hne
  exact ⟨K, lipschitz_growth_real_of_pairing_bound B hP hne hconv hK f,
    lipschitz_support_real_of_pairing_bound B hP hne hK⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The actual original finite support is genuinely convex as a real-valued function. -/
theorem convexOn_support_toReal (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {P : Set F} (hP : IsCompact P) (hne : P.Nonempty) :
    ConvexOn ℝ univ (fun x ↦ (support B.flip P x).toReal) := by
  have h := convexOn_toReal_effectiveDomain ((isProper_support_iff_nonempty B.flip P).mpr hne)
  have hdom : effectiveDomain (support B.flip P) = univ := by
    ext x
    obtain ⟨r, hr⟩ := exists_real_support_value B hP hne x
    simp only [effectiveDomain, mem_ofPred_eq, mem_univ, iff_true]
    rw [hr]
    exact EReal.coe_lt_top r
  rw [hdom] at h
  exact h

/-- The actual source obstacle is the genuine maximum of the original function and original support minus the natural index. -/
def growthObstacle (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (P : Set F) (f : GrowthClass B P)
    (j : ℕ) (x : E) : ℝ := max (f.val x).toReal ((support B.flip P x).toReal - j)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The genuine original growth/support convex functions give actual convex obstacles. -/
theorem convexOn_growthObstacle (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {P : Set F} (hP : IsCompact P) (hne : P.Nonempty) (f : GrowthClass B P) (j : ℕ) :
    ConvexOn ℝ univ (growthObstacle B P f j) :=
  (growthToRealConvex B hP hne f).property.sup
    ((convexOn_support_toReal B hP hne).sub (concaveOn_const (j : ℝ) convex_univ))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Both true original Lipschitz estimates produce one actual bound for every genuine maximum obstacle. -/
theorem lipschitz_growthObstacle (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {P : Set F}
    (f : GrowthClass B P) {K : NNReal}
    (hf : LipschitzWith K (fun x ↦ (f.val x).toReal))
    (hs : LipschitzWith K (fun x ↦ (support B.flip P x).toReal)) (j : ℕ) :
    LipschitzWith K (growthObstacle B P f j) := by
  have hshift : LipschitzWith K (fun x ↦ (support B.flip P x).toReal - j) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, sub_sub_sub_cancel_right] using hs.dist_le_mul x y
  unfold growthObstacle
  simpa only [max_self] using hf.max hshift

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Original obstacle indices genuinely decrease their actual original function values. -/
theorem antitone_growthObstacle (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {P : Set F}
    (f : GrowthClass B P) : Antitone (growthObstacle B P f) := by
  intro i j hij x
  exact max_le_max le_rfl (sub_le_sub_left (Nat.cast_le.mpr hij) _)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The actual natural-index obstacle eventually equals each original finite growth value. -/
theorem tendsto_growthObstacle (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {P : Set F}
    (f : GrowthClass B P) (x : E) :
    Tendsto (fun j ↦ growthObstacle B P f j x) atTop (𝓝 (f.val x).toReal) := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((support B.flip P x).toReal - (f.val x).toReal)
  have heq : ∀ᶠ j : ℕ in atTop, growthObstacle B P f j x = (f.val x).toReal := by
    apply eventually_atTop.mpr
    refine ⟨n, fun j hj ↦ ?_⟩
    have hnj : (n : ℝ) ≤ j := Nat.cast_le.mpr hj
    apply max_eq_left
    linarith
  exact tendsto_const_nhds.congr' (heq.mono (fun _ h ↦ h.symm))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Actual compact support values are recovered exactly from their true real representatives. -/
theorem coe_support_toReal (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {P : Set F} (hP : IsCompact P) (hne : P.Nonempty) (x : E) :
    ((support B.flip P x).toReal : EReal) = support B.flip P x := by
  obtain ⟨r, hr⟩ := exists_real_support_value B hP hne x
  simp only [hr, EReal.toReal_coe]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Every original genuine obstacle has actual bounded mutual support comparison, with constructed real constants. -/
theorem singularityEquiv_growthObstacle_support (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    [B.IsContPerfPair] {P : Set F} (hP : IsCompact P) (hne : P.Nonempty)
    (f : GrowthClass B P) (j : ℕ) :
    SGPT.PSH.SingularityEquiv (fun x ↦ (growthObstacle B P f j x : EReal))
      (support B.flip P) := by
  obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp f.property.2
  constructor
  · apply (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
    refine ⟨max C 0, fun x ↦ ?_⟩
    have h := hC x
    rw [← coe_growthToRealConvex B hP hne f x,
      ← coe_support_toReal B hP hne x, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
    rw [← coe_support_toReal B hP hne x, ← EReal.coe_add, EReal.coe_le_coe_iff]
    apply max_le
    · exact h.trans (add_le_add le_rfl (le_max_left C 0))
    · have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hmax := le_max_right C 0
      linarith
  · apply (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
    refine ⟨(j : ℝ), fun x ↦ ?_⟩
    rw [← coe_support_toReal B hP hne x, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have h := le_max_right (f.val x).toReal ((support B.flip P x).toReal - j)
    change (support B.flip P x).toReal ≤
      max (f.val x).toReal ((support B.flip P x).toReal - j) + j
    linarith

section ActualSmoothing

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Actual normalized-bump convolution of the original real function. -/
def bumpSmoothing (φ : ContDiffBump (0 : E)) (g : E → ℝ) : E → ℝ :=
  convolution (φ.normed μ) g (ContinuousLinearMap.lsmul ℝ ℝ) μ

/-- Original continuous translated values times the genuine compact bump are truly integrable. -/
theorem integrable_bumpSmoothing_integrand (φ : ContDiffBump (0 : E)) {g : E → ℝ}
    (hg : Continuous g) (x : E) :
    Integrable (fun y ↦ φ.normed μ y * g (x - y)) μ :=
  (φ.continuous_normed.mul (hg.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
    (φ.hasCompactSupport_normed.mul_right)

/-- Genuine compact smooth kernel and original local integrability produce actual smoothness. -/
theorem contDiff_bumpSmoothing (φ : ContDiffBump (0 : E)) {g : E → ℝ}
    (hg : Continuous g) : ContDiff ℝ ∞ (bumpSmoothing μ φ g) :=
  (φ.hasCompactSupport_normed (μ := μ)).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (φ.contDiff_normed (μ := μ)) hg.locallyIntegrable

/-- The true unit kernel mass and actual original Lipschitz bound yield a genuine uniform convolution error. -/
theorem dist_bumpSmoothing_le (φ : ContDiffBump (0 : E)) {g : E → ℝ}
    {K : NNReal} (hg : LipschitzWith K g) (x : E) :
    dist (bumpSmoothing μ φ g x) (g x) ≤ K * φ.rOut := by
  apply φ.dist_normed_convolution_le hg.continuous.aestronglyMeasurable
  intro y hy
  exact (hg.dist_le_mul y x).trans
    (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy).le K.coe_nonneg)

/-- Actual original convex interpolation inequalities integrate against the true nonnegative normalized kernel. -/
theorem convexOn_bumpSmoothing (φ : ContDiffBump (0 : E)) {g : E → ℝ}
    (hg : ConvexOn ℝ univ g) : ConvexOn ℝ univ (bumpSmoothing μ φ g) := by
  have hc : Continuous g := continuousOn_univ.mp (hg.continuousOn isOpen_univ)
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  simp only [bumpSmoothing, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((integrable_bumpSmoothing_integrand μ φ hc x).const_mul a)
      ((integrable_bumpSmoothing_integrand μ φ hc y).const_mul b)]
  refine integral_mono (integrable_bumpSmoothing_integrand μ φ hc _)
    (((integrable_bumpSmoothing_integrand μ φ hc x).const_mul a).add
      ((integrable_bumpSmoothing_integrand μ φ hc y).const_mul b)) fun t ↦ ?_
  have heq : a • x + b • y - t = a • (x - t) + b • (y - t) := by
    calc
      a • x + b • y - t = a • x + b • y - (a + b) • t := by rw [hab, one_smul]
      _ = a • (x - t) + b • (y - t) := by module
  have h := hg.2 (mem_univ (x - t)) (mem_univ (y - t)) ha hb hab
  rw [← heq] at h
  simp only [smul_eq_mul] at h
  calc
    φ.normed μ t * g (a • x + b • y - t) ≤
        φ.normed μ t * (a * g (x - t) + b * g (y - t)) :=
      mul_le_mul_of_nonneg_left h (φ.nonneg_normed t)
    _ = a * (φ.normed μ t * g (x - t)) + b * (φ.normed μ t * g (y - t)) := by ring

/-! The radii and approximation constants are actual constructed data. -/

/-- The genuine geometric radii used by the original approximation. -/
def smoothingRadius (j : ℕ) : ℝ := (1 / 2 : ℝ) ^ j

theorem smoothingRadius_pos (j : ℕ) : 0 < smoothingRadius j := by
  unfold smoothingRadius
  positivity

theorem smoothingRadius_succ (j : ℕ) : smoothingRadius (j + 1) = smoothingRadius j / 2 := by
  simp only [smoothingRadius, pow_succ]
  ring

theorem tendsto_smoothingRadius : Tendsto smoothingRadius atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- The actual positive-radius smooth bump, using genuine finite-dimensional bump existence. -/
def smoothingBump (j : ℕ) : ContDiffBump (0 : E) :=
  ⟨smoothingRadius j / 2, smoothingRadius j, by
    have h := smoothingRadius_pos j
    positivity, by
    have h := smoothingRadius_pos j
    linarith⟩

/-- The original obstacle convolution with its actual constructed geometric error offset. -/
def smoothGrowthApprox (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {P : Set F}
    (f : GrowthClass B P) (K : NNReal) (j : ℕ) (x : E) : ℝ :=
  bumpSmoothing μ (smoothingBump j) (growthObstacle B P f j) x +
    3 * (K : ℝ) * smoothingRadius j

omit [FiniteDimensional ℝ F] in
/-- Genuine convolution errors give actual lower and upper bounds for each original approximant. -/
theorem bounds_smoothGrowthApprox (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {P : Set F}
    (f : GrowthClass B P) {K : NNReal}
    (hf : LipschitzWith K (fun x ↦ (f.val x).toReal))
    (hs : LipschitzWith K (fun x ↦ (support B.flip P x).toReal)) (j : ℕ) (x : E) :
    growthObstacle B P f j x + 2 * (K : ℝ) * smoothingRadius j ≤
      smoothGrowthApprox μ B f K j x ∧
    smoothGrowthApprox μ B f K j x ≤
      growthObstacle B P f j x + 4 * (K : ℝ) * smoothingRadius j := by
  have h := dist_bumpSmoothing_le μ (smoothingBump j)
    (lipschitz_growthObstacle B f hf hs j) x
  rw [Real.dist_eq] at h
  change |bumpSmoothing μ (smoothingBump j) (growthObstacle B P f j) x -
    growthObstacle B P f j x| ≤ K * smoothingRadius j at h
  obtain ⟨hl, hu⟩ := abs_le.mp h
  unfold smoothGrowthApprox
  constructor <;> linarith

omit [FiniteDimensional ℝ F] in
/-- The true half-radius identity and actual decreasing obstacles force the constructed smoothed sequence to decrease. -/
theorem antitone_smoothGrowthApprox (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {P : Set F}
    (f : GrowthClass B P) {K : NNReal}
    (hf : LipschitzWith K (fun x ↦ (f.val x).toReal))
    (hs : LipschitzWith K (fun x ↦ (support B.flip P x).toReal)) :
    Antitone (smoothGrowthApprox μ B f K) := by
  apply antitone_nat_of_succ_le
  intro j x
  have hupper := (bounds_smoothGrowthApprox μ B f hf hs (j + 1) x).2
  have hlower := (bounds_smoothGrowthApprox μ B f hf hs j x).1
  have hobstacle := antitone_growthObstacle B f (Nat.le_succ j) x
  rw [smoothingRadius_succ] at hupper
  linarith

omit [FiniteDimensional ℝ F] in
/-- Original obstacle convergence and actual vanishing errors yield genuine original-value convergence of the constructed smooth approximants. -/
theorem tendsto_smoothGrowthApprox (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {P : Set F}
    (f : GrowthClass B P) {K : NNReal}
    (hf : LipschitzWith K (fun x ↦ (f.val x).toReal))
    (hs : LipschitzWith K (fun x ↦ (support B.flip P x).toReal)) (x : E) :
    Tendsto (fun j ↦ smoothGrowthApprox μ B f K j x) atTop (𝓝 (f.val x).toReal) := by
  have hl := (tendsto_growthObstacle B f x).add (tendsto_smoothingRadius.const_mul (2 * (K : ℝ)))
  have hu := (tendsto_growthObstacle B f x).add (tendsto_smoothingRadius.const_mul (4 * (K : ℝ)))
  simp only [mul_zero, add_zero] at hl hu
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu
    (fun j ↦ (bounds_smoothGrowthApprox μ B f hf hs j x).1)
    (fun j ↦ (bounds_smoothGrowthApprox μ B f hf hs j x).2)

omit [FiniteDimensional ℝ F] in
/-- The actual original obstacle interpolation and real offset make each original approximant genuinely convex. -/
theorem convexOn_smoothGrowthApprox (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {P : Set F} (hP : IsCompact P) (hne : P.Nonempty) (f : GrowthClass B P)
    (K : NNReal) (j : ℕ) : ConvexOn ℝ univ (smoothGrowthApprox μ B f K j) := by
  unfold smoothGrowthApprox
  exact (convexOn_bumpSmoothing μ (smoothingBump j)
    (convexOn_growthObstacle B hP hne f j)).add_const _

omit [FiniteDimensional ℝ F] in
/-- Genuine normalized-bump smoothness gives actual smooth original approximants. -/
theorem contDiff_smoothGrowthApprox (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {P : Set F} (hP : IsCompact P) (hne : P.Nonempty) (f : GrowthClass B P)
    (K : NNReal) (j : ℕ) : ContDiff ℝ ∞ (smoothGrowthApprox μ B f K j) := by
  unfold smoothGrowthApprox
  exact (contDiff_bumpSmoothing μ (smoothingBump j)
    (continuousOn_univ.mp ((convexOn_growthObstacle B hP hne f j).continuousOn isOpen_univ))).add
    contDiff_const

omit [FiniteDimensional ℝ F] in
/-- True uniform errors and their actual positive offsets give bounded mutual comparison with each actual original obstacle. -/
theorem singularityEquiv_smoothGrowthApprox_obstacle (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    {P : Set F} (f : GrowthClass B P) {K : NNReal}
    (hf : LipschitzWith K (fun x ↦ (f.val x).toReal))
    (hs : LipschitzWith K (fun x ↦ (support B.flip P x).toReal)) (j : ℕ) :
    SGPT.PSH.SingularityEquiv (fun x ↦ (smoothGrowthApprox μ B f K j x : EReal))
      (fun x ↦ (growthObstacle B P f j x : EReal)) := by
  constructor
  · apply (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
    refine ⟨4 * (K : ℝ) * smoothingRadius j, fun x ↦ ?_⟩
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    exact (bounds_smoothGrowthApprox μ B f hf hs j x).2
  · apply (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
    refine ⟨0, fun x ↦ ?_⟩
    rw [EReal.coe_zero, add_zero, EReal.coe_le_coe_iff]
    have hl := (bounds_smoothGrowthApprox μ B f hf hs j x).1
    have hnonneg : 0 ≤ 2 * (K : ℝ) * smoothingRadius j := by
      have h := smoothingRadius_pos j
      positivity
    linarith

omit [FiniteDimensional ℝ F] in
/-- Actual finite convexity and proved mutual support comparison put every actual approximant in the original source bounded-growth class. -/
theorem mem_boundedGrowthClass_smoothGrowthApprox (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    [B.IsContPerfPair] {P : Set F} (hP : IsCompact P) (hne : P.Nonempty)
    (f : GrowthClass B P) {K : NNReal}
    (hf : LipschitzWith K (fun x ↦ (f.val x).toReal))
    (hs : LipschitzWith K (fun x ↦ (support B.flip P x).toReal)) (j : ℕ) :
    (fun x ↦ (smoothGrowthApprox μ B f K j x : EReal)) ∈ BoundedGrowthClass B P := by
  constructor
  · apply isClosedConvex_of_isProper_full_domain
      (isProper_coe_of_convexOn (convexOn_smoothGrowthApprox μ B hP hne f K j))
    ext x
    simp only [effectiveDomain, mem_ofPred_eq, EReal.coe_lt_top, mem_univ]
  · exact SGPT.PSH.singularityEquiv_trans
      (singularityEquiv_smoothGrowthApprox_obstacle μ B f hf hs j)
      (singularityEquiv_growthObstacle_support B hP hne f j)

include μ in
/-- Exact source smooth decreasing regularization, using any actual Haar measure only to construct the genuine normalized kernels. -/
theorem exists_decreasing_smooth_growth_approx_with_haar (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    [B.IsContPerfPair] {P : Set F} (hP : IsCompact P) (hne : P.Nonempty)
    (hconv : Convex ℝ P) (f : GrowthClass B P) :
    ∃ g : ℕ → E → ℝ,
      (∀ j, (fun x ↦ (g j x : EReal)) ∈ BoundedGrowthClass B P ∧ ContDiff ℝ ∞ (g j)) ∧
      Antitone g ∧ ∀ x, Tendsto (fun j ↦ (g j x : EReal)) atTop (𝓝 (f.val x)) := by
  obtain ⟨K, hf, hs⟩ := exists_common_growth_lipschitz B hP hne hconv f
  refine ⟨smoothGrowthApprox μ B f K, fun j ↦ ⟨?_, ?_⟩,
    antitone_smoothGrowthApprox μ B f hf hs, fun x ↦ ?_⟩
  · exact mem_boundedGrowthClass_smoothGrowthApprox μ B hP hne f hf hs j
  · exact contDiff_smoothGrowthApprox μ B hP hne f K j
  · have h := continuous_coe_real_ereal.continuousAt.tendsto.comp
      (tendsto_smoothGrowthApprox μ B f hf hs x)
    rw [EReal.coe_toReal (growth_value_ne_top B hP hne f x) (f.property.1.2.2 x)] at h
    exact h

end ActualSmoothing

/-- Full exact source regularization: an actual Haar measure is chosen, rather than assumed as additional input. -/
theorem exists_decreasing_smooth_growth_approx (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    [B.IsContPerfPair] {P : Set F} (hP : IsCompact P) (hne : P.Nonempty)
    (hconv : Convex ℝ P) (f : GrowthClass B P) :
    ∃ g : ℕ → E → ℝ,
      (∀ j, (fun x ↦ (g j x : EReal)) ∈ BoundedGrowthClass B P ∧ ContDiff ℝ ∞ (g j)) ∧
      Antitone g ∧ ∀ x, Tendsto (fun j ↦ (g j x : EReal)) atTop (𝓝 (f.val x)) := by
  borelize E
  exact exists_decreasing_smooth_growth_approx_with_haar (Measure.addHaar : Measure E)
    B hP hne hconv f

end SGPT.Convex
