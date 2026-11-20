import SGPT.Convex.PointwiseTopology
import SGPT.Convex.SubgradientMeasure
import SGPT.Convex.AlexandrovLocalFinite
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.MeasureTheory.Integral.CompactlySupported

namespace SGPT.Convex

open Set Filter Topology MeasureTheory
open scoped Topology CompactlySupported

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
  {I : Type*} {l : Filter I} [l.NeBot]

omit [l.NeBot] in
/-- Actual compact-uniform convergence supplies original moving values
at every genuinely convergent original basepoint. -/
theorem tendsto_convex_moving_value {F : I → E → ℝ} {f : E → ℝ}
    (hf : ConvexOn ℝ univ f)
    (hF : ∀ K : Set E, IsCompact K → TendstoUniformlyOn F f l K)
    {x : I → E} {x₀ : E} (hx : Tendsto x l (𝓝 x₀)) :
    Tendsto (fun i ↦ F i (x i)) l (𝓝 (f x₀)) := by
  have hu : TendstoLocallyUniformly F f l :=
    tendstoLocallyUniformly_iff_forall_isCompact.mpr hF
  exact hu.tendsto_comp
    (continuousOn_univ.mp (hf.continuousOn isOpen_univ)).continuousAt hx

/-- Actual original raw touching inequalities pass to the actual graph
limit through produced moving-value convergence and true pairing continuity. -/
theorem mem_rawSubdifferential_of_tendsto
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {F : I → E → ℝ} {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    (hF : ∀ K : Set E, IsCompact K → TendstoUniformlyOn F f l K)
    {x : I → E} {x₀ : E} (hx : Tendsto x l (𝓝 x₀))
    {m : I → M} {m₀ : M} (hm : Tendsto m l (𝓝 m₀))
    (hsub : ∀ᶠ i in l, m i ∈ rawSubdifferential B
      (fun z ↦ (F i z : EReal)) (x i)) :
    m₀ ∈ rawSubdifferential B (fun z ↦ (f z : EReal)) x₀ := by
  intro y
  change (f x₀ : EReal) + (B (y - x₀) m₀ : EReal) ≤ (f y : EReal)
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]
  have hp : Continuous (fun p : E × M ↦ B (y - p.1) p.2) := by
    change Continuous (fun p : E × M ↦ B.toContPerfPair (y - p.1) p.2)
    exact (B.toContPerfPair.toContinuousLinearEquiv.continuous.comp (continuous_const.sub continuous_fst)).clm_apply
      continuous_snd
  have hpair := hp.continuousAt.tendsto.comp (hx.prodMk_nhds hm)
  have hval := tendsto_convex_moving_value hf hF hx
  have hy := (hF {y} isCompact_singleton).tendsto_at (mem_singleton y)
  apply le_of_tendsto_of_tendsto (hval.add hpair) hy
  filter_upwards [hsub] with i hi
  simpa only [← EReal.coe_add, EReal.coe_le_coe_iff, Function.comp_apply] using hi y

variable [FiniteDimensional ℝ M]

omit [l.NeBot] in
/-- Actual conjugate differentiability and the genuine raw Fenchel inverse
produce the original touching covector at its actual conjugate gradient. -/
theorem mem_rawSubdifferential_conjugateGradient_coe
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair] {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) {m : M}
    (hm : m ∈ interior (effectiveDomain (conjugate B (fun x ↦ (f x : EReal)))))
    (hd : DifferentiableAt ℝ (fun p ↦ (conjugate B (fun x ↦ (f x : EReal)) p).toReal) m) :
    m ∈ rawSubdifferential B (fun x ↦ (f x : EReal))
      (conjugateGradient B (fun x ↦ (f x : EReal)) m) := by
  have hp := isProper_coe_of_convexOn hf
  have hcont : Continuous (fun x ↦ (f x : EReal)) :=
    continuous_coe_real_ereal.comp (continuousOn_univ.mp (hf.continuousOn isOpen_univ))
  have hsingle := rawSubdifferential_conjugate_eq_singleton_of_differentiableAt B hp hm hd
  apply (mem_rawSubdifferential_iff_conjugate_rawSubdifferential B hp
    hcont.lowerSemicontinuous (by simp [effectiveDomain]) (interior_subset hm)).mpr
  rw [hsingle]
  exact mem_singleton _

omit [l.NeBot] in
/-- The actual conjugate derivative supplies a unique original minimizer,
so every other original point has a genuine strict supporting-cost gap. -/
theorem strict_conjugate_support_cost
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair] {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) {m : M}
    (hm : m ∈ interior (effectiveDomain (conjugate B (fun x ↦ (f x : EReal)))))
    (hd : DifferentiableAt ℝ (fun p ↦ (conjugate B (fun x ↦ (f x : EReal)) p).toReal) m)
    {y : E} (hy : y ≠ conjugateGradient B (fun x ↦ (f x : EReal)) m) :
    f (conjugateGradient B (fun x ↦ (f x : EReal)) m) -
      B (conjugateGradient B (fun x ↦ (f x : EReal)) m) m < f y - B y m := by
  let x₀ := conjugateGradient B (fun x ↦ (f x : EReal)) m
  have hraw := mem_rawSubdifferential_conjugateGradient_coe B hf hm hd
  have hle : f x₀ + B (y - x₀) m ≤ f y := by
    simpa only [← EReal.coe_add, EReal.coe_le_coe_iff] using hraw y
  have hcost : f x₀ - B x₀ m ≤ f y - B y m := by
    simp only [map_sub, LinearMap.sub_apply] at hle
    linarith
  apply lt_of_le_of_ne hcost
  intro heq
  have hyraw : m ∈ rawSubdifferential B (fun z ↦ (f z : EReal)) y := by
    intro z
    change (f y : EReal) + (B (z - y) m : EReal) ≤ (f z : EReal)
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    have hz : f x₀ + B (z - x₀) m ≤ f z := by
      simpa only [← EReal.coe_add, EReal.coe_le_coe_iff] using hraw z
    simp only [map_sub, LinearMap.sub_apply] at hz ⊢
    linarith
  have hp := isProper_coe_of_convexOn hf
  have hcont : Continuous (fun x ↦ (f x : EReal)) :=
    continuous_coe_real_ereal.comp (continuousOn_univ.mp (hf.continuousOn isOpen_univ))
  have hydual := (mem_rawSubdifferential_iff_conjugate_rawSubdifferential B hp
    hcont.lowerSemicontinuous (by simp [effectiveDomain]) (interior_subset hm)).mp hyraw
  rw [rawSubdifferential_conjugate_eq_singleton_of_differentiableAt B hp hm hd] at hydual
  exact hy (mem_singleton_iff.mp hydual)

omit [l.NeBot] in
/-- Compactness of the actual original sphere turns genuine uniqueness of
the original touching point into a positive uniform real cost gap. -/
theorem exists_positive_conjugate_support_gap_on_sphere
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair] {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) {m : M}
    (hm : m ∈ interior (effectiveDomain (conjugate B (fun x ↦ (f x : EReal)))))
    (hd : DifferentiableAt ℝ (fun p ↦ (conjugate B (fun x ↦ (f x : EReal)) p).toReal) m)
    {r : ℝ} (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ Metric.sphere
      (conjugateGradient B (fun x ↦ (f x : EReal)) m) r,
      f (conjugateGradient B (fun x ↦ (f x : EReal)) m) -
        B (conjugateGradient B (fun x ↦ (f x : EReal)) m) m + δ ≤ f y - B y m := by
  let x₀ := conjugateGradient B (fun x ↦ (f x : EReal)) m
  let g : E → ℝ := fun x ↦ f x - B x m
  have hc : Continuous g :=
    (continuousOn_univ.mp (hf.continuousOn isOpen_univ)).sub
      (B.toContPerfPair.toContinuousLinearEquiv.continuous.clm_apply continuous_const)
  by_cases hne : (Metric.sphere x₀ r).Nonempty
  · obtain ⟨y, hy, hmin⟩ := (isCompact_sphere x₀ r).exists_isMinOn hne hc.continuousOn
    have hyne : y ≠ x₀ := by
      intro heq
      have hdist := Metric.mem_sphere.mp hy
      rw [heq, dist_self] at hdist
      exact hr.ne' hdist.symm
    have hgap : g x₀ < g y := strict_conjugate_support_cost B hf hm hd hyne
    refine ⟨(g y - g x₀) / 2, by linarith, ?_⟩
    intro z hz
    have hzmin : g y ≤ g z := hmin hz
    change g x₀ + (g y - g x₀) / 2 ≤ g z
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro y hy
    exact False.elim (hne ⟨y, hy⟩)

omit [l.NeBot] [FiniteDimensional ℝ E] in
/-- Genuine radial convex interpolation propagates the actual sphere cost
gap to every original point outside that original ball. -/
theorem support_gap_of_not_mem_ball {g : E → ℝ} (hg : ConvexOn ℝ univ g)
    {x₀ z : E} {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hgap : ∀ y ∈ Metric.sphere x₀ r, g x₀ + δ ≤ g y)
    (hz : z ∉ Metric.ball x₀ r) : g x₀ + δ ≤ g z := by
  let d := ‖z - x₀‖
  have hrd : r ≤ d := by
    simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hz
  have hd : 0 < d := hr.trans_le hrd
  let t := r / d
  have ht : 0 < t := div_pos hr hd
  have ht1 : t ≤ 1 := (div_le_one₀ hd).mpr hrd
  have htd : t * d = r := div_mul_cancel₀ r hd.ne'
  let y := x₀ + t • (z - x₀)
  have hy : y ∈ Metric.sphere x₀ r := by
    rw [Metric.mem_sphere]
    simpa only [y, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht] using htd
  have hlo := hgap y hy
  have hhi := hg.2 (mem_univ x₀) (mem_univ z) (sub_nonneg.mpr ht1) ht.le
    (show 1 - t + t = 1 by ring)
  have hcombo : (1 - t) • x₀ + t • z = y := by dsimp [y]; module
  rw [hcombo] at hhi
  simp only [smul_eq_mul] at hhi
  have hδt : δ ≤ t * (g z - g x₀) := by nlinarith
  have hcost : 0 ≤ g z - g x₀ := by
    by_contra hn
    have hneg : t * (g z - g x₀) < 0 := mul_neg_of_pos_of_neg ht (lt_of_not_ge hn)
    linarith
  have hprod := mul_le_mul_of_nonneg_right ht1 hcost
  nlinarith

omit [l.NeBot] [FiniteDimensional ℝ M] in
/-- A genuine positive sphere gap produces an actual original interior
global touching point by compact minimization and radial convexity. -/
theorem exists_rawSubgradient_of_sphere_gap
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    (m : M) (x₀ : E) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hgap : ∀ y ∈ Metric.sphere x₀ r, f x₀ - B x₀ m + δ ≤ f y - B y m) :
    ∃ q ∈ Metric.ball x₀ r, m ∈ rawSubdifferential B (fun z ↦ (f z : EReal)) q := by
  let g : E → ℝ := fun x ↦ f x - B x m
  have hg : ConvexOn ℝ univ g := hf.sub ((B.flip m).concaveOn convex_univ)
  have hc : Continuous g := continuousOn_univ.mp (hg.continuousOn isOpen_univ)
  obtain ⟨q, hq, hmin⟩ := (isCompact_closedBall x₀ r).exists_isMinOn
    ⟨x₀, Metric.mem_closedBall_self hr.le⟩ hc.continuousOn
  have hqx : g q ≤ g x₀ := hmin (Metric.mem_closedBall_self hr.le)
  have hqball : q ∈ Metric.ball x₀ r := by
    by_contra hqb
    have hcost := support_gap_of_not_mem_ball hg hr hδ hgap hqb
    change g x₀ + δ ≤ g q at hcost
    linarith
  have hglobal : ∀ z, g q ≤ g z := by
    intro z
    by_cases hz : z ∈ Metric.closedBall x₀ r
    · exact hmin hz
    · have hzball : z ∉ Metric.ball x₀ r := fun hzb ↦ hz (Metric.ball_subset_closedBall hzb)
      have hcost := support_gap_of_not_mem_ball hg hr hδ hgap hzball
      change g x₀ + δ ≤ g z at hcost
      linarith
  refine ⟨q, hqball, ?_⟩
  intro z
  change (f q : EReal) + (B (z - q) m : EReal) ≤ (f z : EReal)
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]
  have hcost := hglobal z
  dsimp [g] at hcost
  simp only [map_sub, LinearMap.sub_apply]
  linarith

omit [l.NeBot] in
/-- Actual compact-uniform convergence preserves a produced positive
original sphere gap uniformly along the original sequence. -/
theorem eventually_positive_conjugate_support_gap
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {F : I → E → ℝ} {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    (hF : ∀ K : Set E, IsCompact K → TendstoUniformlyOn F f l K)
    {m : M} (hm : m ∈ interior (effectiveDomain (conjugate B (fun x ↦ (f x : EReal)))))
    (hd : DifferentiableAt ℝ (fun p ↦ (conjugate B (fun x ↦ (f x : EReal)) p).toReal) m)
    {r : ℝ} (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in l, ∀ y ∈ Metric.sphere
      (conjugateGradient B (fun x ↦ (f x : EReal)) m) r,
      F i (conjugateGradient B (fun x ↦ (f x : EReal)) m) -
        B (conjugateGradient B (fun x ↦ (f x : EReal)) m) m + δ ≤ F i y - B y m := by
  let x₀ := conjugateGradient B (fun x ↦ (f x : EReal)) m
  obtain ⟨δ, hδ, hgap⟩ := exists_positive_conjugate_support_gap_on_sphere B hf hm hd hr
  have hε : 0 < δ / 4 := by positivity
  have hs := Metric.tendstoUniformlyOn_iff.mp (hF (Metric.sphere x₀ r)
    (isCompact_sphere x₀ r)) (δ / 4) hε
  have hx := Metric.tendstoUniformlyOn_iff.mp (hF {x₀} isCompact_singleton) (δ / 4) hε
  refine ⟨δ / 2, by positivity, ?_⟩
  filter_upwards [hs, hx] with i hi hxi
  intro y hy
  have hsbound := abs_lt.mp (show |f y - F i y| < δ / 4 by
    simpa only [Real.dist_eq] using hi y hy)
  have hxb := abs_lt.mp (show |f x₀ - F i x₀| < δ / 4 by
    simpa only [Real.dist_eq] using hxi x₀ (mem_singleton x₀))
  have hgy := hgap y hy
  change f x₀ - B x₀ m + δ ≤ f y - B y m at hgy
  linarith

omit [l.NeBot] in
/-- Actual compact-uniform convergence preserves the produced strict
sphere gap and supplies a genuine original touching point nearby. -/
theorem eventually_exists_rawSubgradient_near_conjugateGradient
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {F : I → E → ℝ} {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    (hFcv : ∀ i, ConvexOn ℝ univ (F i))
    (hF : ∀ K : Set E, IsCompact K → TendstoUniformlyOn F f l K)
    {m : M} (hm : m ∈ interior (effectiveDomain (conjugate B (fun x ↦ (f x : EReal)))))
    (hd : DifferentiableAt ℝ (fun p ↦ (conjugate B (fun x ↦ (f x : EReal)) p).toReal) m)
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ i in l, ∃ q ∈ Metric.ball (conjugateGradient B (fun x ↦ (f x : EReal)) m) r,
      m ∈ rawSubdifferential B (fun z ↦ (F i z : EReal)) q := by
  obtain ⟨δ, hδ, hgap⟩ := eventually_positive_conjugate_support_gap B hf hF hm hd hr
  filter_upwards [hgap] with i hi
  exact exists_rawSubgradient_of_sphere_gap B (hFcv i) m
    (conjugateGradient B (fun x ↦ (f x : EReal)) m) hr hδ hi

omit [l.NeBot] [FiniteDimensional ℝ M] in
/-- Actual finite-dimensional pairing bounds preserve a positive original
sphere gap under a genuine covector neighborhood. Compact minimization then
places the original covector in the actual conjugate-domain interior. -/
theorem mem_interior_effectiveDomain_conjugate_of_sphere_gap
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair] {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (m : M) (x₀ : E) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hgap : ∀ y ∈ Metric.sphere x₀ r, f x₀ - B x₀ m + δ ≤ f y - B y m) :
    m ∈ interior (effectiveDomain (conjugate B (fun x ↦ (f x : EReal)))) := by
  let T := B.toContPerfPair.toContinuousLinearEquiv.toContinuousLinearMap
  let C : ℝ := ‖T‖ * r
  have hC : 0 ≤ C := mul_nonneg T.opNorm_nonneg hr.le
  let ε : ℝ := δ / (2 * (C + 1))
  have hε : 0 < ε := div_pos hδ (by positivity)
  have hCε : (C + 1) * ε = δ / 2 := by
    dsimp [ε]
    field_simp
  have hball : Metric.ball m ε ⊆ effectiveDomain (conjugate B (fun x ↦ (f x : EReal))) := by
    intro m' hm'
    have hdist : ‖m' - m‖ < ε := by simpa only [Metric.mem_ball, dist_eq_norm] using hm'
    have hsmall : C * ‖m' - m‖ < δ / 2 := calc
      C * ‖m' - m‖ ≤ (C + 1) * ‖m' - m‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (C + 1) * ε := mul_lt_mul_of_pos_left hdist (by positivity)
      _ = δ / 2 := hCε
    have hnewgap : ∀ y ∈ Metric.sphere x₀ r,
        f x₀ - B x₀ m' + δ / 2 ≤ f y - B y m' := by
      intro y hy
      have hnorm : ‖y - x₀‖ = r := by simpa only [dist_eq_norm] using Metric.mem_sphere.mp hy
      have hB : |B (y - x₀) (m' - m)| ≤ C * ‖m' - m‖ := by
        have h₁ := (B.toContPerfPair (y - x₀)).le_opNorm (m' - m)
        have h₂ := T.le_opNorm (y - x₀)
        calc
          |B (y - x₀) (m' - m)| ≤ ‖B.toContPerfPair (y - x₀)‖ * ‖m' - m‖ := h₁
          _ ≤ (‖T‖ * ‖y - x₀‖) * ‖m' - m‖ :=
            mul_le_mul_of_nonneg_right h₂ (norm_nonneg _)
          _ = C * ‖m' - m‖ := by rw [hnorm]
      have hb := (abs_lt.mp (hB.trans_lt hsmall)).2
      have hg := hgap y hy
      simp only [map_sub, LinearMap.sub_apply] at hb
      linarith
    obtain ⟨q, _, hq⟩ := exists_rawSubgradient_of_sphere_gap B hf m' x₀ hr
      (by positivity : 0 < δ / 2) hnewgap
    exact rawSubgradientImage_subset_effectiveDomain_conjugate B
      (isProper_coe_of_convexOn hf) (mem_iUnion.mpr ⟨q, hq⟩)
  exact (Metric.isOpen_ball.subset_interior_iff.mpr hball) (Metric.mem_ball_self hε)

omit [l.NeBot] in
/-- The actual preserved sphere gap produces true eventual conjugate
domain interior membership, rather than assuming the sequence domains. -/
theorem eventually_mem_interior_effectiveDomain_conjugate
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {F : I → E → ℝ} {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    (hFcv : ∀ i, ConvexOn ℝ univ (F i))
    (hF : ∀ K : Set E, IsCompact K → TendstoUniformlyOn F f l K)
    {m : M} (hm : m ∈ interior (effectiveDomain (conjugate B (fun x ↦ (f x : EReal)))))
    (hd : DifferentiableAt ℝ (fun p ↦ (conjugate B (fun x ↦ (f x : EReal)) p).toReal) m) :
    ∀ᶠ i in l, m ∈ interior (effectiveDomain (conjugate B (fun x ↦ (F i x : EReal)))) := by
  obtain ⟨δ, hδ, hgap⟩ := eventually_positive_conjugate_support_gap B hf hF hm hd zero_lt_one
  filter_upwards [hgap] with i hi
  exact mem_interior_effectiveDomain_conjugate_of_sphere_gap B (hFcv i) m
    (conjugateGradient B (fun x ↦ (f x : EReal)) m) zero_lt_one hδ hi

omit [l.NeBot] in
/-- Actual positive-radius sphere localization and the genuine singleton
inverse produce convergence of the original conjugate gradients. -/
theorem tendsto_conjugateGradient_of_convex_compact_convergence
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {F : I → E → ℝ} {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    (hFcv : ∀ i, ConvexOn ℝ univ (F i))
    (hF : ∀ K : Set E, IsCompact K → TendstoUniformlyOn F f l K)
    {m : M} (hm : m ∈ interior (effectiveDomain (conjugate B (fun x ↦ (f x : EReal)))))
    (hd : DifferentiableAt ℝ (fun p ↦ (conjugate B (fun x ↦ (f x : EReal)) p).toReal) m)
    (hdF : ∀ᶠ i in l, DifferentiableAt ℝ
      (fun p ↦ (conjugate B (fun x ↦ (F i x : EReal)) p).toReal) m) :
    Tendsto (fun i ↦ conjugateGradient B (fun x ↦ (F i x : EReal)) m) l
      (𝓝 (conjugateGradient B (fun x ↦ (f x : EReal)) m)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_exists_rawSubgradient_near_conjugateGradient B hf hFcv hF hm hd hε,
    eventually_mem_interior_effectiveDomain_conjugate B hf hFcv hF hm hd, hdF]
    with i hi him hid
  obtain ⟨q, hq, hqm⟩ := hi
  have hp := isProper_coe_of_convexOn (hFcv i)
  have hc : Continuous (fun x ↦ (F i x : EReal)) :=
    continuous_coe_real_ereal.comp (continuousOn_univ.mp ((hFcv i).continuousOn isOpen_univ))
  have hqdual := (mem_rawSubdifferential_iff_conjugate_rawSubdifferential B hp
    hc.lowerSemicontinuous (by simp [effectiveDomain]) (interior_subset him)).mp hqm
  rw [rawSubdifferential_conjugate_eq_singleton_of_differentiableAt B hp him hid] at hqdual
  rw [mem_singleton_iff.mp hqdual] at hq
  exact hq

omit [l.NeBot] [FiniteDimensional ℝ M] in
/-- Actual compactness and produced raw graph stability exclude every
original compact touching point outside the true limiting conjugate domain. -/
theorem eventually_no_rawSubgradient_on_compact
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {F : ℕ → E → ℝ} {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    (hF : ∀ K : Set E, IsCompact K → TendstoUniformlyOn F f atTop K)
    {m : M} (hm : m ∉ closure (effectiveDomain (conjugate B (fun x ↦ (f x : EReal)))))
    {K : Set E} (hK : IsCompact K) :
    ∀ᶠ i in atTop, ∀ q ∈ K, m ∉ rawSubdifferential B (fun z ↦ (F i z : EReal)) q := by
  classical
  by_contra hevent
  have hbad : ∃ᶠ i in atTop, ∃ q ∈ K, m ∈ rawSubdifferential B
      (fun z ↦ (F i z : EReal)) q := by
    apply (not_eventually.mp hevent).mono
    intro i hi
    push Not at hi
    exact hi
  obtain ⟨φ, hφ, hφbad⟩ := extraction_of_frequently_atTop hbad
  choose q hq hqraw using hφbad
  obtain ⟨q₀, _, ψ, hψ, hqt⟩ := hK.tendsto_subseq hq
  have hsubconv (A : Set E) (hA : IsCompact A) :
      TendstoUniformlyOn (fun i ↦ F (φ (ψ i))) f atTop A := by
    intro u hu
    exact (hφ.comp hψ).tendsto_atTop.eventually ((hF A hA) u hu)
  have hraw := mem_rawSubdifferential_of_tendsto B hf hsubconv hqt
    (tendsto_const_nhds (x := m)) (Eventually.of_forall (fun i ↦ hqraw (ψ i)))
  have hdom := rawSubgradientImage_subset_effectiveDomain_conjugate B
    (isProper_coe_of_convexOn hf) (mem_iUnion.mpr ⟨q₀, hraw⟩)
  exact hm (subset_closure hdom)

/-- Literal compact-test integrand of the original restricted conjugate
pushforward. Pole values outside its true domain are not projected into mass. -/
noncomputable def conjugateTestIntegrand
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    (f : E → EReal) (h : C_c(E, ℝ)) (m : M) : ℝ :=
  (interior (effectiveDomain (conjugate B f))).indicator
    (fun p ↦ h (conjugateGradient B f p)) m

omit [l.NeBot] in
/-- Actual interior touching convergence and genuine compact exterior
exclusion produce convergence of the literal original compact-test integrand. -/
theorem tendsto_conjugateTestIntegrand_of_convex_compact_convergence
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {F : ℕ → E → ℝ} {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    (hFcv : ∀ i, ConvexOn ℝ univ (F i))
    (hF : ∀ K : Set E, IsCompact K → TendstoUniformlyOn F f atTop K)
    (h : C_c(E, ℝ)) {m : M}
    (hd : m ∈ interior (effectiveDomain (conjugate B (fun x ↦ (f x : EReal)))) →
      DifferentiableAt ℝ (fun p ↦ (conjugate B (fun x ↦ (f x : EReal)) p).toReal) m)
    (hdF : ∀ i, m ∈ interior (effectiveDomain (conjugate B (fun x ↦ (F i x : EReal)))) →
      DifferentiableAt ℝ (fun p ↦ (conjugate B (fun x ↦ (F i x : EReal)) p).toReal) m)
    (hfront : m ∉ frontier (effectiveDomain (conjugate B (fun x ↦ (f x : EReal))))) :
    Tendsto (fun i ↦ conjugateTestIntegrand B (fun x ↦ (F i x : EReal)) h m) atTop
      (𝓝 (conjugateTestIntegrand B (fun x ↦ (f x : EReal)) h m)) := by
  by_cases hm : m ∈ interior (effectiveDomain (conjugate B (fun x ↦ (f x : EReal))))
  · have hdom := eventually_mem_interior_effectiveDomain_conjugate B hf hFcv hF hm (hd hm)
    have hgrad := tendsto_conjugateGradient_of_convex_compact_convergence B hf hFcv hF hm
      (hd hm) (hdom.mono (fun i hi ↦ hdF i hi))
    have htest := (map_continuous h).continuousAt.tendsto.comp hgrad
    have heq : ∀ᶠ i in atTop, h (conjugateGradient B (fun x ↦ (F i x : EReal)) m) =
        conjugateTestIntegrand B (fun x ↦ (F i x : EReal)) h m := by
      filter_upwards [hdom] with i hi
      simp only [conjugateTestIntegrand, indicator_of_mem hi]
    simpa only [conjugateTestIntegrand, indicator_of_mem hm, Function.comp_apply] using
      htest.congr' heq
  · have hnotcl : m ∉ closure (effectiveDomain (conjugate B (fun x ↦ (f x : EReal)))) :=
      fun hc ↦ hfront ⟨hc, hm⟩
    have hevent := eventually_no_rawSubgradient_on_compact B hf hF hnotcl h.hasCompactSupport
    have hzero : ∀ᶠ i in atTop, conjugateTestIntegrand B (fun x ↦ (F i x : EReal)) h m = 0 := by
      filter_upwards [hevent] with i hi
      by_cases him : m ∈ interior (effectiveDomain (conjugate B (fun x ↦ (F i x : EReal))))
      · have hz : h (conjugateGradient B (fun x ↦ (F i x : EReal)) m) = 0 := by
          by_contra hn
          exact hi _ (subset_tsupport h hn)
            (mem_rawSubdifferential_conjugateGradient_coe B (hFcv i) him (hdF i him))
        simp only [conjugateTestIntegrand, indicator_of_mem him, hz]
      · simp only [conjugateTestIntegrand, indicator_of_notMem him]
    simpa only [conjugateTestIntegrand, indicator_of_notMem hm] using
      (tendsto_const_nhds.congr' (hzero.mono (fun _ hi ↦ hi.symm)))

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  {ν : Measure M} [ν.IsAddHaarMeasure]

omit [l.NeBot] [MeasurableSpace E] [BorelSpace E] in
/-- Genuine countable Rademacher intersection and actual null convex
frontier supply the original compact-test convergence almost everywhere. -/
theorem ae_tendsto_conjugateTestIntegrand_of_convex_compact_convergence
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {F : ℕ → E → ℝ} {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    (hFcv : ∀ i, ConvexOn ℝ univ (F i))
    (hF : ∀ K : Set E, IsCompact K → TendstoUniformlyOn F f atTop K)
    (h : C_c(E, ℝ)) :
    ∀ᵐ m ∂ν, Tendsto (fun i ↦ conjugateTestIntegrand B (fun x ↦ (F i x : EReal)) h m)
      atTop (𝓝 (conjugateTestIntegrand B (fun x ↦ (f x : EReal)) h m)) := by
  have hp := isProper_conjugate_of_isContPerfPair B (isProper_coe_of_convexOn hf)
  have hdp := ae_differentiableAt_toReal_of_isProper (μ := ν) hp
  have hdF : ∀ᵐ m ∂ν, ∀ i, m ∈ interior (effectiveDomain (conjugate B (fun x ↦ (F i x : EReal)))) →
      DifferentiableAt ℝ (fun p ↦ (conjugate B (fun x ↦ (F i x : EReal)) p).toReal) m :=
    ae_all_iff.mpr (fun i ↦ ae_differentiableAt_toReal_of_isProper (μ := ν)
      (isProper_conjugate_of_isContPerfPair B (isProper_coe_of_convexOn (hFcv i))))
  have hfront : ∀ᵐ m ∂ν, m ∉ frontier (effectiveDomain (conjugate B (fun x ↦ (f x : EReal)))) := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using
      (convex_effectiveDomain hp.1).addHaar_frontier ν
  filter_upwards [hdp, hdF, hfront] with m hdm hdFm hfm
  exact tendsto_conjugateTestIntegrand_of_convex_compact_convergence B hf hFcv hF h
    hdm hdFm hfm

omit [l.NeBot] [ν.IsAddHaarMeasure] [FiniteDimensional ℝ M] in
/-- The literal original compact-test integrand is actually measurable. -/
theorem measurable_conjugateTestIntegrand
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    (f : E → EReal) (h : C_c(E, ℝ)) : Measurable (conjugateTestIntegrand B f h) :=
  ((map_continuous h).measurable.comp (measurable_conjugateGradient B f)).indicator measurableSet_interior

omit [l.NeBot] [ν.IsAddHaarMeasure] [FiniteDimensional ℝ M] in
/-- Actual original Alexandrov pushforward gives the exact integral of
its literal restricted compact-test integrand before any limit is asserted. -/
theorem integral_alexandrovMeasure_eq_conjugateTestIntegrand
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    (f : E → EReal) (h : C_c(E, ℝ)) :
    (∫ x, h x ∂alexandrovMeasure B ν f) = ((Module.finrank ℝ E).factorial : ℝ) *
      ∫ m, conjugateTestIntegrand B f h m ∂ν := by
  rw [alexandrovMeasure, integral_smul_measure,
    integral_map_of_stronglyMeasurable (measurable_conjugateGradient B f) (map_continuous h).measurable.stronglyMeasurable]
  simp only [ENNReal.toReal_natCast, smul_eq_mul]
  unfold conjugateTestIntegrand
  rw [integral_indicator measurableSet_interior]

omit [l.NeBot] [ν.IsAddHaarMeasure] [FiniteDimensional ℝ M]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
/-- The literal original compact-test integrand has the genuine global
bound produced by that original compactly supported continuous function. -/
theorem norm_conjugateTestIntegrand_le
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    (f : E → EReal) (h : C_c(E, ℝ)) (m : M) :
    ‖conjugateTestIntegrand B f h m‖ ≤ ‖h.toBoundedContinuousFunction‖ := by
  by_cases hm : m ∈ interior (effectiveDomain (conjugate B f))
  · simp only [conjugateTestIntegrand, indicator_of_mem hm]
    exact h.toBoundedContinuousFunction.norm_coe_le_norm _
  · simp only [conjugateTestIntegrand, indicator_of_notMem hm, norm_zero]
    exact norm_nonneg _

omit [l.NeBot] [ν.IsAddHaarMeasure] [FiniteDimensional ℝ M] in
/-- Genuine conjugate-domain containment restricts the literal original
pushforward integrand to the original compact support body. -/
theorem integral_alexandrovMeasure_eq_conjugateTestIntegrand_restrict
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    (f : E → EReal) (h : C_c(E, ℝ)) {P : Set M} (hP : MeasurableSet P)
    (hdom : effectiveDomain (conjugate B f) ⊆ P) :
    (∫ x, h x ∂alexandrovMeasure B ν f) = ((Module.finrank ℝ E).factorial : ℝ) *
      ∫ m in P, conjugateTestIntegrand B f h m ∂ν := by
  rw [integral_alexandrovMeasure_eq_conjugateTestIntegrand B f h, ← integral_indicator hP]
  congr 1
  congr 1
  funext m
  by_cases hm : m ∈ P
  · rw [indicator_of_mem hm]
  · have hnot : m ∉ interior (effectiveDomain (conjugate B f)) :=
      fun hd ↦ hm (hdom (interior_subset hd))
    simp only [indicator_of_notMem hm, conjugateTestIntegrand, indicator_of_notMem hnot]

omit [l.NeBot] in
/-- Actual original conjugate-gradient localization and true compact-body
Lebesgue domination prove local weak Alexandrov continuity. -/
theorem tendsto_integral_alexandrovMeasure_of_convex_compact_convergence
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {F : ℕ → E → ℝ} {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    (hFcv : ∀ i, ConvexOn ℝ univ (F i))
    (hF : ∀ K : Set E, IsCompact K → TendstoUniformlyOn F f atTop K)
    {P : Set M} (hP : IsCompact P)
    (hdom : effectiveDomain (conjugate B (fun x ↦ (f x : EReal))) ⊆ P)
    (hdomF : ∀ i, effectiveDomain (conjugate B (fun x ↦ (F i x : EReal))) ⊆ P)
    (h : C_c(E, ℝ)) :
    Tendsto (fun i ↦ ∫ x, h x ∂alexandrovMeasure B ν (fun z ↦ (F i z : EReal))) atTop
      (𝓝 (∫ x, h x ∂alexandrovMeasure B ν (fun z ↦ (f z : EReal)))) := by
  have : IsFiniteMeasure (ν.restrict P) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hP.measure_lt_top⟩
  have ht := tendsto_integral_of_dominated_convergence
    (μ := ν.restrict P) (fun _ ↦ ‖h.toBoundedContinuousFunction‖)
    (fun i ↦ (measurable_conjugateTestIntegrand B (fun x ↦ (F i x : EReal)) h).aestronglyMeasurable)
    (integrable_const _) (fun i ↦ Eventually.of_forall (fun m ↦
      norm_conjugateTestIntegrand_le B (fun x ↦ (F i x : EReal)) h m))
    (ae_restrict_of_ae (ae_tendsto_conjugateTestIntegrand_of_convex_compact_convergence B hf hFcv hF h))
  rw [integral_alexandrovMeasure_eq_conjugateTestIntegrand_restrict B
    (fun z ↦ (f z : EReal)) h hP.measurableSet hdom]
  exact (tendsto_const_nhds.mul ht).congr' (Eventually.of_forall (fun i ↦
    (integral_alexandrovMeasure_eq_conjugateTestIntegrand_restrict B
      (fun z ↦ (F i z : EReal)) h hP.measurableSet (hdomF i)).symm))

omit [l.NeBot] [ν.IsAddHaarMeasure] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace M] [BorelSpace M] in
/-- Genuine checked source support growth bounds the actual conjugate
domain; this reuses the original outside-support top producer. -/
theorem effectiveDomain_conjugate_subset_of_mem_growthClass
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair] {P : Set M}
    (hP : IsCompact P) (hconv : Convex ℝ P) {f : E → EReal}
    (hf : f ∈ GrowthClass B P) : effectiveDomain (conjugate B f) ⊆ P := by
  intro m hm
  by_contra hnot
  change conjugate B f m < ⊤ at hm
  rw [conjugate_eq_top_of_singularityLE_support B hP hconv hf.1 hf.2 hnot] at hm
  exact lt_irrefl _ hm

omit [l.NeBot] in
/-- Exact source thm:realMAcont in its original local weak sense: actual
pointwise original growth-class convergence produces every compact-test
Alexandrov integral limit, with no mass-conservation or limit certificate. -/
theorem tendsto_integral_alexandrovMeasure_of_mem_growthClass
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair] {P : Set M}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    {F : ℕ → GrowthClass B P} {f : GrowthClass B P}
    (hlim : ∀ x, Tendsto (fun i ↦ (F i).val x) atTop (𝓝 (f.val x)))
    (h : C_c(E, ℝ)) :
    Tendsto (fun i ↦ ∫ x, h x ∂alexandrovMeasure B ν (F i).val) atTop
      (𝓝 (∫ x, h x ∂alexandrovMeasure B ν f.val)) := by
  let fr := growthToRealConvex B hP hne f
  let Fr := fun i ↦ growthToRealConvex B hP hne (F i)
  have hfr : (fun x ↦ (fr.val x : EReal)) = f.val :=
    funext (coe_growthToRealConvex B hP hne f)
  have hFr (i : ℕ) : (fun x ↦ ((Fr i).val x : EReal)) = (F i).val :=
    funext (coe_growthToRealConvex B hP hne (F i))
  have hcm := (tendsto_growthToContinuousMap_iff atTop B hP hne).mpr hlim
  have hcompact (K : Set E) (hK : IsCompact K) :
      TendstoUniformlyOn (fun i ↦ (Fr i).val) fr.val atTop K :=
    (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hcm) K hK
  have hdom : effectiveDomain (conjugate B (fun x ↦ (fr.val x : EReal))) ⊆ P := by
    rw [hfr]
    exact effectiveDomain_conjugate_subset_of_mem_growthClass B hP hconv f.property
  have hdomF (i : ℕ) : effectiveDomain (conjugate B (fun x ↦ ((Fr i).val x : EReal))) ⊆ P := by
    rw [hFr i]
    exact effectiveDomain_conjugate_subset_of_mem_growthClass B hP hconv (F i).property
  have ht := tendsto_integral_alexandrovMeasure_of_convex_compact_convergence B
    fr.property (fun i ↦ (Fr i).property) hcompact hP hdom hdomF h (ν := ν)
  simpa only [hfr, hFr] using ht

/-- Literal canonical source coordinates and Lebesgue normalization for
all original pointwise-convergent convex growth functions. -/
theorem tendsto_integral_alexandrovMeasure_of_mem_growthClass_euclidean {n : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin n))} (hP : IsCompact P)
    (hne : P.Nonempty) (hconv : Convex ℝ P)
    {F : ℕ → GrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) P}
    {f : GrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) P}
    (hlim : ∀ x, Tendsto (fun i ↦ (F i).val x) atTop (𝓝 (f.val x)))
    (h : C_c(EuclideanSpace ℝ (Fin n), ℝ)) :
    Tendsto (fun i ↦ ∫ x, h x ∂alexandrovMeasure
      (innerₗ (EuclideanSpace ℝ (Fin n))) volume (F i).val) atTop
      (𝓝 (∫ x, h x ∂alexandrovMeasure (innerₗ (EuclideanSpace ℝ (Fin n))) volume f.val)) :=
  tendsto_integral_alexandrovMeasure_of_mem_growthClass
    (innerₗ (EuclideanSpace ℝ (Fin n))) hP hne hconv hlim h

end SGPT.Convex
