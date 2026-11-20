import SGPT.Toric.Toric5Multiplier
import SGPT.Toric.BigToricNewtonBody
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The local `L²` estimates of Yao's theorem

Source `chapter_toric_ample.tex`, proof of `thm:Yao` (and its use for `L^k`, `kφ` in the proof
of `cor:DXmaintoric`).  For a toric potential `φ ∈ PSH_tor(X, θ)`, `θ = c_1(O(D), h)`, and
`m ∈ M ∩ kP_D`, the coefficient of `χ^m ∈ H⁰(X, O(kD))` in the frame `e_v^k` on the vertex chart
`U_v ≅ ℂ^n` is the monomial `χ^{m - k m_v}`; on the torus its weighted density is
`exp(⟨m, ν⟩ - k F_φ(ν) + k ψ_v)`, `ν = Trop(z) = ∑_j log |z_j|² u_j(v)`
(`BigToricMetric.multiplierDensity_toricMonomial`).

* **Upper bound** (`thm:Yao` (1)): by Fenchel--Young, `F_φ(ν) ≥ ⟨x₀, ν⟩ - G_φ(x₀)` for every
  `x₀` with `G_φ(x₀) < ∞`, so the density is at most a constant times
  `∏_j |z_j|^{2⟨m - k x₀, u_j(v)⟩}`, which is locally integrable as soon as all exponents
  `⟨m - k x₀, u_j(v)⟩` are `> -1` (`multiplierIntegrableAt_toricMonomial_of_exponent`).  For
  `m ∈ kΔ(θ, φ)` such an `x₀` exists, `x₀` being any point of `{G_φ < ∞}` close to `m / k`.
  This replaces the source's reduction to `P_θ[φ]` (which uses `prop:PandPI`) by a direct
  estimate.
* **Lower bound** (`thm:Yao` (2)): `F_φ ≤ Supp_Δ + F_φ(0)`, so the density is at least a
  constant times `exp(H(ν))`, `H(ν) = ⟨m, ν⟩ - k Supp_Δ(ν)`; on the polydiscs
  `B_K = {|z_j - e^{-c_j K/2}| < e^{-c_j K/2}/4}`, `ν` stays at bounded distance from `-K u`,
  `u = ∑ c_j u_j(v)`, and `vol B_K = (π/16)^n e^{-K ∑ c_j}`, so the integral over `B_K` is
  `≳ e^{K (H(-u) - ∑ c_j)}`; infinitely many disjoint such polydiscs accumulate at `0`
  (`not_multiplierIntegrableAt_toricMonomial`).  This is the source's tube estimate.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology ContDiff BigOperators Manifold ENNReal

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-! ### Integrability of monomial weights -/

/-- `|w|^{2e}` is integrable on discs of `ℂ` for `e > -1`. -/
theorem integrable_indicator_ball_rpow {e : ℝ} (he : -1 < e) (R : ℝ) :
    Integrable ((Metric.ball (0 : ℂ) R).indicator fun w : ℂ => ‖w‖ ^ (2 * e)) := by
  rw [integrable_indicator_iff measurableSet_ball]
  have hd : 1 ≤ Module.finrank ℝ ℂ := by rw [Complex.finrank_real_complex]; norm_num
  have hα : -(2 * e) < (Module.finrank ℝ ℂ : ℝ) := by
    rw [Complex.finrank_real_complex]; push_cast; linarith
  refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := -(2 * e)) hd hα ?_
    (measurable_norm.pow_const _).aestronglyMeasurable
  refine Filter.Eventually.of_forall fun w => ?_
  rw [neg_neg, one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg w) _)]

/-- The product weight `∏_j |z_j|^{2 e_j}` on a polydisc of `ℂ^n` is integrable for `e_j > -1`. -/
theorem integrable_prod_indicator_ball_rpow {e : Fin n → ℝ} (he : ∀ j, -1 < e j) (R : ℝ) :
    Integrable (fun z : ComplexModel n =>
      ∏ j, (Metric.ball (0 : ℂ) R).indicator (fun w : ℂ => ‖w‖ ^ (2 * e j)) (z j)) := by
  have := (integrable_complexModel_coordinates (n := n)
    (fun x => ∏ j, (Metric.ball (0 : ℂ) R).indicator (fun w : ℂ => ‖w‖ ^ (2 * e j)) (x j))).mpr
    (Integrable.fintype_prod (f := fun j => (Metric.ball (0 : ℂ) R).indicator
      (fun w : ℂ => ‖w‖ ^ (2 * e j))) fun j => integrable_indicator_ball_rpow (he j) R)
  exact this

namespace BigToricMetric

variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-! ### Legendre duality bounds -/

/-- The Legendre transform `G_φ` is finite on its effective domain. -/
theorem legendre_eq_coe_toReal {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    {x : EuclideanSpace ℝ (Fin n)} (hx : h.legendre u x < ⊤) :
    h.legendre u x = ((h.legendre u x).toReal : EReal) := by
  have hG := h.legendre_mem_closedProperOnBody (h.nonempty_toricDivisorPolytope_of_mem hu) hu
  exact (EReal.coe_toReal hx.ne (hG.1.2.2 x)).symm

/-- Fenchel--Young: `⟨ν, x⟩ - F_φ(ν) ≤ G_φ(x)`. -/
theorem inner_sub_realProfile_le {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    {x : EuclideanSpace ℝ (Fin n)} (hx : h.legendre u x < ⊤) (ν : EuclideanSpace ℝ (Fin n)) :
    inner ℝ ν x - h.realProfile u ν ≤ (h.legendre u x).toReal := by
  have h1 : ((inner ℝ ν x : ℝ) : EReal) - h.profile u ν ≤ h.legendre u x :=
    le_iSup (fun ν' => ((innerₗ (EuclideanSpace ℝ (Fin n)) ν' x : ℝ) : EReal) - h.profile u ν') ν
  rw [congrFun (h.realProfile_mem hu).2 ν, h.legendre_eq_coe_toReal hu hx, ← EReal.coe_sub] at h1
  exact EReal.coe_le_coe_iff.mp h1

/-! ### The upper estimate -/

/-- Source proof of `thm:Yao` (1), local form: if `x₀ ∈ {G_φ < ∞}` and all exponents
`⟨m - k x₀, u_j(v)⟩` are `> -1`, the coefficient `χ^{m - k m_v}` of `χ^m` in the vertex chart at
`v` is `e^{-kφ}`-square integrable near every point. -/
theorem multiplierIntegrableAt_toricMonomial_of_exponent {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) {k : ℕ} (hk : 0 < k) {m : Fin n → ℤ}
    (hm : m ∈ toricLatticePoints ((k : ℤ) • D)) (v : latticePolytopeVertices γ)
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : h.legendre u x₀ < ⊤)
    (hexp : ∀ j, -1 < latticeFunctional (polytopeToricRayGenerator γ hs v j)
      (latticeVector m - (k : ℝ) • x₀))
    (z₀ : ComplexModel n) :
    MultiplierIntegrableAt (chartFunction u (polytopeToricVertexChart γ hs v)) k
      (toricMonomial ((k : ℤ) • D) v m) z₀ volume := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  set R : ℝ := ‖z₀‖ + 1 with hR
  set e : Fin n → ℝ := fun j =>
    latticeFunctional (polytopeToricRayGenerator γ hs v j) (latticeVector m - (k : ℝ) • x₀)
  set G₀ : ℝ := (h.legendre u x₀).toReal
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ComplexModel n) R).exists_bound_of_continuousOn
    (h.smooth v).continuous.continuousOn
  set C₀ : ℝ := Real.exp (k * G₀ + k * B)
  have hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH u := ⟨_, hu.1⟩
  have hqpsh : QuasiPlurisubharmonicOn (chartFunction u (polytopeToricVertexChart γ hs v))
      (Metric.ball 0 R) := fun z _ =>
    IsQPSH.chartFunction hφ _ z (by rw [vertexChart_val, vertexChart_target]; exact mem_univ z)
  refine ⟨hkpos, Metric.ball 0 R, Metric.isOpen_ball, by simp [hR], ?_, ?_, ?_⟩
  · exact (differentiable_toricMonomial _ v m).differentiableOn
  · exact Pending.aemeasurable_multiplierDensity_restrict_of_quasiPlurisubharmonicOn
      Metric.isOpen_ball hqpsh hkpos.ne' (differentiable_toricMonomial _ v m).continuous.continuousOn
  -- the pointwise bound on the torus
  set W : ComplexModel n → ℝ := fun z =>
    C₀ * ∏ j, (Metric.ball (0 : ℂ) R).indicator (fun w : ℂ => ‖w‖ ^ (2 * e j)) (z j)
  have hbound : ∀ z ∈ Metric.ball (0 : ComplexModel n) R, z ∈ complexTorus n →
      multiplierDensity (chartFunction u (polytopeToricVertexChart γ hs v)) k
        (toricMonomial ((k : ℤ) • D) v m) z ≤ ENNReal.ofReal (W z) := by
    intro z hzR hz
    obtain ⟨a, rfl⟩ := exists_embedding_eq_of_mem_complexTorus (hs := hs) v hz
    rw [h.multiplierDensity_toricMonomial hu hm v a]
    apply ENNReal.ofReal_le_ofReal
    set z := originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)
    set ν := unitTorusLog a
    have hcoord : ∀ j, z j ∈ Metric.ball (0 : ℂ) R := fun j => by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt (PiLp.norm_apply_le z j) (by simpa using hzR)
    have hpow : ∀ j, ‖z j‖ ^ (2 * e j) =
        Real.exp (e j * latticeFunctional (originalPolytopeNativeBasis γ hs v j) ν) := by
      intro j
      have hpos : 0 < ‖z j‖ := norm_pos_iff.mpr (hz j)
      have hsq := norm_sq_vertexChart_embedding (hs := hs) v a j
      have hlog : Real.log ‖z j‖ = latticeFunctional (originalPolytopeNativeBasis γ hs v j) ν / 2 := by
        have := congrArg Real.log hsq
        rw [Real.log_pow, Real.log_exp] at this
        push_cast at this
        linarith
      rw [Real.rpow_def_of_pos hpos, hlog]
      ring_nf
    have hprod : ∏ j, (Metric.ball (0 : ℂ) R).indicator (fun w : ℂ => ‖w‖ ^ (2 * e j)) (z j) =
        Real.exp (inner ℝ (latticeVector m - (k : ℝ) • x₀) ν) := by
      rw [inner_eq_sum_basis hs v, Real.exp_sum]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [indicator_of_mem (hcoord j), hpow j, mul_comm]
    have hFY := h.inner_sub_realProfile_le hu hx₀ ν
    have hψ : h.weight v z ≤ B := by
      have := hB z (Metric.ball_subset_closedBall hzR)
      exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
    have hinner : inner ℝ (latticeVector m - (k : ℝ) • x₀) ν =
        latticeFunctional m ν - k * inner ℝ ν x₀ := by
      rw [inner_sub_left, inner_smul_left, inner_latticeVector, real_inner_comm]
      simp
    change Real.exp _ ≤ C₀ * ∏ j, _
    rw [hprod, hinner, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : (k : ℝ) * (inner ℝ ν x₀ - h.realProfile u ν) ≤ k * G₀ :=
      mul_le_mul_of_nonneg_left hFY hkpos.le
    have h2 : (k : ℝ) * h.weight v z ≤ k * B := mul_le_mul_of_nonneg_left hψ hkpos.le
    nlinarith
  have hint : Integrable W := (integrable_prod_indicator_ball_rpow
    (fun j => hexp j) R).const_mul C₀
  calc (∫⁻ z in Metric.ball 0 R, multiplierDensity (chartFunction u
          (polytopeToricVertexChart γ hs v)) k (toricMonomial ((k : ℤ) • D) v m) z)
      ≤ ∫⁻ z in Metric.ball 0 R, ENNReal.ofReal (W z) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_of_ae ae_mem_complexTorus,
          ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz hzR
        exact hbound z hzR hz
    _ ≤ ∫⁻ z, ENNReal.ofReal (W z) := setLIntegral_le_lintegral _ _
    _ < ⊤ := hint.lintegral_lt_top

/-! ### The support function of the Newton body -/

/-- The real support function `Supp_Δ` of the Newton body `Δ(θ, φ)`. -/
def newtonSupport (u : PolytopeToricVariety γ hs → EReal) (ν : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (h.newtonBody u) ν).toReal

theorem support_newtonBody_eq {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    (ν : EuclideanSpace ℝ (Fin n)) :
    support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (h.newtonBody u) ν =
      (h.newtonSupport u ν : EReal) := by
  obtain ⟨hne, hcpt, -, -⟩ := h.newtonBody_properties (h.nonempty_toricDivisorPolytope_of_mem hu) hu
  obtain ⟨r, hr⟩ := exists_real_support_value (innerₗ (EuclideanSpace ℝ (Fin n))) hcpt hne ν
  rw [newtonSupport, hr, EReal.toReal_coe]

theorem inner_le_newtonSupport {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ h.newtonBody u) (ν : EuclideanSpace ℝ (Fin n)) :
    inner ℝ ν x ≤ h.newtonSupport u ν := by
  have h1 : ((innerₗ (EuclideanSpace ℝ (Fin n))).flip x ν : EReal) ≤
      support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (h.newtonBody u) ν :=
    le_iSup (fun y : h.newtonBody u => (((innerₗ (EuclideanSpace ℝ (Fin n))).flip y ν : ℝ) : EReal))
      ⟨x, hx⟩
  rw [h.support_newtonBody_eq hu] at h1
  exact EReal.coe_le_coe_iff.mp h1

theorem newtonSupport_le_of_forall {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    {ν : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : ∀ x ∈ h.newtonBody u, inner ℝ ν x ≤ r) :
    h.newtonSupport u ν ≤ r := by
  have h1 : support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (h.newtonBody u) ν ≤ (r : EReal) :=
    iSup_le fun y => EReal.coe_le_coe_iff.mpr (hr y.1 y.2)
  rw [h.support_newtonBody_eq hu] at h1
  exact EReal.coe_le_coe_iff.mp h1

/-- `Supp_Δ(t ν) ≤ t Supp_Δ(ν)` for `t ≥ 0`. -/
theorem newtonSupport_smul_le {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    {t : ℝ} (ht : 0 ≤ t) (ν : EuclideanSpace ℝ (Fin n)) :
    h.newtonSupport u (t • ν) ≤ t * h.newtonSupport u ν :=
  h.newtonSupport_le_of_forall hu fun x hx => by
    rw [inner_smul_left]
    exact mul_le_mul_of_nonneg_left (h.inner_le_newtonSupport hu hx ν) ht

/-- `Supp_Δ` is Lipschitz with the radius of `Δ` as constant (one direction). -/
theorem exists_newtonSupport_le_add {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ ν ν' : EuclideanSpace ℝ (Fin n),
      h.newtonSupport u ν ≤ h.newtonSupport u ν' + ρ * ‖ν - ν'‖ := by
  obtain ⟨-, hcpt, -, -⟩ := h.newtonBody_properties (h.nonempty_toricDivisorPolytope_of_mem hu) hu
  obtain ⟨ρ, hρ⟩ := hcpt.isBounded.subset_closedBall 0
  refine ⟨max ρ 0, le_max_right _ _, fun ν ν' => h.newtonSupport_le_of_forall hu fun x hx => ?_⟩
  have hxρ : ‖x‖ ≤ max ρ 0 := (by simpa using hρ hx : ‖x‖ ≤ ρ).trans (le_max_left _ _)
  have h1 : inner ℝ ν x = inner ℝ ν' x + inner ℝ (ν - ν') x := by
    rw [inner_sub_left]; ring
  have h2 : inner ℝ (ν - ν') x ≤ max ρ 0 * ‖ν - ν'‖ :=
    (real_inner_le_norm _ _).trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hxρ (norm_nonneg _))
  linarith [h.inner_le_newtonSupport hu hx ν']

theorem newtonSupport_zero {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    h.newtonSupport u 0 = 0 := by
  obtain ⟨⟨x, hx⟩, -, -, -⟩ := h.newtonBody_properties (h.nonempty_toricDivisorPolytope_of_mem hu) hu
  apply le_antisymm
  · exact h.newtonSupport_le_of_forall hu fun y _ => by simp
  · simpa using h.inner_le_newtonSupport hu hx 0

/-- Source proof of `thm:Yao` (2): `F_φ ≤ Supp_Δ + F_φ(0)`. -/
theorem realProfile_le_newtonSupport {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    (ν : EuclideanSpace ℝ (Fin n)) :
    h.realProfile u ν ≤ h.newtonSupport u ν + h.realProfile u 0 := by
  have hP := h.nonempty_toricDivisorPolytope_of_mem hu
  have hconj := congrFun (h.conjugate_legendre hP hu) ν
  rw [congrFun (h.realProfile_mem hu).2 ν] at hconj
  have hle : conjugate (innerₗ (EuclideanSpace ℝ (Fin n))).flip (h.legendre u) ν ≤
      ((h.newtonSupport u ν + h.realProfile u 0 : ℝ) : EReal) := by
    refine iSup_le fun x => ?_
    by_cases hx : h.legendre u x < ⊤
    · rw [h.legendre_eq_coe_toReal hu hx, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      have hxΔ : x ∈ h.newtonBody u := by
        rw [h.newtonBody_eq_closure_effectiveDomain hP hu]
        exact subset_closure hx
      have h1 := h.inner_le_newtonSupport hu hxΔ ν
      have h2 := h.inner_sub_realProfile_le hu hx 0
      simp only [inner_zero_left, zero_sub] at h2
      change inner ℝ ν x - _ ≤ _
      linarith
    · rw [not_lt_top_iff.mp hx]
      simp
  rw [hconj] at hle
  exact EReal.coe_le_coe_iff.mp hle

end BigToricMetric

/-! ### Elementary estimates on small discs -/

/-- Points of the disc `|w - p| < p/4` (`p > 0`) have `3p/4 < |w| < 5p/4` and
`|log |w|² - log p²| < 1`. -/
theorem norm_bounds_of_mem_ball {p : ℝ} (hp : 0 < p) {w : ℂ}
    (hw : w ∈ Metric.ball (p : ℂ) (p / 4)) :
    3 / 4 * p < ‖w‖ ∧ ‖w‖ < 5 / 4 * p ∧ |Real.log (‖w‖ ^ 2) - Real.log (p ^ 2)| < 1 := by
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have h1 : ‖(p : ℂ)‖ = p := by rw [Complex.norm_real, Real.norm_of_nonneg hp.le]
  have hlow : 3 / 4 * p < ‖w‖ := by
    have := norm_sub_norm_le (p : ℂ) w
    rw [h1, norm_sub_rev] at this
    linarith
  have hup : ‖w‖ < 5 / 4 * p := by
    have := norm_le_insert' w (p : ℂ)
    rw [h1] at this
    linarith
  refine ⟨hlow, hup, ?_⟩
  have hwpos : 0 < ‖w‖ := by linarith
  have hratio : Real.log (‖w‖ ^ 2) - Real.log (p ^ 2) = Real.log ((‖w‖ / p) ^ 2) := by
    rw [div_pow, Real.log_div (by positivity) (by positivity)]
  rw [hratio, abs_lt]
  have hq1 : 9 / 16 < (‖w‖ / p) ^ 2 := by
    rw [div_pow, lt_div_iff₀ (by positivity)]; nlinarith
  have hq2 : (‖w‖ / p) ^ 2 < 25 / 16 := by
    rw [div_pow, div_lt_iff₀ (by positivity)]; nlinarith
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hepos : 0 < Real.exp (-1) := Real.exp_pos _
  have hem : Real.exp (-1) < 9 / 16 := by
    rw [Real.exp_neg]
    rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  constructor
  · rw [← Real.log_exp (-1)]
    exact Real.log_lt_log hepos (by linarith)
  · rw [← Real.log_exp 1]
    exact Real.log_lt_log (by positivity) (by linarith)

/-- The real vector `x` in the dual bases at `v`: `x = ∑_j ⟨b_j(v), x⟩ u_j(v)`. -/
theorem eq_sum_basis_smul_rayVector (v : latticePolytopeVertices γ)
    (x : EuclideanSpace ℝ (Fin n)) :
    x = ∑ j, latticeFunctional (originalPolytopeNativeBasis γ hs v j) x •
      latticeVector (polytopeToricRayGenerator γ hs v j) := by
  apply ext_inner_left ℝ
  intro m
  rw [inner_eq_sum_basis hs v m x, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_right, real_inner_comm, inner_latticeVector]

namespace BigToricMetric

variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-! ### The lower estimate -/

/-- Source proof of `thm:Yao` (2), local form at the torus-fixed point of a maximal cone: if
`c_j > 0` and `u = ∑_j c_j u_j(v)` satisfies `⟨m, -u⟩ - k Supp_Δ(-u) > ∑_j c_j`, then the
coefficient `χ^{m - k m_v}` of `χ^m` is not `e^{-kφ}`-square integrable near `z_v = 0`. -/
theorem not_multiplierIntegrableAt_toricMonomial {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) {k : ℕ} (hk : 0 < k) {m : Fin n → ℤ}
    (hm : m ∈ toricLatticePoints ((k : ℤ) • D)) (v : latticePolytopeVertices γ)
    (c : Fin n → ℝ) (hc : ∀ j, 0 < c j)
    (hH : ∑ j, c j < latticeFunctional m
        (-∑ j, c j • latticeVector (polytopeToricRayGenerator γ hs v j)) -
      k * h.newtonSupport u (-∑ j, c j • latticeVector (polytopeToricRayGenerator γ hs v j))) :
    ¬ MultiplierIntegrableAt (chartFunction u (polytopeToricVertexChart γ hs v)) k
      (toricMonomial ((k : ℤ) • D) v m) 0 volume := by
  rintro ⟨-, V, hV, h0V, -, -, hfin⟩
  set U : Fin n → EuclideanSpace ℝ (Fin n) := fun j =>
    latticeVector (polytopeToricRayGenerator γ hs v j)
  set w := ∑ j, c j • U j with hw
  set Hval := latticeFunctional m (-w) - k * h.newtonSupport u (-w) with hHval
  set dens := multiplierDensity (chartFunction u (polytopeToricVertexChart γ hs v)) k
    (toricMonomial ((k : ℤ) • D) v m)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hw0 : w = 0 := by simp [hw]
      have hH0 : Hval = 0 := by rw [hHval, hw0, neg_zero, h.newtonSupport_zero hu]; simp
      rw [hH0] at hH
      simp at hH
    · exact hn
  set j₀ : Fin n := ⟨0, hn⟩
  -- constants
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hV 0 h0V
  obtain ⟨Bψ, hBψ⟩ := (isCompact_closedBall (0 : ComplexModel n) 1).exists_bound_of_continuousOn
    (h.smooth v).continuous.continuousOn
  obtain ⟨ρ, hρ0, hρ⟩ := h.exists_newtonSupport_le_add hu
  set F₀ := h.realProfile u 0
  set L := ‖latticeVector m‖ + k * ρ
  set Ru := ∑ j, ‖U j‖
  set C₁ := k * F₀ + k * Bψ + L * Ru
  obtain ⟨cmin, hcmin0, hcmin⟩ : ∃ cmin, 0 < cmin ∧ ∀ j, cmin ≤ c j := by
    obtain ⟨j, -, hj⟩ := Finset.exists_min_image Finset.univ c ⟨j₀, Finset.mem_univ _⟩
    exact ⟨c j, hc j, fun j' => hj j' (Finset.mem_univ _)⟩
  -- the polydiscs
  set p : ℕ → Fin n → ℝ := fun K j => Real.exp (-(c j * K / 2)) with hp
  have hppos : ∀ K j, 0 < p K j := fun K j => Real.exp_pos _
  set Bs : ℕ → Set (ComplexModel n) := fun K =>
    {z | ∀ j, z j ∈ Metric.ball ((p K j : ℝ) : ℂ) (p K j / 4)} with hBs
  have hBpre : ∀ K, Bs K = (fun z : ComplexModel n => (fun i => z i)) ⁻¹'
      (Set.univ.pi fun j => Metric.ball ((p K j : ℝ) : ℂ) (p K j / 4)) := by
    intro K; ext z; simp [hBs]
  have hBopen : ∀ K, IsOpen (Bs K) := by
    intro K
    rw [hBpre]
    exact (isOpen_set_pi finite_univ fun j _ => Metric.isOpen_ball).preimage
      (continuous_pi fun i => PiLp.continuous_apply 2 _ i)
  have hBvol : ∀ K, volume (Bs K) =
      ∏ j, ENNReal.ofReal (p K j / 4) ^ 2 * (NNReal.pi : ℝ≥0∞) := by
    intro K
    rw [hBpre, (volume_preserving_complexModel_coordinates n).measure_preimage
      (MeasurableSet.univ_pi fun j => measurableSet_ball).nullMeasurableSet, Measure.pi_pi]
    exact Finset.prod_congr rfl fun j _ => Complex.volume_ball _ _
  -- points of the polydiscs
  have hlogp : ∀ K j, Real.log (p K j ^ 2) = -(c j * K) := by
    intro K j
    rw [Real.log_pow, Real.log_exp]; push_cast; ring
  have hmemB : ∀ K, ∀ z ∈ Bs K, z ∈ complexTorus n ∧ (∀ j, ‖z j‖ < 5 / 4 * p K j) ∧
      (∀ j, 3 / 4 * p K j < ‖z j‖) ∧ ∀ j, |Real.log (‖z j‖ ^ 2) + c j * K| < 1 := by
    intro K z hz
    have hb := fun j => norm_bounds_of_mem_ball (hppos K j) (hz j)
    refine ⟨fun j => ?_, fun j => (hb j).2.1, fun j => (hb j).1, fun j => ?_⟩
    · have := (hb j).1
      have : 0 < ‖z j‖ := lt_trans (by have := hppos K j; positivity) this
      exact norm_pos_iff.mp this
    · have := (hb j).2.2
      rwa [hlogp, sub_neg_eq_add] at this
  -- eventually the polydiscs lie in `V ∩ closedBall 0 1`
  set r := min ε 1
  have hr : 0 < r := lt_min hε one_pos
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℕ, ∀ K ≥ K₁, (n : ℝ) * (25 / 16) * Real.exp (-(cmin * K)) < r ^ 2 := by
    have ht : Tendsto (fun K : ℕ => (n : ℝ) * (25 / 16) * Real.exp (-(cmin * K))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun K : ℕ => cmin * (K : ℝ)) atTop atTop :=
        Filter.Tendsto.const_mul_atTop hcmin0 tendsto_natCast_atTop_atTop
      have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
      simpa using h2.const_mul ((n : ℝ) * (25 / 16))
    exact eventually_atTop.mp ((tendsto_order.1 ht).2 _ (by positivity))
  have hBsub : ∀ K ≥ K₁, Bs K ⊆ Metric.ball 0 r := by
    intro K hK z hz
    obtain ⟨-, hup, -, -⟩ := hmemB K z hz
    rw [Metric.mem_ball, dist_zero_right, EuclideanSpace.norm_eq,
      Real.sqrt_lt' hr]
    have hj : ∀ j, ‖z j‖ ^ 2 ≤ 25 / 16 * Real.exp (-(cmin * K)) := by
      intro j
      have h1 : ‖z j‖ ^ 2 ≤ (5 / 4 * p K j) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hup j).le 2
      have h2 : p K j ^ 2 ≤ Real.exp (-(cmin * K)) := by
        rw [hp, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have : cmin * K ≤ c j * K := mul_le_mul_of_nonneg_right (hcmin j) (Nat.cast_nonneg K)
        push_cast; linarith
      nlinarith
    calc ∑ j, ‖z j‖ ^ 2 ≤ ∑ _j : Fin n, 25 / 16 * Real.exp (-(cmin * K)) :=
          Finset.sum_le_sum fun j _ => hj j
      _ = (n : ℝ) * (25 / 16) * Real.exp (-(cmin * K)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ < r ^ 2 := hK₁ K hK
  -- the density on a polydisc
  have hdens : ∀ K ≥ K₁, ∀ z ∈ Bs K, ENNReal.ofReal (Real.exp (K * Hval - C₁)) ≤ dens z := by
    intro K hK z hz
    obtain ⟨hzT, -, -, hlog⟩ := hmemB K z hz
    have hz1 : z ∈ Metric.closedBall (0 : ComplexModel n) 1 :=
      Metric.ball_subset_closedBall (Metric.ball_subset_ball (min_le_right _ _) (hBsub K hK hz))
    obtain ⟨a, rfl⟩ := exists_embedding_eq_of_mem_complexTorus (hs := hs) v hzT
    change ENNReal.ofReal _ ≤ multiplierDensity _ _ _ _
    rw [h.multiplierDensity_toricMonomial hu hm v a]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    set z := originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)
    set ν := unitTorusLog a
    -- `ν` is close to `K • (-w)`
    have hs_j : ∀ j, latticeFunctional (originalPolytopeNativeBasis γ hs v j) ν =
        Real.log (‖z j‖ ^ 2) := by
      intro j
      rw [norm_sq_vertexChart_embedding (hs := hs) v a j, Real.log_exp]
    have hdist : ‖ν - (K : ℝ) • (-w)‖ ≤ Ru := by
      have hexp : ν - (K : ℝ) • (-w) =
          ∑ j, (Real.log (‖z j‖ ^ 2) + c j * K) • U j := by
        conv_lhs => rw [eq_sum_basis_smul_rayVector (hs := hs) v ν]
        simp only [hw, smul_neg, sub_neg_eq_add, Finset.smul_sum, smul_smul, hs_j,
          ← Finset.sum_add_distrib, add_smul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_comm (K : ℝ) (c j)]
      rw [hexp]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (hlog j).le
    have h1 := h.realProfile_le_newtonSupport hu ν
    have h2 := hρ ν ((K : ℝ) • (-w))
    have h3 := h.newtonSupport_smul_le hu (Nat.cast_nonneg K) (-w)
    have h4 : latticeFunctional m ((K : ℝ) • (-w)) - ‖latticeVector m‖ * ‖ν - (K : ℝ) • (-w)‖ ≤
        latticeFunctional m ν := by
      have := real_inner_le_norm (latticeVector m) ((K : ℝ) • (-w) - ν)
      rw [inner_latticeVector, map_sub, norm_sub_rev] at this
      linarith
    have h5 : -Bψ ≤ h.weight v z := by
      have := hBψ z hz1
      exact neg_le_of_abs_le (by simpa [Real.norm_eq_abs] using this)
    have h6 : latticeFunctional m ((K : ℝ) • (-w)) = K * latticeFunctional m (-w) := by
      rw [map_smul, smul_eq_mul]
    have hLnn : 0 ≤ ‖latticeVector m‖ := norm_nonneg _
    have hdist' : ‖latticeVector m‖ * ‖ν - (K : ℝ) • (-w)‖ ≤ ‖latticeVector m‖ * Ru :=
      mul_le_mul_of_nonneg_left hdist hLnn
    have hρd : ρ * ‖ν - (K : ℝ) • (-w)‖ ≤ ρ * Ru := mul_le_mul_of_nonneg_left hdist hρ0
    have hk1 : (k : ℝ) * h.realProfile u ν ≤
        k * (h.newtonSupport u ((K : ℝ) • (-w)) + ρ * ‖ν - (K : ℝ) • (-w)‖ + F₀) := by
      apply mul_le_mul_of_nonneg_left _ hkpos.le
      linarith
    have hk2 : (k : ℝ) * h.newtonSupport u ((K : ℝ) • (-w)) ≤
        k * (K * h.newtonSupport u (-w)) := mul_le_mul_of_nonneg_left h3 hkpos.le
    have hk3 : (k : ℝ) * (-Bψ) ≤ k * h.weight v z := mul_le_mul_of_nonneg_left h5 hkpos.le
    have hk4 : (k : ℝ) * (ρ * ‖ν - (K : ℝ) • (-w)‖) ≤ k * (ρ * Ru) :=
      mul_le_mul_of_nonneg_left hρd hkpos.le
    simp only [hHval, C₁, L]
    nlinarith
  -- the integral over a polydisc
  set δ : ℝ≥0∞ := ENNReal.ofReal ((Real.pi / 16) ^ n * Real.exp (-C₁))
  have hδ : δ ≠ 0 := by
    simp only [δ, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact mul_pos (pow_pos (by positivity) n) (Real.exp_pos _)
  have hHpos : ∑ j, c j < Hval := hH
  have hint : ∀ K ≥ K₁, δ ≤ ∫⁻ z in Bs K, dens z := by
    intro K hK
    calc δ ≤ ENNReal.ofReal (Real.exp (K * Hval - C₁)) * volume (Bs K) := by
          rw [hBvol]
          have hprod : ∏ j, ENNReal.ofReal (p K j / 4) ^ 2 * (NNReal.pi : ℝ≥0∞) =
              ENNReal.ofReal ((Real.pi / 16) ^ n * Real.exp (-(K * ∑ j, c j))) := by
            have hterm : ∀ j, ENNReal.ofReal (p K j / 4) ^ 2 * (NNReal.pi : ℝ≥0∞) =
                ENNReal.ofReal (Real.pi / 16 * Real.exp (-(c j * K))) := by
              intro j
              rw [← ENNReal.ofReal_pow (by have := hppos K j; positivity),
                ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
                ← ENNReal.ofReal_mul (by positivity)]
              congr 1
              rw [hp, div_pow, ← Real.exp_nat_mul]
              push_cast
              ring_nf
            rw [Finset.prod_congr rfl fun j _ => hterm j,
              ← ENNReal.ofReal_prod_of_nonneg (fun j _ => by positivity),
              Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
              ← Real.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
            have hsum : ∑ x, -(c x * (K : ℝ)) = ∑ x, -((K : ℝ) * c x) :=
              Finset.sum_congr rfl fun j _ => by ring
            rw [hsum]
          rw [hprod, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
          apply ENNReal.ofReal_le_ofReal
          have hrhs : Real.exp (K * Hval - C₁) * ((Real.pi / 16) ^ n *
              Real.exp (-(K * ∑ j, c j))) =
              (Real.pi / 16) ^ n * Real.exp ((K * Hval - C₁) + -(K * ∑ j, c j)) := by
            rw [Real.exp_add]; ring
          rw [hrhs]
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by positivity) n)
          apply Real.exp_le_exp.mpr
          have : (K : ℝ) * ∑ j, c j ≤ K * Hval :=
            mul_le_mul_of_nonneg_left hHpos.le (Nat.cast_nonneg K)
          linarith
      _ = ∫⁻ z in Bs K, ENNReal.ofReal (Real.exp (K * Hval - C₁)) :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ z in Bs K, dens z := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem (hBopen K).measurableSet] with z hz
          exact hdens K hK z hz
  -- infinitely many disjoint polydiscs
  set N : ℕ := ⌈2 / c j₀⌉₊
  have hN : 2 ≤ c j₀ * N := by
    have := Nat.le_ceil (2 / c j₀)
    rw [div_le_iff₀' (hc j₀)] at this
    exact this
  set s : ℕ → Set (ComplexModel n) := fun q => Bs (K₁ + N * q)
  have hdisj : Pairwise (Function.onFun Disjoint s) := by
    rw [pairwise_disjoint_on]
    intro q q' hqq'
    rw [Set.disjoint_left]
    intro z hz hz'
    obtain ⟨-, -, hlow, -⟩ := hmemB _ z hz
    obtain ⟨-, hup, -, -⟩ := hmemB _ z hz'
    have h1 := hlow j₀
    have h2 := hup j₀
    have hle : p (K₁ + N * q') j₀ ≤ p (K₁ + N * q) j₀ * Real.exp (-1) := by
      rw [hp, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hq : ((K₁ + N * q : ℕ) : ℝ) + N ≤ ((K₁ + N * q' : ℕ) : ℝ) := by
        have : N * q + N ≤ N * q' := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hqq'
        exact_mod_cast (by omega : K₁ + N * q + N ≤ K₁ + N * q')
      have : c j₀ * (((K₁ + N * q : ℕ) : ℝ) + N) ≤ c j₀ * ((K₁ + N * q' : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hq (hc j₀).le
      nlinarith
    have he : Real.exp (-1) < 3 / 5 := by
      rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
      linarith [Real.add_one_le_exp 1]
    have hpq := hppos (K₁ + N * q) j₀
    nlinarith
  have htop : ∫⁻ z in V, dens z = ⊤ := by
    apply eq_top_iff.mpr
    calc (⊤ : ℝ≥0∞) = ∑' _q : ℕ, δ := (ENNReal.tsum_const_eq_top_of_ne_zero hδ).symm
      _ ≤ ∑' q, ∫⁻ z in s q, dens z :=
          ENNReal.tsum_le_tsum fun q => hint _ (by omega)
      _ = ∫⁻ z in ⋃ q, s q, dens z :=
          (lintegral_iUnion (fun q => (hBopen _).measurableSet) hdisj _).symm
      _ ≤ ∫⁻ z in V, dens z := by
          apply lintegral_mono_set
          refine iUnion_subset fun q => ?_
          exact (hBsub _ (by omega)).trans
            ((Metric.ball_subset_ball (min_le_left _ _)).trans hεV)
  exact absurd hfin (by rw [htop]; exact lt_irrefl _)

end BigToricMetric

end SGPT.Toric
