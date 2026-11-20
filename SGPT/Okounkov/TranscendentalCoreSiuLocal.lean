import SGPT.Okounkov.TranscendentalCoreAlgebra
import SGPT.Foundations.Analysis.Pending.DemaillyAnalyticType
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly
import SGPT.Foundations.Analysis.Pending.MeteredDivisorPositivity
import SGPT.Foundations.Analysis.Pending.AnalyticSingularities
import SGPT.Foundations.Analysis.PlurisubharmonicAE
import SGPT.Foundations.Analysis.LocalPshDiscControl
import SGPT.Foundations.Analysis.Pending.PolydiskPerronDataComparison

/-!
# Local tools for subtracting a smooth divisor from an analytic potential

Auxiliary for blueprint node `tok:siu-analytic`.

* `HasAnalyticSingularityTypeAt.comp_holomorphic`: analytic singularity types pull back along
  holomorphic maps of Euclidean domains.
* `ChartTypeOver`: the analytic singularity type in every chart over an open set, with the
  algebra (`add`, bounded perturbations) and the conversion to
  `HasManifoldAnalyticSingularityType`.
* `exists_bounded_remainder_of_bounds`: two-sided bounds `A - B ≤ v ≤ A + B` give a bounded real
  remainder `v = A + r`.
* `generatorLog_pow_mul`: `log ∑ |ℓ^a H_i|² = a log |ℓ|² + log ∑ |H_i|²`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalCore

open Set Filter Metric
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation

/-! ### Euclidean analytic types -/

section Euclid

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
  [NormedSpace ℂ E']

/-- Analytic singularity types pull back along holomorphic maps. -/
theorem HasAnalyticSingularityTypeAt.comp_holomorphic {u : E' → EReal} {G : E → E'} {z : E}
    (hu : HasAnalyticSingularityTypeAt u (G z))
    (hG : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ G w) :
    HasAnalyticSingularityTypeAt (fun w => u (G w)) z := by
  obtain ⟨c, N, f, hc, ⟨V, hV, hGzV, hf⟩, b, hb, heq⟩ := hu
  have hGc : ContinuousAt G z := hG.self_of_nhds.continuousAt
  have hS : {w | DifferentiableAt ℂ G w ∧ G w ∈ V} ∈ 𝓝 z :=
    hG.and (hGc.preimage_mem_nhds (hV.mem_nhds hGzV))
  refine ⟨c, N, fun i w => f i (G w), hc,
    ⟨interior {w | DifferentiableAt ℂ G w ∧ G w ∈ V}, isOpen_interior,
      mem_interior_iff_mem_nhds.mpr hS, fun i w hw => ?_⟩,
    fun w => b (G w), hb.comp_continuousAt hGc, heq.comp_tendsto hGc⟩
  have hw' := interior_subset hw
  exact (((hf i).differentiableAt (hV.mem_nhds hw'.2)).comp w hw'.1).differentiableWithinAt

/-- `c log ∑ |H_i|²` has analytic singularity type where the `H_i` are holomorphic. -/
theorem hasAnalyticSingularityTypeAt_generatorLog {N : ℕ} {H : Fin N → E → ℂ} {z : E}
    (hH : ∀ i, ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (H i) w) {c : ℚ} (hc : 0 < c) :
    HasAnalyticSingularityTypeAt (fun w => ((c : ℝ) : EReal) * generatorLog H w) z := by
  obtain ⟨U, hsub, hU, hzU⟩ := _root_.mem_nhds_iff.mp (eventually_all.mpr hH)
  refine ⟨c, N, H, by exact_mod_cast hc,
    ⟨U, hU, hzU, fun i w hw => (hsub hw i).differentiableWithinAt⟩, fun _ => 0,
    ⟨0, le_rfl, Eventually.of_forall fun _ => by simp⟩, Eventually.of_forall fun w => ?_⟩
  simp

end Euclid

/-! ### Extended-real remainders -/

/-- Two-sided bounds `A - B ≤ v ≤ A + B` (with `A ≠ ⊤`, `B ≥ 0`) give a real remainder `r`,
`|r| ≤ B`, with `v = A + r`. -/
theorem exists_remainder_of_bounds {A v : EReal} {B : ℝ} (hB : 0 ≤ B) (hA : A ≠ ⊤)
    (hlow : A + ((-B : ℝ) : EReal) ≤ v) (hup : v ≤ A + (B : EReal)) :
    ∃ r : ℝ, |r| ≤ B ∧ v = A + (r : EReal) := by
  induction A using EReal.rec with
  | bot =>
      refine ⟨0, by simpa using hB, ?_⟩
      rw [EReal.bot_add] at hup ⊢
      exact le_bot_iff.mp hup
  | top => exact absurd rfl hA
  | coe a =>
      induction v using EReal.rec with
      | bot =>
          rw [← EReal.coe_add] at hlow
          exact absurd hlow (not_le.mpr (EReal.bot_lt_coe _))
      | top =>
          rw [← EReal.coe_add] at hup
          exact absurd hup (not_le.mpr (EReal.coe_lt_top _))
      | coe w =>
          rw [← EReal.coe_add, EReal.coe_le_coe_iff] at hlow hup
          refine ⟨w - a, abs_le.mpr ⟨by linarith, by linarith⟩, ?_⟩
          rw [← EReal.coe_add, add_sub_cancel]


/-- `log ∑ |ℓ^a H_i|² = a log |ℓ|² + log ∑ |H_i|²`. -/
theorem generatorLog_pow_mul {X : Type*} {N : ℕ} (ℓ : X → ℂ) (a : ℕ) (H : Fin N → X → ℂ)
    (y : X) :
    generatorLog (fun i x => ℓ x ^ a * H i x) y =
      ((a : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (‖ℓ y‖ ^ 2)) + generatorLog H y := by
  rw [generatorLog_eq_log_sum, generatorLog_eq_log_sum]
  have h : ∑ j, ‖ℓ y ^ a * H j y‖ ^ 2 = (‖ℓ y‖ ^ 2) ^ a * ∑ j, ‖H j y‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [norm_mul, norm_pow]
    ring
  rw [h, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.log_mul_add, ENNReal.log_pow, EReal.coe_natCast]


/-! ### Extended-real identities for residuals -/

/-- `log ∑_{Fin 1} |g|² = log |g|²`. -/
theorem generatorLog_single {X : Type*} (g : X → ℂ) (y : X) :
    generatorLog (fun _ : Fin 1 => g) y = ENNReal.log (ENNReal.ofReal (‖g y‖ ^ 2)) := by
  rw [generatorLog_eq_log_sum, Fin.sum_univ_one]

theorem generatorLog_ne_top {X : Type*} {N : ℕ} (f : Fin N → X → ℂ) (y : X) :
    generatorLog f y ≠ ⊤ := by
  rw [generatorLog_eq_log_sum]
  exact fun h => ENNReal.ofReal_ne_top (ENNReal.log_eq_top_iff.mp h)

theorem ereal_coe_mul_ne_top {r : ℝ} (hr : 0 ≤ r) {G : EReal} (hG : G ≠ ⊤) :
    (r : EReal) * G ≠ ⊤ := by
  induction G using EReal.rec with
  | bot =>
      rcases hr.lt_or_eq with hr | rfl
      · rw [EReal.coe_mul_bot_of_pos hr]
        exact bot_ne_top
      · simp
  | top => exact absurd rfl hG
  | coe g => exact (EReal.coe_mul r g ▸ EReal.coe_ne_top _)

/-- The residual identity `r(aλ + G) + b - c(λ + ℓ) = rG + δλ + (b - cℓ)` with `δ = ra - c`, for
`r > 0`, real `a, λ, b, c, ℓ` and `G ∈ [-∞, ∞)`. -/
theorem ereal_residual_identity {r : ℝ} (hr : 0 < r) (a lam b c ell : ℝ) {G : EReal} :
    (r : EReal) * ((a : EReal) * (lam : EReal) + G) + (b : EReal) -
        (c : EReal) * ((lam : EReal) + (ell : EReal)) =
      (r : EReal) * G + ((r * a - c : ℝ) : EReal) * (lam : EReal) +
        ((b - c * ell : ℝ) : EReal) := by
  induction G using EReal.rec with
  | bot =>
      rw [EReal.add_bot, EReal.coe_mul_bot_of_pos hr, EReal.bot_add, EReal.bot_add,
        EReal.bot_add, ← EReal.coe_add, ← EReal.coe_mul, EReal.bot_sub]
  | top =>
      rw [EReal.add_top_of_ne_bot (by simp [← EReal.coe_mul]), EReal.coe_mul_top_of_pos hr,
        EReal.top_add_of_ne_bot (EReal.coe_ne_bot _), ← EReal.coe_add, ← EReal.coe_mul,
        EReal.top_sub_coe, ← EReal.coe_mul, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _),
        EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
  | coe g =>
      simp only [← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_eq_coe_iff]
      ring


/-- Moving a real summand across an inequality: `x + ρ ≤ y + B` gives `x ≤ y + (B - ρ)`. -/
theorem ereal_le_add_sub_of_add_le {x y : EReal} {ρ B : ℝ} (h : x + (ρ : EReal) ≤ y + (B : EReal)) :
    x ≤ y + ((B - ρ : ℝ) : EReal) := by
  have h' := add_le_add_left h ((-ρ : ℝ) : EReal)
  rwa [add_assoc, add_assoc, ← EReal.coe_add, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero,
    add_zero, ← sub_eq_add_neg] at h'

/-- Moving a real summand across an inequality: `y + B ≤ x + ρ` gives `y + (B - ρ) ≤ x`. -/
theorem ereal_add_sub_le_of_le_add {x y : EReal} {ρ B : ℝ} (h : y + (B : EReal) ≤ x + (ρ : EReal)) :
    y + ((B - ρ : ℝ) : EReal) ≤ x := by
  have h' := add_le_add_left h ((-ρ : ℝ) : EReal)
  rwa [add_assoc, add_assoc, ← EReal.coe_add, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero,
    add_zero, ← sub_eq_add_neg] at h'

/-- The coordinate hyperplane `{z_last = 0}` is Lebesgue-null. -/
theorem volume_last_coordinate_hyperplane (m : ℕ) :
    MeasureTheory.volume {z : ComplexModel (m + 1) | z (Fin.last m) = 0} = 0 := by
  have hset : {z : ComplexModel (m + 1) | z (Fin.last m) = 0} =
      ((LinearMap.ker ((EuclideanSpace.proj (𝕜 := ℂ) (Fin.last m) :
        ComplexModel (m + 1) →L[ℂ] ℂ).toLinearMap.restrictScalars ℝ)) :
          Set (ComplexModel (m + 1))) := by
    ext z
    simp
  rw [hset]
  apply MeasureTheory.Measure.addHaar_submodule
  intro htop
  have h1 : (EuclideanSpace.single (Fin.last m) (1 : ℂ) : ComplexModel (m + 1)) ∈
      LinearMap.ker ((EuclideanSpace.proj (𝕜 := ℂ) (Fin.last m) :
        ComplexModel (m + 1) →L[ℂ] ℂ).toLinearMap.restrictScalars ℝ) := by
    rw [htop]
    trivial
  simp at h1

/-! ### Chartwise analytic types over an open set -/

section Chart

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- `φ` has analytic singularity type in every holomorphic chart at every point lying over `U`. -/
def ChartTypeOver (φ : M → EReal) (U : Set M) : Prop :=
  ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target → e.val.symm z ∈ U →
    HasAnalyticSingularityTypeAt (chartFunction φ e) z

omit [IsComplexManifold n M] in
/-- Analytic singularities are local. -/
theorem hasManifoldAnalyticSingularityType_of_chartTypeOver {φ : M → EReal}
    (h : ∀ x, ∃ U : Set M, x ∈ U ∧ ChartTypeOver (n := n) φ U) :
    HasManifoldAnalyticSingularityType (n := n) φ := by
  intro e z hz
  obtain ⟨U, hxU, hU⟩ := h (e.val.symm z)
  exact hU e z hz hxU

omit [IsComplexManifold n M] in
theorem ChartTypeOver.mono {φ : M → EReal} {U V : Set M} (h : ChartTypeOver (n := n) φ U) (hVU : V ⊆ U) :
    ChartTypeOver (n := n) φ V :=
  fun e z hz hzV => h e z hz (hVU hzV)

omit [IsComplexManifold n M] in
theorem ChartTypeOver.add {φ ψ : M → EReal} {U : Set M} (hφ : ChartTypeOver (n := n) φ U)
    (hψ : ChartTypeOver (n := n) ψ U) : ChartTypeOver (n := n) (fun x => φ x + ψ x) U :=
  fun e z hz hzU => Pending.RationalAnalyticAddition.hasAnalyticSingularityTypeAt_add
    (hφ e z hz hzU) (hψ e z hz hzU)

omit [IsComplexManifold n M] in
/-- Bounded real perturbations on an open set preserve chartwise analytic types. -/
theorem ChartTypeOver.of_eqOn_add_bounded {φ ψ : M → EReal} {U : Set M} (hφ : ChartTypeOver (n := n) φ U)
    (hU : IsOpen U) {R : M → ℝ} {C : ℝ} (hR : ∀ y ∈ U, |R y| ≤ C)
    (heq : ∀ y ∈ U, ψ y = φ y + (R y : EReal)) : ChartTypeOver (n := n) ψ U := by
  intro e z hz hzU
  have hO : IsOpen (e.val.target ∩ e.val.symm ⁻¹' U) := e.val.isOpen_inter_preimage_symm hU
  have hzO : z ∈ e.val.target ∩ e.val.symm ⁻¹' U := ⟨hz, hzU⟩
  refine Pending.DemaillyAnalyticType.HasAnalyticSingularityTypeAt.of_eventuallyEq_add_bounded
    (hφ e z hz hzU) (b := fun w => R (e.val.symm w))
    ⟨C, (abs_nonneg _).trans (hR _ hzU), ?_⟩ ?_
  · filter_upwards [hO.mem_nhds hzO] with w hw
    exact hR _ hw.2
  · filter_upwards [hO.mem_nhds hzO] with w hw
    exact heq _ hw.2

omit [IsComplexManifold n M] in
/-- The analytic type of `φ ∘ e.symm` near `e x` in one chart transports to all charts through
the holomorphic chart transitions. -/
theorem chartTypeOver_of_comp_coordinates {φ : M → EReal} {U : Set M} (hU : IsOpen U)
    {Ψ : M → ComplexModel n} {A : ComplexModel n → EReal}
    (hΨ : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target → e.val.symm z ∈ U →
      ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (fun w => Ψ (e.val.symm w)) w)
    (hA : ∀ y ∈ U, HasAnalyticSingularityTypeAt A (Ψ y))
    (heq : ∀ y ∈ U, φ y = A (Ψ y)) : ChartTypeOver (n := n) φ U := by
  intro e z hz hzU
  have hO : IsOpen (e.val.target ∩ e.val.symm ⁻¹' U) := e.val.isOpen_inter_preimage_symm hU
  have hzO : z ∈ e.val.target ∩ e.val.symm ⁻¹' U := ⟨hz, hzU⟩
  have h := HasAnalyticSingularityTypeAt.comp_holomorphic (u := A)
    (G := fun w => Ψ (e.val.symm w)) (hA _ hzU) (hΨ e z hz hzU)
  refine Pending.DemaillyAnalyticType.HasAnalyticSingularityTypeAt.of_eventuallyEq_add_bounded h
    (b := fun _ => 0) ⟨0, le_rfl, Eventually.of_forall fun _ => by simp⟩ ?_
  filter_upwards [hO.mem_nhds hzO] with w hw
  change φ (e.val.symm w) = A (Ψ (e.val.symm w)) + ((0 : ℝ) : EReal)
  rw [EReal.coe_zero, add_zero, heq _ hw.2]

end Chart

end SGPT.Okounkov.TranscendentalCore
