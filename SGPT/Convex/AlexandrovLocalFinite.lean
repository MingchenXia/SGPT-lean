import SGPT.Convex.SubgradientMeasure
import Mathlib.MeasureTheory.Measure.Regular

namespace SGPT.Convex

open Set MeasureTheory Metric
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The shared actual compact secant argument, independent of how its value bound is obtained.
Both compact-value and compact-uniform sequence bounds call this single core. -/
theorem canonical_rawSubgradientImageOn_norm_le_of_value_bound
    {f : E → ℝ} (hf : ConvexOn ℝ univ f) {K : Set E} {S : ℝ}
    (hS : 0 ≤ S) (hval : ∀ z ∈ K + closedBall (0 : E) 1, |f z| ≤ S) :
    ∀ m ∈ rawSubgradientImageOn continuousDualPairing (fun x ↦ (f x : EReal)) K,
      ‖m‖ ≤ 2 * S := by
  have hp := isProper_coe_of_convexOn hf
  intro m hm
  obtain ⟨x, hx⟩ := mem_iUnion.mp hm
  obtain ⟨hxK, hxm⟩ := mem_iUnion.mp hx
  have hm' : m ∈ subdifferential continuousDualPairing (fun z ↦ (f z : EReal)) x := by
    rwa [← rawSubdifferential_eq_subdifferential_of_isProper continuousDualPairing hp]
  have hxval := hval x (mem_add.mpr ⟨x, hxK, 0, mem_closedBall_self zero_le_one, by simp⟩)
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  have hpval := hval (x + v)
    (mem_add.mpr ⟨x, hxK, v, by simp [mem_closedBall, dist_eq_norm, hv], rfl⟩)
  have hnval := hval (x + -v)
    (mem_add.mpr ⟨x, hxK, -v, by simp [mem_closedBall, dist_eq_norm, hv], rfl⟩)
  have hplus := subgradient_le_toReal_difference hp hm'
    (show x + v ∈ effectiveDomain (fun z ↦ (f z : EReal)) by simp [effectiveDomain])
  have hminus := subgradient_le_toReal_difference hp hm'
    (show x + -v ∈ effectiveDomain (fun z ↦ (f z : EReal)) by simp [effectiveDomain])
  simp only [add_sub_cancel_left, EReal.toReal_coe] at hplus hminus
  rw [map_neg] at hminus
  rw [Real.norm_eq_abs]
  rcases abs_le.mp hxval with ⟨hxlo, hxhi⟩
  rcases abs_le.mp hpval with ⟨_, hphi⟩
  rcases abs_le.mp hnval with ⟨_, hnhi⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Actual compact real convex values give a uniform bound on all original
canonical raw subgradients over the entire original compact set. -/
theorem exists_compact_canonical_rawSubgradientImageOn_bound_coe
    {f : E → ℝ} (hf : ConvexOn ℝ univ f) {K : Set E} (hK : IsCompact K) :
    ∃ R : ℝ, ∀ m ∈ rawSubgradientImageOn continuousDualPairing (fun x ↦ (f x : EReal)) K,
      ‖m‖ ≤ R := by
  have hc : Continuous f := continuousOn_univ.mp (hf.continuousOn isOpen_univ)
  have hcomp : IsCompact (K + closedBall (0 : E) 1) := hK.add (isCompact_closedBall 0 1)
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp ((hcomp.image hc).isBounded)
  let S := max R 0
  have hS : 0 ≤ S := le_max_right _ _
  have hval (z : E) (hz : z ∈ K + closedBall (0 : E) 1) : |f z| ≤ S := by
    exact (hR (f z) (mem_image_of_mem f hz)).trans (le_max_left _ _)
  exact ⟨2 * S, canonical_rawSubgradientImageOn_norm_le_of_value_bound hf hS hval⟩

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
  [FiniteDimensional ℝ M]
  (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]

/-- The genuine perfect-pairing inverse transports the produced compact
canonical bound to the actual original dual image. -/
theorem isBounded_rawSubgradientImageOn_coe {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) {K : Set E} (hK : IsCompact K) :
    Bornology.IsBounded (rawSubgradientImageOn B (fun x ↦ (f x : EReal)) K) := by
  let e := B.flip.toContPerfPair.toContinuousLinearEquiv
  obtain ⟨R, hR⟩ := exists_compact_canonical_rawSubgradientImageOn_bound_coe hf hK
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨‖e.symm.toContinuousLinearMap‖ * R, ?_⟩
  intro m hm
  obtain ⟨x, hx⟩ := mem_iUnion.mp hm
  obtain ⟨hxK, hxm⟩ := mem_iUnion.mp hx
  have hmap := rawSubdifferential_image_toContPerfPair B (fun z ↦ (f z : EReal)) x
  have hmc : e m ∈ rawSubdifferential continuousDualPairing (fun z ↦ (f z : EReal)) x :=
    hmap ▸ mem_image_of_mem e hxm
  have hmi : e m ∈ rawSubgradientImageOn continuousDualPairing (fun z ↦ (f z : EReal)) K :=
    mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hxK, hmc⟩⟩
  calc
    ‖m‖ = ‖e.symm (e m)‖ := by rw [e.symm_apply_apply]
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e m‖ := e.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * R :=
      mul_le_mul_of_nonneg_left (hR (e m) hmi) e.symm.toContinuousLinearMap.opNorm_nonneg

variable [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace M] [BorelSpace M] {ν : Measure M} [ν.IsAddHaarMeasure]

/-- Actual source Borel image formula and produced bounded image give
genuine finiteness on every original compact primal set. -/
theorem alexandrovMeasure_coe_lt_top_of_isCompact {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) {K : Set E} (hK : IsCompact K) :
    alexandrovMeasure B ν (fun x ↦ (f x : EReal)) K < ⊤ := by
  rw [alexandrovMeasure_apply_coe B hf hK.isClosed.measurableSet]
  exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (isBounded_rawSubgradientImageOn_coe B hf hK).measure_lt_top

theorem isFiniteMeasureOnCompacts_alexandrovMeasure_coe {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) :
    IsFiniteMeasureOnCompacts (alexandrovMeasure B ν (fun x ↦ (f x : EReal))) :=
  ⟨fun _ hK ↦ alexandrovMeasure_coe_lt_top_of_isCompact B hf hK⟩

theorem isLocallyFiniteMeasure_alexandrovMeasure_coe {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) :
    IsLocallyFiniteMeasure (alexandrovMeasure B ν (fun x ↦ (f x : EReal))) := by
  have := isFiniteMeasureOnCompacts_alexandrovMeasure_coe B hf (ν := ν)
  infer_instance

theorem regular_alexandrovMeasure_coe {f : E → ℝ} (hf : ConvexOn ℝ univ f) :
    Measure.Regular (alexandrovMeasure B ν (fun x ↦ (f x : EReal))) := by
  have := isLocallyFiniteMeasure_alexandrovMeasure_coe B hf (ν := ν)
  infer_instance

end SGPT.Convex
