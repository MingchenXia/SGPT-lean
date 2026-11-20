import SGPT.Convex.Subgradient
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Actual bounded subdifferentials and ordinary domain interior

The boundary normal is produced by actual convex separation, including
lower-dimensional domains. Actual real convex continuity supplies one local
ball bound, and actual subgradient inequalities supply the operator-norm bound.
-/

namespace SGPT.Convex

open Set Filter Topology
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Every actual convex boundary point admits an actual nonzero supporting
continuous linear normal, including actual lower-dimensional domains. -/
theorem exists_nonzero_supporting_normal {D : Set E} (hD : Convex ℝ D)
    {x : E} (hx : x ∈ D) (hxint : x ∉ interior D) :
    ∃ L : StrongDual ℝ E, L ≠ 0 ∧ ∀ y ∈ D, L y ≤ L x := by
  by_cases hint : (interior D).Nonempty
  · exact geometric_hahn_banach_of_nonempty_interior_point hD hxint hint
  let A := affineSpan ℝ D
  have hnotTop : A ≠ ⊤ := by
    intro h
    exact hint (hD.interior_nonempty_iff_affineSpan_eq_top.mpr h)
  obtain ⟨z, _, hz⟩ := A.exists_of_lt (lt_top_iff_ne_top.mpr hnotTop)
  obtain ⟨L, u, hA, hsep⟩ := geometric_hahn_banach_closed_point
    A.convex A.closed_of_finiteDimensional hz
  have hxA : x ∈ A := subset_affineSpan ℝ D hx
  have hnonzero : L ≠ 0 := by
    intro h
    have hbase := hA x hxA
    simp only [h, zero_apply] at hbase hsep
    linarith
  refine ⟨L, hnonzero, ?_⟩
  intro y hy
  have hyA : y ∈ A := subset_affineSpan ℝ D hy
  have hdir : y - x ∈ A.direction := A.vsub_mem_direction hyA hxA
  have hzero : L (y - x) = 0 := by
    by_contra hn
    let t : ℝ := (u - L x + 1) / L (y - x)
    have hp := A.vadd_mem_of_mem_direction (A.direction.smul_mem t hdir) hxA
    have hbound := hA (t • (y - x) + x) hp
    rw [map_add, map_smul] at hbound
    change t * L (y - x) + L x < u at hbound
    have heq : t * L (y - x) = u - L x + 1 := by
      dsimp [t]
      field_simp
    rw [heq] at hbound
    linarith
  have hvalue : L y - L x = 0 := by simpa only [map_sub] using hzero
  linarith

/-- Actual real convex continuity provides an actual positive-radius domain
ball with actual real oscillation less than one. -/
theorem exists_local_domain_bound {f : E → EReal} (hf : IsProper f)
    {x : E} (hx : x ∈ interior (effectiveDomain f)) :
    ∃ r : ℝ, 0 < r ∧ ∀ h : E, ‖h‖ < r →
      x + h ∈ effectiveDomain f ∧ |(f (x + h)).toReal - (f x).toReal| < 1 := by
  have hc : ContinuousAt (fun y ↦ (f y).toReal) x :=
    ((convexOn_toReal_effectiveDomain hf).continuousOn_interior x hx).continuousAt
      (isOpen_interior.mem_nhds hx)
  have hdom : effectiveDomain f ∈ 𝓝 x :=
    mem_nhds_iff.mpr ⟨interior (effectiveDomain f), interior_subset, isOpen_interior, hx⟩
  have hval : ∀ᶠ y in 𝓝 x, |(f y).toReal - (f x).toReal| < 1 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using
      hc.eventually (Metric.ball_mem_nhds (f x).toReal zero_lt_one)
  have hd : ∀ᶠ y in 𝓝 x, y ∈ effectiveDomain f := hdom
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hd.and hval)
  refine ⟨r, hr, fun h hh ↦ hball (x + h) ?_⟩
  simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] using hh

omit [FiniteDimensional ℝ E] in
/-- Every actual proper subgradient bounds each actual finite real secant. -/
theorem subgradient_le_toReal_difference {f : E → EReal} (hf : IsProper f)
    {x y : E} {m : StrongDual ℝ E} (hm : m ∈ subdifferential continuousDualPairing f x)
    (hy : y ∈ effectiveDomain f) : m (y - x) ≤ (f y).toReal - (f x).toReal := by
  have hfx : f x = ((f x).toReal : EReal) :=
    (EReal.coe_toReal (ne_of_lt hm.1) (hf.2.2 _)).symm
  have hfy : f y = ((f y).toReal : EReal) :=
    (EReal.coe_toReal (ne_of_lt hy) (hf.2.2 _)).symm
  have h := hm.2 y
  change f x + (m (y - x) : EReal) ≤ f y at h
  rw [hfx, hfy, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  linarith

omit [FiniteDimensional ℝ E] in
/-- Actual two-sided local domain bounds bound actual subgradient evaluations. -/
theorem subgradient_apply_le_one {f : E → EReal} (hf : IsProper f) {x : E}
    {r : ℝ} (hb : ∀ h : E, ‖h‖ < r →
      x + h ∈ effectiveDomain f ∧ |(f (x + h)).toReal - (f x).toReal| < 1)
    {m : StrongDual ℝ E} (hm : m ∈ subdifferential continuousDualPairing f x)
    {h : E} (hh : ‖h‖ < r) : ‖m h‖ ≤ 1 := by
  have hp := hb h hh
  have hn := hb (-h) (by simpa only [norm_neg] using hh)
  have hplus := subgradient_le_toReal_difference hf hm hp.1
  have hminus := subgradient_le_toReal_difference hf hm hn.1
  rw [add_sub_cancel_left] at hplus hminus
  rw [map_neg] at hminus
  have hpval := (abs_lt.mp hp.2).2
  have hnval := (abs_lt.mp hn.2).2
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith

/-- Genuine local convex continuity gives an actual uniform subgradient operator-norm bound. -/
theorem exists_subgradient_norm_bound_of_mem_interior {f : E → EReal} (hf : IsProper f)
    {x : E} (hx : x ∈ interior (effectiveDomain f)) :
    ∃ R : ℝ, ∀ m ∈ subdifferential continuousDualPairing f x, ‖m‖ ≤ R := by
  obtain ⟨r, hr, hb⟩ := exists_local_domain_bound hf hx
  refine ⟨2 / r, fun m hm ↦ ?_⟩
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  have hhalf : 0 < r / 2 := by positivity
  have hsmall : ‖(r / 2 : ℝ) • v‖ < r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hhalf, hv, mul_one]
    linarith
  have h := subgradient_apply_le_one hf hb hm hsmall
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hhalf] at h
  apply (le_div_iff₀ hr).mpr
  nlinarith

/-- The actual canonical-dual subdifferential is bounded at every actual interior domain point. -/
theorem isBounded_subdifferential_of_mem_interior {f : E → EReal} (hf : IsProper f)
    {x : E} (hx : x ∈ interior (effectiveDomain f)) :
    Bornology.IsBounded (subdifferential continuousDualPairing f x) :=
  isBounded_iff_forall_norm_le.mpr (exists_subgradient_norm_bound_of_mem_interior hf hx)

omit [FiniteDimensional ℝ E] in
/-- Actual supporting domain normals generate an actual ray of subgradients. -/
theorem add_normal_mem_subdifferential {f : E → EReal}
    {x : E} {m L : StrongDual ℝ E} (hm : m ∈ subdifferential continuousDualPairing f x)
    (hL : ∀ y ∈ effectiveDomain f, L y ≤ L x) {t : ℝ} (ht : 0 ≤ t) :
    m + t • L ∈ subdifferential continuousDualPairing f x := by
  refine ⟨hm.1, fun y ↦ ?_⟩
  by_cases hy : y ∈ effectiveDomain f
  · have hnormal : L (y - x) ≤ 0 := by rw [map_sub]; linarith [hL y hy]
    have hvalue : ((m + t • L) (y - x) : EReal) ≤ (m (y - x) : EReal) := by
      apply EReal.coe_le_coe
      simp only [add_apply, smul_apply, smul_eq_mul]
      have hneg := mul_nonpos_of_nonneg_of_nonpos ht hnormal
      linarith
    exact (add_le_add (le_refl (f x)) hvalue).trans (hm.2 y)
  · have htop : f y = ⊤ := eq_top_iff.mpr (le_of_not_gt hy)
    rw [htop]
    exact le_top

omit [FiniteDimensional ℝ E] in
/-- An actual nonzero normal ray rules out actual subdifferential boundedness. -/
theorem not_isBounded_subdifferential_of_normal {f : E → EReal}
    {x : E} {m L : StrongDual ℝ E} (hm : m ∈ subdifferential continuousDualPairing f x)
    (hL : L ≠ 0) (hsupport : ∀ y ∈ effectiveDomain f, L y ≤ L x) :
    ¬ Bornology.IsBounded (subdifferential continuousDualPairing f x) := by
  intro hbounded
  obtain ⟨R, hR⟩ := hbounded.exists_norm_le
  have hnorm : 0 < ‖L‖ := norm_pos_iff.mpr hL
  let t : ℝ := (|R| + ‖m‖ + 1) / ‖L‖
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hmem := add_normal_mem_subdifferential hm hsupport ht
  have hbound := hR (m + t • L) hmem
  have htriangle := norm_sub_le (m + t • L) m
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at htriangle
  have heq : t * ‖L‖ = |R| + ‖m‖ + 1 := by dsimp [t]; field_simp
  rw [heq] at htriangle
  have hRabs := le_abs_self R
  linarith

/-- Actual nonempty bounded canonical-dual subdifferentials characterize actual ambient domain interior. -/
theorem subdifferential_nonempty_isBounded_iff_mem_interior {f : E → EReal}
    (hf : IsProper f) (x : E) :
    ((subdifferential continuousDualPairing f x).Nonempty ∧
      Bornology.IsBounded (subdifferential continuousDualPairing f x)) ↔
        x ∈ interior (effectiveDomain f) := by
  constructor
  · rintro ⟨hne, hbounded⟩
    obtain ⟨m, hm⟩ := hne
    by_contra hx
    obtain ⟨L, hL, hsupport⟩ := exists_nonzero_supporting_normal
      (convex_effectiveDomain hf.1) hm.1 hx
    exact not_isBounded_subdifferential_of_normal hm hL hsupport hbounded
  · intro hx
    exact ⟨subdifferential_nonempty_of_mem_intrinsicInterior continuousDualPairing hf
      (interior_subset_intrinsicInterior (𝕜 := ℝ) hx),
      isBounded_subdifferential_of_mem_interior hf hx⟩

/-- The canonical characterization uses the exact source raw subdifferential. -/
theorem rawSubdifferential_nonempty_isBounded_iff_mem_interior {f : E → EReal}
    (hf : IsProper f) (x : E) :
    ((rawSubdifferential continuousDualPairing f x).Nonempty ∧
      Bornology.IsBounded (rawSubdifferential continuousDualPairing f x)) ↔
        x ∈ interior (effectiveDomain f) := by
  rw [rawSubdifferential_eq_subdifferential_of_isProper continuousDualPairing hf]
  exact subdifferential_nonempty_isBounded_iff_mem_interior hf x

omit [FiniteDimensional ℝ E] in
/-- The genuine perfect dual equivalence transports the exact raw source inequalities. -/
theorem rawSubdifferential_image_toContPerfPair {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] (f : E → EReal) (x : E) :
    B.flip.toContPerfPair '' rawSubdifferential B f x =
      rawSubdifferential continuousDualPairing f x := by
  ext L
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact hm
  · intro hm
    obtain ⟨m, rfl⟩ := B.flip.toContPerfPair.surjective L
    exact ⟨m, hm, rfl⟩

/-- Exact source `thm:nablaF` third clause for the actual arbitrary continuous
perfect pairing and the exact raw source subdifferential. -/
theorem rawSubdifferential_nonempty_isBounded_iff_mem_interior_of_isContPerfPair
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {f : E → EReal}
    (hf : IsProper f) (x : E) :
    ((rawSubdifferential B f x).Nonempty ∧ Bornology.IsBounded (rawSubdifferential B f x)) ↔
      x ∈ interior (effectiveDomain f) := by
  let e : F ≃L[ℝ] StrongDual ℝ E := B.flip.toContPerfPair.toContinuousLinearEquiv
  have himage : e '' rawSubdifferential B f x = rawSubdifferential continuousDualPairing f x :=
    rawSubdifferential_image_toContPerfPair B f x
  constructor
  · rintro ⟨hne, hbounded⟩
    apply (rawSubdifferential_nonempty_isBounded_iff_mem_interior hf x).mp
    constructor
    · rw [← himage]
      exact hne.image e
    · rw [← himage]
      exact e.toContinuousLinearMap.lipschitz.isBounded_image hbounded
  · intro hx
    obtain ⟨hne, hbounded⟩ :=
      (rawSubdifferential_nonempty_isBounded_iff_mem_interior hf x).mpr hx
    have hinverse : e.symm '' rawSubdifferential continuousDualPairing f x =
        rawSubdifferential B f x := by
      rw [← himage]
      exact e.toEquiv.symm_image_image _
    constructor
    · rw [← himage] at hne
      exact hne.of_image
    · rw [← hinverse]
      exact e.symm.toContinuousLinearMap.lipschitz.isBounded_image hbounded

end SGPT.Convex
