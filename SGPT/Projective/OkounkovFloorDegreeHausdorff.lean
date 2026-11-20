import SGPT.Projective.OkounkovConvexBodyScalingLimit
import Mathlib.Analysis.SpecificLimits.Basic

/-! Genuine full-degree floor normalization of compact convex Hausdorff limits.
The ambient real normed space may have dimension zero. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace SGPT.Okounkov.FloorDegreeHausdorff
open Set Filter Metric
open scoped Topology Pointwise

/-- The Euclidean remainder vanishes after normalization, along ALL integer degrees. -/
theorem tendsto_floor_degree_factor (q : ℕ) (hq : 0 < q) :
    Tendsto (fun k : ℕ => (q : ℝ) * ((k / q : ℕ) : ℝ) / (k : ℝ))
      atTop (𝓝 1) := by
  have h : Tendsto (fun k : ℕ => 1 - ((k % q : ℕ) : ℝ) / (k : ℝ))
      atTop (𝓝 ((1 : ℝ) - 0)) :=
    tendsto_const_nhds.sub (tendsto_mod_div_atTop_nhds_zero_nat hq)
  have hzero : Tendsto (fun k : ℕ => 1 - ((k % q : ℕ) : ℝ) / (k : ℝ))
      atTop (𝓝 1) := by simpa only [sub_zero] using h
  apply hzero.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with k hk
  have hkreal : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hdecomp : ((k % q : ℕ) : ℝ) + (q : ℝ) * ((k / q : ℕ) : ℝ) = k := by
    exact_mod_cast Nat.mod_add_div k q
  field_simp
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem hausdorffDist_fixed_smul_le (c : ℝ) (A B : ConvexBody E) :
    hausdorffDist (c • (A : Set E)) (c • (B : Set E)) ≤
      |c| * hausdorffDist (A : Set E) (B : Set E) := by
  have hfin : hausdorffEDist (A : Set E) (B : Set E) ≠ ⊤ :=
    ConvexBody.hausdorffEDist_ne_top
  apply hausdorffDist_le_of_mem_dist (mul_nonneg (abs_nonneg _) hausdorffDist_nonneg)
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨y,hy,hxy⟩ := B.isCompact.exists_infDist_eq_dist B.nonempty x
    refine ⟨c • y, mem_smul_set.mpr ⟨y,hy,rfl⟩, ?_⟩
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, ← dist_eq_norm, ← hxy]
    exact mul_le_mul_of_nonneg_left (infDist_le_hausdorffDist_of_mem hx hfin) (abs_nonneg _)
  · rintro _ ⟨y,hy,rfl⟩
    obtain ⟨x,hx,hyx⟩ := A.isCompact.exists_infDist_eq_dist A.nonempty y
    refine ⟨c • x, mem_smul_set.mpr ⟨x,hx,rfl⟩, ?_⟩
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, ← dist_eq_norm, ← hyx]
    rw [hausdorffDist_comm]
    exact mul_le_mul_of_nonneg_left
      (infDist_le_hausdorffDist_of_mem hy (by rwa [hausdorffEDist_comm])) (abs_nonneg _)

/-- Eventual actual bodies and their actual Hausdorff limit give the desired full-degree
normalization, with eventual compactness/nonemptiness/convexity. No subsequence conclusion. -/
theorem floor_degree_hausdorff_limit (q : ℕ) (hq : 0 < q)
    (F : Set E) (hFc : IsCompact F) (hFn : F.Nonempty) (hFv : Convex ℝ F)
    (P : ℕ → Set E)
    (hP : ∀ᶠ g : ℕ in atTop, IsCompact (P g) ∧ (P g).Nonempty ∧ Convex ℝ (P g))
    (hlim : Tendsto (fun g => hausdorffDist (P g) F) atTop (𝓝 0)) :
    (∀ᶠ k : ℕ in atTop,
      IsCompact ((((k / q : ℕ) : ℝ) / (k : ℝ)) • P (k / q)) ∧
      ((((k / q : ℕ) : ℝ) / (k : ℝ)) • P (k / q)).Nonempty ∧
      Convex ℝ ((((k / q : ℕ) : ℝ) / (k : ℝ)) • P (k / q))) ∧
    Tendsto (fun k : ℕ => hausdorffDist
      ((((k / q : ℕ) : ℝ) / (k : ℝ)) • P (k / q)) ((q : ℝ)⁻¹ • F))
      atTop (𝓝 0) := by
  classical
  have hdiv : Tendsto (fun k : ℕ => k / q) atTop atTop :=
    Nat.tendsto_div_const_atTop (Nat.ne_of_gt hq)
  have hPe := hdiv.eventually hP
  refine ⟨?_,?_⟩
  · filter_upwards [hPe] with k hk
    exact ⟨hk.1.smul _, hk.2.1.smul_set, hk.2.2.smul _⟩
  · let K : ConvexBody E := ⟨F,hFv,hFc,hFn⟩
    let B : ℕ → ConvexBody E := fun g =>
      if h : IsCompact (P g) ∧ (P g).Nonempty ∧ Convex ℝ (P g) then
        ⟨P g,h.2.2,h.1,h.2.1⟩ else K
    have heq : ∀ᶠ k : ℕ in atTop, (B (k / q) : Set E) = P (k / q) := by
      filter_upwards [hPe] with k hk
      simp only [B,dif_pos hk]
      rfl
    have hBlim : Tendsto (fun k : ℕ => hausdorffDist (B (k / q) : Set E) (K : Set E))
        atTop (𝓝 0) := by
      apply (hlim.comp hdiv).congr'
      filter_upwards [heq] with k hk
      rw [hk]
      rfl
    let a : ℕ → ℝ := fun k => (q : ℝ) * ((k / q : ℕ) : ℝ) / (k : ℝ)
    have ha : Tendsto a atTop (𝓝 1) := tendsto_floor_degree_factor q hq
    have hscaled := ConvexBodyScalingLimit.tendsto_hausdorffDist_smul
      atTop (fun k => B (k / q)) K a hBlim ha
    have hscaledConst : Tendsto (fun k : ℕ => hausdorffDist
        ((q : ℝ)⁻¹ • (a k • (B (k / q) : Set E))) ((q : ℝ)⁻¹ • (K : Set E)))
        atTop (𝓝 0) := by
      apply squeeze_zero (fun _ => hausdorffDist_nonneg)
        (fun k => hausdorffDist_fixed_smul_le (q : ℝ)⁻¹ (a k • B (k / q)) K)
      simpa only [mul_zero,ConvexBody.coe_smul] using hscaled.const_mul |(q : ℝ)⁻¹|
    apply hscaledConst.congr'
    filter_upwards [heq] with k hk
    have hqreal : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
    have hcoef : (q : ℝ)⁻¹ * a k = ((k / q : ℕ) : ℝ) / (k : ℝ) := by
      simp only [a,div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hqreal,one_mul]
    rw [smul_smul,hcoef,hk]
    rfl

end SGPT.Okounkov.FloorDegreeHausdorff
