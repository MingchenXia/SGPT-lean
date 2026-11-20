import SGPT.Foundations.Analysis.Pending.XiaoMixedDensityTrace
import SGPT.Foundations.Analysis.Pending.XiaoNormalizedDensityMeasure
import SGPT.Foundations.Analysis.Pending.TopDegreeDensity

set_option autoImplicit false

/-!
# The actual positive test-density and measure step in Xiao's argument

The good-set bound is produced by wedging the actual semipositive difference
with a strongly positive complementary-degree form. The final estimate uses
the genuine measure with density `G ∧ B`, produces its probability instance,
and transfers integrability and both normalized integrals internally.

This is an estimate for actual coefficient-form families. Constructing the
global strictly positive `ddᶜ`-closed test form and Lamari's criterion is separate.
-/

open MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.XiaoTestDensityEstimate

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  TopDegreeDensity

private theorem isSemipositiveOneOne_of_strict {n : ℕ} {A : RealForm n 2}
    (hA : IsOneOne A) (hAp : IsStrictlyPositive A) : IsSemipositiveOneOne A := by
  refine ⟨hA, fun v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · rw [smul_zero, A.map_eq_zero_of_eq ![0, 0] (i := 0) (j := 1) (by simp) (by decide)]
  · exact (hAp v hv).le

/-- Pairing a semipositive actual difference with a strongly positive test form preserves order. -/
theorem topDensity_wedge_le_of_semipositive_sub {m : ℕ}
    {A B : RealForm (m + 1) 2} {G : RealForm (m + 1) (2 * m)} {s : ℝ}
    (hG : G ∈ spCone m) (hsub : IsSemipositiveOneOne (A - s • B)) :
    s * topDensity (coordinateWedge G B) ≤ topDensity (coordinateWedge G A) := by
  have hnonneg := topDensity_nonneg_of_mem_spCone (wedge_mem_spCone hG hsub)
  rw [← wedgeBilin_apply, map_sub, map_smul, topDensity_sub, topDensity_smul] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- The good-set lower bound is produced from genuine Monge–Ampère and mixed densities. -/
theorem ratio_ge_of_density_bound {m : ℕ} {A B : RealForm (m + 1) 2}
    {G : RealForm (m + 1) (2 * m)} (hA : IsOneOne A) (hB : IsOneOne B)
    (hAp : IsStrictlyPositive A) (hBp : IsStrictlyPositive B) (hG : G ∈ spCone m)
    (hv : 0 < topDensity (coordinateWedge G B))
    {c γ M : ℝ} (hc : 0 < c) (hγ : 0 < γ) (hM : 0 < M)
    (hMA : actualTopPowerDensity A = c * topDensity (coordinateWedge G B))
    (hmix : actualMixedTopDensity (Fin.cons B (fun _ : Fin m => A)) ≤
      γ * M * topDensity (coordinateWedge G B)) :
    c / ((m + 1 : ℝ) * γ * M) ≤
      topDensity (coordinateWedge G A) / topDensity (coordinateWedge G B) := by
  have htype : IsOneOne (A - (c / ((m + 1 : ℝ) * γ * M)) • B) := by
    intro u v
    simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
      hA u v, hB u v]
  have hsemi := XiaoMixedDensityTrace.coefficientSemipositive_sub_smul_of_density_bound
    hA hB hAp hBp hc hv hγ hM hMA hmix
  exact (le_div_iff₀ hv).2
    (topDensity_wedge_le_of_semipositive_sub hG ⟨htype, hsemi⟩)

/-- Xiao's factor-four estimate with actual form coefficients and the actual density measure.
The good-set comparison, probability instance and normalized integral are all produced here. -/
theorem integral_actual_testDensity_ge {m : ℕ} {X : Type*} [MeasurableSpace X]
    (σ : Measure X) (A B : X → RealForm (m + 1) 2)
    (G : X → RealForm (m + 1) (2 * m))
    (hA : ∀ x, IsOneOne (A x)) (hB : ∀ x, IsOneOne (B x))
    (hAp : ∀ x, IsStrictlyPositive (A x)) (hBp : ∀ x, IsStrictlyPositive (B x))
    (hG : ∀ x, G x ∈ spCone m)
    (hv : ∀ x, 0 < topDensity (coordinateWedge (G x) (B x)))
    (hvm : Measurable (fun x => topDensity (coordinateWedge (G x) (B x))))
    (hvi : Integrable (fun x => topDensity (coordinateWedge (G x) (B x))) σ)
    (hnorm : ∫ x, topDensity (coordinateWedge (G x) (B x)) ∂σ = 1)
    (hPi : Integrable (fun x => topDensity (coordinateWedge (G x) (A x))) σ)
    (hQi : Integrable
      (fun x => actualMixedTopDensity (Fin.cons (B x) (fun _ : Fin m => A x))) σ)
    (hQm : Measurable
      (fun x => actualMixedTopDensity (Fin.cons (B x) (fun _ : Fin m => A x))))
    {c M : ℝ} (hc : 0 < c) (hM : 0 < M)
    (hint : ∫ x, actualMixedTopDensity (Fin.cons (B x) (fun _ : Fin m => A x)) ∂σ = M)
    (hMA : ∀ x, actualTopPowerDensity (A x) =
      c * topDensity (coordinateWedge (G x) (B x))) :
    c / (4 * (m + 1 : ℝ) * M) ≤ ∫ x, topDensity (coordinateWedge (G x) (A x)) ∂σ := by
  let v : X → ℝ := fun x => topDensity (coordinateWedge (G x) (B x))
  let P : X → ℝ := fun x => topDensity (coordinateWedge (G x) (A x))
  let Q : X → ℝ := fun x => actualMixedTopDensity (Fin.cons (B x) (fun _ : Fin m => A x))
  let μ := σ.withDensity fun x => ENNReal.ofReal (v x)
  let f : X → ℝ := fun x => P x / v x
  let g : X → ℝ := fun x => Q x / v x
  let : IsProbabilityMeasure μ :=
    XiaoNormalizedDensityMeasure.isProbabilityMeasure_withDensity_of_integral_one
      σ hvi (fun x => (hv x).le) hnorm
  have hf : Integrable f μ :=
    XiaoNormalizedDensityMeasure.integrable_div_withDensity σ hvm hv hPi
  have hg : Integrable g μ :=
    XiaoNormalizedDensityMeasure.integrable_div_withDensity σ hvm hv hQi
  have hgm : Measurable g := hQm.div hvm
  have hP0 : ∀ x, 0 ≤ P x := fun x => topDensity_nonneg_of_mem_spCone
    (wedge_mem_spCone (hG x) (isSemipositiveOneOne_of_strict (hA x) (hAp x)))
  have hQ0 : ∀ x, 0 ≤ Q x := by
    intro x
    apply actualMixedTopDensity_nonneg
    intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · exact isSemipositiveOneOne_of_strict (hB x) (hBp x)
    · exact isSemipositiveOneOne_of_strict (hA x) (hAp x)
  have hf0 : ∀ x, 0 ≤ f x := fun x => div_nonneg (hP0 x) (hv x).le
  have hg0 : ∀ x, 0 ≤ g x := fun x => div_nonneg (hQ0 x) (hv x).le
  have hgmass : ∫ x, g x ∂μ = M := by
    rw [XiaoNormalizedDensityMeasure.integral_div_withDensity σ hvm hv Q]
    exact hint
  have hgood : ∀ x, g x < 2 * M → c / (2 * (m + 1 : ℝ) * M) ≤ f x := by
    intro x hx
    have hbound : Q x ≤ 2 * M * v x := ((div_lt_iff₀ (hv x)).mp hx).le
    have hgoodraw := ratio_ge_of_density_bound (hA x) (hB x) (hAp x) (hBp x)
      (hG x) (hv x) hc (by norm_num : (0 : ℝ) < 2) hM (hMA x) hbound
    simpa only [mul_comm, mul_left_comm] using hgoodraw
  have h := XiaoBadSetEstimate.integral_ge_of_bad_set μ hf hg hgm hf0 hg0 hc.le
    (by positivity : (0 : ℝ) < m + 1) hM hgmass hgood
  rw [XiaoNormalizedDensityMeasure.integral_div_withDensity σ hvm hv P] at h
  exact h

end SGPT.Foundations.Analysis.Pending.XiaoTestDensityEstimate
