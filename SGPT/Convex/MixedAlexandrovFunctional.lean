import SGPT.Convex.SmoothMixedAlexandrov
import SGPT.Convex.RealMixedPolarization
import SGPT.Convex.FiniteAlexandrovContinuity
import SGPT.Convex.SmoothFiniteApproximation
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

noncomputable section
namespace SGPT.Convex

open Set Filter MeasureTheory
open scoped CompactlySupported Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure] {n : ℕ}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Actual finite sums preserve the original finite convex functions. -/
theorem convexOn_finset_sum_real {ι : Type*} (S : Finset ι)
    {u : ι → E → ℝ} (hu : ∀ i, ConvexOn ℝ univ (u i)) :
    ConvexOn ℝ univ (fun x ↦ ∑ i ∈ S, u i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using convexOn_const (0 : ℝ) convex_univ
  | @insert a S ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hu a).add ih

/-- Literal original finite convex subset sum. -/
def finiteConvexSubsetSum (u : Fin n → RealConvexFunction E) (S : Finset (Fin n)) :
    RealConvexFunction E :=
  ⟨fun x ↦ ∑ i ∈ S, (u i).val x, convexOn_finset_sum_real S (fun i ↦ (u i).property)⟩

/-- Actual locally finite pure Alexandrov measure gives its genuine compact-test linear map. -/
def pureAlexandrovIntegral (f : RealConvexFunction E) : C_c(E, ℝ) →ₚ[ℝ] ℝ := by
  letI := isFiniteMeasureOnCompacts_alexandrovMeasure_coe (innerₗ E) f.property (ν := μ)
  exact CompactlySupportedContinuousMap.integralPositiveLinearMap
    (alexandrovMeasure (innerₗ E) μ (fun x ↦ (f.val x : EReal)))

/-- The original literal finite signed polarization functional; positivity is proved later. -/
def mixedAlexandrovFunctional (u : Fin n → RealConvexFunction E) : C_c(E, ℝ) →ₗ[ℝ] ℝ :=
  (n.factorial : ℝ)⁻¹ • ∑ S : Finset (Fin n),
    ((-1 : ℝ) ^ (n - S.card)) • (pureAlexandrovIntegral μ (finiteConvexSubsetSum u S)).toLinearMap

/-- Literal evaluation retains the actual pure measures of the original subset sums. -/
theorem mixedAlexandrovFunctional_apply (u : Fin n → RealConvexFunction E) (h : C_c(E, ℝ)) :
    mixedAlexandrovFunctional μ u h = (n.factorial : ℝ)⁻¹ *
      ∑ S : Finset (Fin n), ((-1 : ℝ) ^ (n - S.card)) *
        ∫ x, h x ∂alexandrovMeasure (innerₗ E) μ
          (fun x ↦ ((∑ i ∈ S, (u i).val x : ℝ) : EReal)) := by
  classical
  simp [mixedAlexandrovFunctional, pureAlexandrovIntegral, finiteConvexSubsetSum,
    LinearMap.sum_apply, smul_eq_mul]

/-- The literal signed functional of actual smooth tuples equals the actual
nonnegative mixed-density integral, by true original Hessian sums. -/
theorem mixedAlexandrovFunctional_eq_smooth_integral
    (b : OrthonormalBasis (Fin n) ℝ E) (u : Fin n → RealConvexFunction E)
    (hcd : ∀ i, ContDiff ℝ ∞ (u i).val) (h : C_c(E, ℝ)) :
    mixedAlexandrovFunctional μ u h =
      ∫ x, smoothMixedDensity b (fun i ↦ (u i).val) x * h x ∂μ := by
  classical
  let D : Finset (Fin n) → E → ℝ := fun S x ↦
    realMixedCoefficientML (fun _ : Fin n ↦ ∑ j ∈ S, hessianMatrix b (u j).val x)
  have hform (S : Finset (Fin n)) :
      (∫ x, h x ∂alexandrovMeasure (innerₗ E) μ
        (fun x ↦ ((∑ i ∈ S, (u i).val x : ℝ) : EReal))) = ∫ x, D S x * h x ∂μ := by
    have hf := convexOn_finset_sum_real S (fun i ↦ (u i).property)
    have hs : ContDiff ℝ ∞ (fun x ↦ ∑ i ∈ S, (u i).val x) :=
      ContDiff.sum (fun i _ ↦ hcd i)
    rw [← smoothMixedAlexandrovMeasure_diagonal μ b hf hs,
      integral_smoothMixedAlexandrovMeasure μ b (fun _ ↦ hf) (fun _ ↦ hs) h]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    simp only [D, smoothMixedDensity, hessianMatrix_finset_sum_of_contDiff b S hcd]
  have hD (S : Finset (Fin n)) : Continuous (D S) := by
    have hs : ContDiff ℝ ∞ (fun x ↦ ∑ i ∈ S, (u i).val x) :=
      ContDiff.sum (fun i _ ↦ hcd i)
    have hd := continuous_smoothMixedDensity b (u := fun _ : Fin n ↦ fun x ↦ ∑ i ∈ S, (u i).val x)
      (fun _ ↦ hs)
    convert hd using 1
    funext x
    simp only [D, smoothMixedDensity, hessianMatrix_finset_sum_of_contDiff b S hcd]
  have hint (S : Finset (Fin n)) : Integrable
      (fun x ↦ ((-1 : ℝ) ^ (n - S.card)) * (D S x * h x)) μ := by
    have ht : HasCompactSupport (fun x ↦ D S x * h x) := h.hasCompactSupport.mul_left
    exact ((hD S).mul h.continuous).integrable_of_hasCompactSupport ht |>.const_mul _
  have hpoly (x : E) : (n.factorial : ℝ)⁻¹ *
      (∑ S : Finset (Fin n), ((-1 : ℝ) ^ (n - S.card)) * D S x) =
        smoothMixedDensity b (fun i ↦ (u i).val) x := by
    dsimp only [D, smoothMixedDensity]
    simp_rw [realMixedCoefficientML_diagonal]
    exact realMixedCoefficientML_normalized_polarization _
  rw [mixedAlexandrovFunctional_apply]
  simp_rw [hform]
  calc
    _ = (n.factorial : ℝ)⁻¹ * ∑ S : Finset (Fin n),
        ∫ x, ((-1 : ℝ) ^ (n - S.card)) * (D S x * h x) ∂μ := by
      simp_rw [integral_const_mul]
    _ = (n.factorial : ℝ)⁻¹ * ∫ x, ∑ S : Finset (Fin n),
        ((-1 : ℝ) ^ (n - S.card)) * (D S x * h x) ∂μ := by
      rw [integral_finsetSum Finset.univ (fun S _ ↦ hint S)]
    _ = ∫ x, (n.factorial : ℝ)⁻¹ * ∑ S : Finset (Fin n),
        ((-1 : ℝ) ^ (n - S.card)) * (D S x * h x) ∂μ := (integral_const_mul _ _).symm
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul, ← mul_assoc, hpoly]

/-- The actual smooth density proves positivity of the literal functional. -/
theorem mixedAlexandrovFunctional_nonneg_of_contDiff
    (b : OrthonormalBasis (Fin n) ℝ E) (u : Fin n → RealConvexFunction E)
    (hcd : ∀ i, ContDiff ℝ ∞ (u i).val) (h : C_c(E, ℝ)) (hh : 0 ≤ h) :
    0 ≤ mixedAlexandrovFunctional μ u h := by
  rw [mixedAlexandrovFunctional_eq_smooth_integral μ b u hcd]
  apply integral_nonneg
  intro x
  exact mul_nonneg (smoothMixedDensity_nonneg b (fun i ↦ (u i).property) hcd x) (hh x)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Every actual finite subset sum has its genuine compact-uniform limit. -/
theorem tendstoUniformlyOn_finiteConvexSubsetSum
    {F : ℕ → Fin n → RealConvexFunction E} {u : Fin n → RealConvexFunction E}
    (hF : ∀ i (K : Set E), IsCompact K →
      TendstoUniformlyOn (fun j ↦ (F j i).val) (u i).val atTop K)
    (S : Finset (Fin n)) {K : Set E} (hK : IsCompact K) :
    TendstoUniformlyOn (fun j ↦ (finiteConvexSubsetSum (F j) S).val)
      (finiteConvexSubsetSum u S).val atTop K := by
  classical
  change TendstoUniformlyOn (fun j x ↦ ∑ i ∈ S, (F j i).val x)
    (fun x ↦ ∑ i ∈ S, (u i).val x) atTop K
  induction S using Finset.induction_on with
  | empty =>
      simpa using (tendsto_const_nhds (x := (0 : ℝ))).tendstoUniformlyOn_const K
  | @insert a S ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hF a K hK).add ih

/-- Actual pure local weak continuity of every original subset sum gives
continuity of the literal finite signed functional. -/
theorem tendsto_mixedAlexandrovFunctional
    {F : ℕ → Fin n → RealConvexFunction E} {u : Fin n → RealConvexFunction E}
    (hF : ∀ i (K : Set E), IsCompact K →
      TendstoUniformlyOn (fun j ↦ (F j i).val) (u i).val atTop K)
    (h : C_c(E, ℝ)) :
    Tendsto (fun j ↦ mixedAlexandrovFunctional μ (F j) h) atTop
      (𝓝 (mixedAlexandrovFunctional μ u h)) := by
  classical
  simp_rw [mixedAlexandrovFunctional_apply]
  apply tendsto_const_nhds.mul
  apply tendsto_finsetSum
  intro S _
  apply tendsto_const_nhds.mul
  exact tendsto_integral_alexandrovMeasure_of_finite_convex_compact_convergence
    (innerₗ E) (finiteConvexSubsetSum u S).property
    (fun j ↦ (finiteConvexSubsetSum (F j) S).property)
    (fun K hK ↦ tendstoUniformlyOn_finiteConvexSubsetSum hF S hK) h

/-- Genuine smooth original approximation transfers actual nonnegative
mixed-density positivity to every original finite convex tuple. -/
theorem mixedAlexandrovFunctional_nonneg
    (b : OrthonormalBasis (Fin n) ℝ E) (u : Fin n → RealConvexFunction E)
    (h : C_c(E, ℝ)) (hh : 0 ≤ h) :
    0 ≤ mixedAlexandrovFunctional μ u h := by
  let F : ℕ → Fin n → RealConvexFunction E := fun j i ↦
    ⟨finiteConvexSmoothApprox μ (u i).val j,
      convexOn_finiteConvexSmoothApprox μ (u i).property j⟩
  have ht := tendsto_mixedAlexandrovFunctional μ (F := F) (u := u)
    (fun i K hK ↦ tendstoUniformlyOn_finiteConvexSmoothApprox μ (u i).property hK) h
  apply ge_of_tendsto ht
  apply Filter.Eventually.of_forall
  intro j
  exact mixedAlexandrovFunctional_nonneg_of_contDiff μ b (F j)
    (fun i ↦ contDiff_finiteConvexSmoothApprox μ (u i).property j) h hh

/-- The literal functional is now genuinely positive by original smooth approximation. -/
def mixedAlexandrovPositiveFunctional (b : OrthonormalBasis (Fin n) ℝ E)
    (u : Fin n → RealConvexFunction E) : C_c(E, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ (mixedAlexandrovFunctional μ u)
    (fun h hh ↦ mixedAlexandrovFunctional_nonneg μ b u h hh)

/-- Actual Riesz representation constructs the original mixed Alexandrov measure. -/
def mixedAlexandrovMeasure (b : OrthonormalBasis (Fin n) ℝ E)
    (u : Fin n → RealConvexFunction E) : Measure E :=
  RealRMK.rieszMeasure (mixedAlexandrovPositiveFunctional μ b u)

/-- The genuinely constructed mixed measure has its actual original compact-test functional. -/
theorem integral_mixedAlexandrovMeasure (b : OrthonormalBasis (Fin n) ℝ E)
    (u : Fin n → RealConvexFunction E) (h : C_c(E, ℝ)) :
    (∫ x, h x ∂mixedAlexandrovMeasure μ b u) = mixedAlexandrovFunctional μ u h :=
  RealRMK.integral_rieszMeasure (mixedAlexandrovPositiveFunctional μ b u) h

/-- Riesz construction produces the actual mixed measure's local finiteness. -/
theorem isLocallyFiniteMeasure_mixedAlexandrovMeasure
    (b : OrthonormalBasis (Fin n) ℝ E) (u : Fin n → RealConvexFunction E) :
    IsLocallyFiniteMeasure (mixedAlexandrovMeasure μ b u) := by
  unfold mixedAlexandrovMeasure
  infer_instance

/-- The original arbitrary finite convex mixed measure is genuinely Radon. -/
theorem regular_mixedAlexandrovMeasure
    (b : OrthonormalBasis (Fin n) ℝ E) (u : Fin n → RealConvexFunction E) :
    (mixedAlexandrovMeasure μ b u).Regular := by
  unfold mixedAlexandrovMeasure
  infer_instance

end SGPT.Convex
