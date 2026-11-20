import SGPT.Convex.RealMixedCoefficient
import SGPT.Convex.SmoothAlexandrov
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Integral.CompactlySupported

noncomputable section
namespace SGPT.Convex

open Set MeasureTheory
open scoped ContDiff RealInnerProductSpace CompactlySupported

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

/-- Genuine second derivative symmetry, original convex gradient secants and
main's Gram producer give the actual PSD Hessian. -/
theorem hessianMatrix_posSemidef_of_contDiff_convex
    (b : OrthonormalBasis (Fin n) ℝ E) {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hcd : ContDiff ℝ ∞ f) (x : E) :
    (hessianMatrix b f x).PosSemidef := by
  have hd : Differentiable ℝ f := hcd.differentiable (by simp)
  have hg : ContDiff ℝ ∞ (gradient f) := by
    have hs := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.contDiff.comp
      (hcd.fderiv_right (m := ∞) (by simp))
    convert hs using 1
    funext y
    rfl
  have hL := (hg.differentiable (by simp) x).hasFDerivAt
  let J : E →L[ℝ] StrongDual ℝ E := (InnerProductSpace.toDual ℝ E).toContinuousLinearMap
  let Q : E →L[ℝ] StrongDual ℝ E := J.comp (fderiv ℝ (gradient f) x)
  have hQ : HasFDerivAt (fderiv ℝ f) Q x :=
    hasFDerivAt_fderiv_of_hasFDerivAt_gradient hL
  have hsym : ∀ v w, Q v w = Q w v :=
    second_derivative_symmetric (fun y ↦ (hd y).hasFDerivAt) hQ
  have hpos : ∀ v, 0 ≤ Q v v := by
    intro v
    simpa [Q, J, real_inner_comm] using nonneg_inner_gradient_derivative hf hd hL v
  have heq : hessianMatrix b f x = Matrix.of (fun i j ↦ Q (b i) (b j)) := by
    simp only [hessianMatrix, hQ.fderiv]
  rw [heq]
  exact SGPT.Foundations.Analysis.Pending.GramDeterminant.posSemidef_gram b hsym hpos

omit [FiniteDimensional ℝ E] in
/-- The actual smooth original second derivative has continuous matrix entries. -/
theorem continuous_hessianMatrix_of_contDiff
    (b : OrthonormalBasis (Fin n) ℝ E) {f : E → ℝ} (hcd : ContDiff ℝ ∞ f) :
    Continuous (hessianMatrix b f) := by
  have hsecond : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) :=
    (hcd.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (hsecond.continuous.clm_apply continuous_const).clm_apply continuous_const

/-- Literal original real mixed Hessian coefficient, with the source n! diagonal normalization. -/
def smoothMixedDensity (b : OrthonormalBasis (Fin n) ℝ E)
    (u : Fin n → E → ℝ) (x : E) : ℝ :=
  realMixedCoefficientML (fun i ↦ hessianMatrix b (u i) x)

/-- True convexity/smoothness produces nonnegative original mixed density. -/
theorem smoothMixedDensity_nonneg (b : OrthonormalBasis (Fin n) ℝ E)
    {u : Fin n → E → ℝ} (hu : ∀ i, ConvexOn ℝ univ (u i))
    (hcd : ∀ i, ContDiff ℝ ∞ (u i)) (x : E) :
    0 ≤ smoothMixedDensity b u x :=
  realMixedCoefficientML_nonneg _
    (fun i ↦ hessianMatrix_posSemidef_of_contDiff_convex b (hu i) (hcd i) x)

omit [FiniteDimensional ℝ E] in
/-- True original smooth Hessian entries give actual continuous mixed density. -/
theorem continuous_smoothMixedDensity (b : OrthonormalBasis (Fin n) ℝ E)
    {u : Fin n → E → ℝ} (hcd : ∀ i, ContDiff ℝ ∞ (u i)) :
    Continuous (smoothMixedDensity b u) := by
  classical
  change Continuous (fun x ↦ realMixedCoefficientML (fun i ↦ hessianMatrix b (u i) x))
  simp_rw [realMixedCoefficientML_eq_sum]
  apply continuous_finsetSum
  intro σ _
  apply Continuous.matrix_det
  apply continuous_pi
  intro j
  apply continuous_pi
  intro k
  exact (continuous_apply k).comp ((continuous_apply j).comp
    (continuous_hessianMatrix_of_contDiff b (hcd (σ j))))

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Actual smooth mixed Alexandrov density measure, rather than a supplied mixed measure. -/
def smoothMixedAlexandrovMeasure (b : OrthonormalBasis (Fin n) ℝ E)
    (u : Fin n → E → ℝ) : Measure E :=
  μ.withDensity (fun x ↦ ENNReal.ofReal (smoothMixedDensity b u x))

/-- Actual continuous density makes the produced positive smooth mixed measure locally finite. -/
theorem isLocallyFiniteMeasure_smoothMixedAlexandrovMeasure
    (b : OrthonormalBasis (Fin n) ℝ E) {u : Fin n → E → ℝ}
    (hcd : ∀ i, ContDiff ℝ ∞ (u i)) :
    IsLocallyFiniteMeasure (smoothMixedAlexandrovMeasure μ b u) :=
  IsLocallyFiniteMeasure.withDensity_ofReal (continuous_smoothMixedDensity b hcd)

/-- Genuine local finiteness gives actual Radon regularity of the smooth mixed measure. -/
theorem regular_smoothMixedAlexandrovMeasure (b : OrthonormalBasis (Fin n) ℝ E)
    {u : Fin n → E → ℝ} (hcd : ∀ i, ContDiff ℝ ∞ (u i)) :
    (smoothMixedAlexandrovMeasure μ b u).Regular := by
  have := isLocallyFiniteMeasure_smoothMixedAlexandrovMeasure μ b hcd
  infer_instance

/-- The original source pure Alexandrov measure is exactly the smooth
mixed diagonal; genuine basis dimension supplies the factorial normalization. -/
theorem smoothMixedAlexandrovMeasure_diagonal
    (b : OrthonormalBasis (Fin n) ℝ E) {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hcd : ContDiff ℝ ∞ f) :
    smoothMixedAlexandrovMeasure μ b (fun _ : Fin n ↦ f) =
      alexandrovMeasure (innerₗ E) μ (fun x ↦ (f x : EReal)) := by
  have hd : Differentiable ℝ f := hcd.differentiable (by simp)
  have hs : ContDiff ℝ (∞ + 1) (fderiv ℝ f) := by
    simpa using (hcd.fderiv_right (m := ∞) (by simp))
  have hLip : LocallyLipschitz (fderiv ℝ f) := hs.one_of_succ.locallyLipschitz
  rw [alexandrovMeasure_eq_withDensity_det_hessianMatrix b hf hd hLip,
    smoothMixedAlexandrovMeasure]
  congr 1
  funext x
  rw [smoothMixedDensity, realMixedCoefficientML_diagonal,
    ENNReal.ofReal_mul (Nat.cast_nonneg n.factorial), ENNReal.ofReal_natCast,
    Module.finrank_eq_card_basis b.toBasis]
  simp

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- Actual native coefficient symmetry gives actual smooth mixed measure symmetry. -/
theorem smoothMixedAlexandrovMeasure_perm (b : OrthonormalBasis (Fin n) ℝ E)
    (u : Fin n → E → ℝ) (τ : Equiv.Perm (Fin n)) :
    smoothMixedAlexandrovMeasure μ b (fun i ↦ u (τ i)) = smoothMixedAlexandrovMeasure μ b u := by
  unfold smoothMixedAlexandrovMeasure
  congr 1
  funext x
  congr 1
  exact realMixedCoefficientML_perm (fun i ↦ hessianMatrix b (u i) x) τ

omit [μ.IsAddHaarMeasure] in
/-- Genuine original mixed-density nonnegativity identifies every literal
compact-test integral with the original real Hessian-coefficient integral. -/
theorem integral_smoothMixedAlexandrovMeasure
    (b : OrthonormalBasis (Fin n) ℝ E) {u : Fin n → E → ℝ}
    (hu : ∀ i, ConvexOn ℝ univ (u i)) (hcd : ∀ i, ContDiff ℝ ∞ (u i))
    (h : C_c(E, ℝ)) :
    (∫ x, h x ∂smoothMixedAlexandrovMeasure μ b u) =
      ∫ x, smoothMixedDensity b u x * h x ∂μ := by
  rw [smoothMixedAlexandrovMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (continuous_smoothMixedDensity b hcd).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (smoothMixedDensity_nonneg b hu hcd _), smul_eq_mul]

omit [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] [FiniteDimensional ℝ E] in
/-- Actual second differentiation of a finite sum supplies the original sum Hessian. -/
theorem hessianMatrix_finset_sum_of_contDiff {ι : Type*}
    (b : OrthonormalBasis (Fin n) ℝ E) (S : Finset ι)
    {u : ι → E → ℝ} (hcd : ∀ i, ContDiff ℝ ∞ (u i)) (x : E) :
    hessianMatrix b (fun y ↦ ∑ i ∈ S, u i y) x = ∑ i ∈ S, hessianMatrix b (u i) x := by
  have hfirst : fderiv ℝ (fun y ↦ ∑ i ∈ S, u i y) =
      fun y ↦ ∑ i ∈ S, fderiv ℝ (u i) y := by
    funext y
    exact fderiv_fun_sum (fun i _ ↦ (hcd i).differentiable (by simp) y)
  have hsecond : fderiv ℝ (fderiv ℝ (fun y ↦ ∑ i ∈ S, u i y)) x =
      ∑ i ∈ S, fderiv ℝ (fderiv ℝ (u i)) x := by
    rw [hfirst]
    exact fderiv_fun_sum (fun i _ ↦
      ((hcd i).fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
  ext j k
  simp only [hessianMatrix, hsecond, sum_apply, Matrix.sum_apply, Matrix.of_apply]

end SGPT.Convex
