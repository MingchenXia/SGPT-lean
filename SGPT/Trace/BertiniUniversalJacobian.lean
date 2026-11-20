import SGPT.Trace.BertiniUniversalProduct
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Determinant

/-! Actual complex/ordinary-real Jacobian of the ORIGINAL normalized
universal equation replacing ONE actual parameter coordinate. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Set Filter Metric
open scoped Topology Manifold ContDiff BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini

section Replacement
variable {D : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι ℂ (ComplexModel D)) (r : ι)

def coordinateReplacementDerivative (g : ComplexModel D →L[ℂ] ℂ) :
    ComplexModel D →L[ℂ] ComplexModel D :=
  ContinuousLinearMap.id ℂ _ + (g - LinearMap.toContinuousLinearMap (b.coord r)).smulRight (b r)

theorem coordinateReplacementDerivative_toMatrix (g : ComplexModel D →L[ℂ] ℂ) :
    LinearMap.toMatrix b b (coordinateReplacementDerivative b r g).toLinearMap =
      Matrix.updateRow (1 : Matrix ι ι ℂ) r (fun j => g (b j)) := by
  ext i j
  by_cases hi : i = r
  · subst i
    simp [LinearMap.toMatrix_apply,coordinateReplacementDerivative,Matrix.updateRow,b.coord_apply,Finsupp.single_apply,eq_comm]
  · simp [LinearMap.toMatrix_apply,coordinateReplacementDerivative,Matrix.updateRow,hi,b.coord_apply,Matrix.one_apply,Finsupp.single_apply,eq_comm]

theorem coordinateReplacementDerivative_det (g : ComplexModel D →L[ℂ] ℂ) :
    LinearMap.det (coordinateReplacementDerivative b r g).toLinearMap = g (b r) := by
  rw [← LinearMap.det_toMatrix b,coordinateReplacementDerivative_toMatrix]
  have hs : (∑ j : ι, (g (b j)) • (1 : Matrix ι ι ℂ) j) = fun j => g (b j) := by
    ext j
    simp [Matrix.one_apply,Pi.smul_apply]
  rw [← hs,Matrix.det_updateRow_sum,Matrix.det_one,smul_eq_mul,mul_one]

def coordinateReplacementMap (G : ComplexModel D → ℂ) (w : ComplexModel D) : ComplexModel D :=
  w + (G w - b.repr w r) • b r

omit [Fintype ι] [DecidableEq ι] in
theorem coordinateReplacementMap_hasFDerivAt {G : ComplexModel D → ℂ} {g : ComplexModel D →L[ℂ] ℂ}
    {w : ComplexModel D} (hG : HasFDerivAt G g w) :
    HasFDerivAt (coordinateReplacementMap b r G) (coordinateReplacementDerivative b r g) w := by
  exact (hasFDerivAt_id w).add
    ((hG.sub (LinearMap.toContinuousLinearMap (b.coord r)).hasFDerivAt).smul_const (b r))
end Replacement

def productCoordinateBasis (N n : ℕ) :
    Module.Basis (Fin N ⊕ Fin n) ℂ (ComplexModel (N + n)) :=
  ((EuclideanSpace.basisFun (Fin N) ℂ).toBasis.prod (EuclideanSpace.basisFun (Fin n) ℂ).toBasis).map
    (prodModelEquiv N n).toLinearEquiv

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i j : Fin (N + 1)) (e : ComplexChart n X) (m : Fin N)

theorem conormalGenerator_fderiv_parameter {w : ComplexModel (N + n)}
    (hw : w ∈ conormalDomain p e j) :
    fderiv ℂ (conormalGenerator p i e j 0) w (productCoordinateBasis N n (Sum.inl m)) =
      chartLift p e j ((prodModelEquiv N n).symm w).2 (i.succAbove m) := by
  let ζ₀ := ((prodModelEquiv N n).symm w).1
  let z₀ := ((prodModelEquiv N n).symm w).2
  let J : ComplexModel N → ComplexModel (N + n) := fun ζ => prodModelEquiv N n (ζ,z₀)
  have hJ : HasFDerivAt J
      ((prodModelEquiv N n : _ →L[ℂ] _).comp
        ((ContinuousLinearMap.id ℂ (ComplexModel N)).prod (0 : ComplexModel N →L[ℂ] ComplexModel n))) ζ₀ :=
    (prodModelEquiv N n).hasFDerivAt.comp ζ₀
      ((hasFDerivAt_id ζ₀).prodMk (hasFDerivAt_const z₀ ζ₀))
  have hJw : J ζ₀ = w := (prodModelEquiv N n).apply_symm_apply w
  have hG := (differentiableOn_conormalGenerator p p.contMDiff i e j 0).differentiableAt
    ((isOpen_conormalDomain p p.contMDiff e j).mem_nhds hw)
  have hGJ : HasFDerivAt (conormalGenerator p i e j 0)
      (fderiv ℂ (conormalGenerator p i e j 0) w) (J ζ₀) := by
    simpa only [hJw] using hG.hasFDerivAt
  have hcomp := hGJ.comp ζ₀ hJ
  have heq : conormalGenerator p i e j 0 ∘ J =
      fun ζ => pairing (chartLift p e j z₀) (affineLift i ζ) := by
    funext ζ
    simp only [J,conormalGenerator,Fin.cons_zero,Function.comp_apply,
      ContinuousLinearEquiv.symm_apply_apply]
    exact pairing_comm _ _
  rw [heq] at hcomp
  have hD := hcomp.unique (hasFDerivAt_pairing_affineLift (chartLift p e j z₀) i ζ₀)
  have hv := DFunLike.congr_fun hD (EuclideanSpace.single m 1)
  have hb : productCoordinateBasis N n (Sum.inl m) =
      prodModelEquiv N n (EuclideanSpace.single m 1,0) := by
    simp [productCoordinateBasis,Module.Basis.prod_apply,EuclideanSpace.basisFun_apply]
  rw [hb]
  simpa [hyperplaneLinearPart_apply] using hv

def parameterEquationFlattening (w : ComplexModel (N + n)) : ComplexModel (N + n) :=
  coordinateReplacementMap (productCoordinateBasis N n) (Sum.inl m) (conormalGenerator p i e j 0) w

theorem parameterEquationFlattening_complex_det {w : ComplexModel (N + n)}
    (hw : w ∈ conormalDomain p e j) :
    LinearMap.det (fderiv ℂ (parameterEquationFlattening p i j e m) w).toLinearMap =
      parameterCoefficient p i j m (e.val.symm ((prodModelEquiv N n).symm w).2) := by
  have hG := (differentiableOn_conormalGenerator p p.contMDiff i e j 0).differentiableAt
    ((isOpen_conormalDomain p p.contMDiff e j).mem_nhds hw)
  unfold parameterEquationFlattening
  rw [(coordinateReplacementMap_hasFDerivAt (productCoordinateBasis N n) (Sum.inl m) hG.hasFDerivAt).fderiv,
    coordinateReplacementDerivative_det,conormalGenerator_fderiv_parameter p i j e m hw]
  rfl

theorem parameterEquationFlattening_real_abs_det {w : ComplexModel (N + n)}
    (hw : w ∈ conormalDomain p e j) :
    |LinearMap.det (fderiv ℝ (parameterEquationFlattening p i j e m) w).toLinearMap| =
      ‖parameterCoefficient p i j m (e.val.symm ((prodModelEquiv N n).symm w).2)‖ ^ 2 := by
  have hG := (differentiableOn_conormalGenerator p p.contMDiff i e j 0).differentiableAt
    ((isOpen_conormalDomain p p.contMDiff e j).mem_nhds hw)
  have hF : DifferentiableAt ℂ (parameterEquationFlattening p i j e m) w :=
    (coordinateReplacementMap_hasFDerivAt (productCoordinateBasis N n) (Sum.inl m) hG.hasFDerivAt).differentiableAt
  rw [hF.fderiv_restrictScalars ℝ]
  change |LinearMap.det (((fderiv ℂ (parameterEquationFlattening p i j e m) w).toLinearMap).restrictScalars ℝ)| = _
  rw [LinearMap.det_restrictScalars,Algebra.norm_complex_apply,
    abs_of_nonneg (Complex.normSq_nonneg _),Complex.normSq_eq_norm_sq,
    parameterEquationFlattening_complex_det p i j e m hw]

end SGPT.Trace.BertiniUniversal
