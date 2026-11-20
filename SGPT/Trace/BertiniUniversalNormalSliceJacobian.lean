import SGPT.Trace.BertiniUniversalSliceJacobian

/-! Actual deleted-normal coordinate derivative/Jacobian. The true same-normal
neighborhood identity manufactures the normal derivative row internally. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Set Filter Metric
open scoped Topology BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {d : ℕ}
def normalSliceMatrix (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (r s : Fin (d + 1)) :
    Matrix (Fin d) (Fin d) ℂ := A.submatrix s.succAbove r.succAbove

theorem normalSliceMatrix_det_norm (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (r s : Fin (d + 1)) (hrow : ∀ j, A s j = if j = r then 1 else 0) :
    ‖(normalSliceMatrix A r s).det‖ = ‖A.det‖ := by
  have hdet : A.det = (-1 : ℂ) ^ (s.val + r.val) * (normalSliceMatrix A r s).det := by
    rw [Matrix.det_succ_row A s,Finset.sum_eq_single r]
    · rw [hrow r,if_pos rfl,mul_one]
      rfl
    · intro j _ hj
      rw [hrow j,if_neg hj,mul_zero,zero_mul]
    · simp
  rw [hdet,norm_mul,norm_pow]
  simp

def normalSliceDerivative (T : ComplexModel (d + 1) →L[ℂ] ComplexModel (d + 1))
    (r s : Fin (d + 1)) : ComplexModel d →L[ℂ] ComplexModel d :=
  (parameterDelete s).comp (T.comp (parameterZeroInsert r))

theorem normalSliceDerivative_toMatrix (T : ComplexModel (d + 1) →L[ℂ] ComplexModel (d + 1))
    (r s : Fin (d + 1)) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin d) ℂ).toBasis (EuclideanSpace.basisFun (Fin d) ℂ).toBasis
      (normalSliceDerivative T r s).toLinearMap =
      normalSliceMatrix
        (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis
          (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis T.toLinearMap) r s := by
  have hI (j : Fin d) : parameterZeroInsert r (EuclideanSpace.single j 1) =
      EuclideanSpace.single (r.succAbove j) 1 := by
    ext l
    rcases Fin.eq_self_or_eq_succAbove r l with rfl | ⟨k,rfl⟩ <;>
      simp [parameterZeroInsert]
  ext i j
  simp only [LinearMap.toMatrix_apply,normalSliceMatrix,Matrix.submatrix_apply,
    OrthonormalBasis.coe_toBasis,OrthonormalBasis.coe_toBasis_repr_apply,EuclideanSpace.basisFun_apply,EuclideanSpace.basisFun_repr]
  change (T (parameterZeroInsert r (EuclideanSpace.single j 1))) (s.succAbove i) =
    (T (EuclideanSpace.single (r.succAbove j) 1)) (s.succAbove i)
  rw [hI]

theorem normalSliceDerivative_det_norm (T : ComplexModel (d + 1) →L[ℂ] ComplexModel (d + 1))
    (r s : Fin (d + 1)) (hrow : ∀ v, T v s = v r) :
    ‖LinearMap.det (normalSliceDerivative T r s).toLinearMap‖ = ‖LinearMap.det T.toLinearMap‖ := by
  let b := (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis
  let A := LinearMap.toMatrix b b T.toLinearMap
  have hA : ∀ j, A s j = if j = r then 1 else 0 := by
    intro j
    change T (EuclideanSpace.single j 1) s = _
    rw [hrow]
    simp [PiLp.single_apply,eq_comm]
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin d) ℂ).toBasis,
    normalSliceDerivative_toMatrix,← LinearMap.det_toMatrix b]
  exact normalSliceMatrix_det_norm A r s hA

def normalSliceMap (F : ComplexModel (d + 1) → ComplexModel (d + 1))
    (r s : Fin (d + 1)) (z : ComplexModel d) : ComplexModel d :=
  parameterDelete s (F (parameterZeroInsert r z))

theorem normalSliceMap_hasFDerivAt {F : ComplexModel (d + 1) → ComplexModel (d + 1)}
    {T : ComplexModel (d + 1) →L[ℂ] ComplexModel (d + 1)} (r s : Fin (d + 1)) {z : ComplexModel d}
    (hF : HasFDerivAt F T (parameterZeroInsert r z)) :
    HasFDerivAt (normalSliceMap F r s) (normalSliceDerivative T r s) z :=
  (parameterDelete s).hasFDerivAt.comp z (hF.comp z (parameterZeroInsert r).hasFDerivAt)

theorem normalSliceMap_complex_det_norm {F : ComplexModel (d + 1) → ComplexModel (d + 1)}
    (r s : Fin (d + 1)) {z : ComplexModel d}
    (hF : DifferentiableAt ℂ F (parameterZeroInsert r z))
    (hcoord : (fun w => F w s) =ᶠ[𝓝 (parameterZeroInsert r z)] (fun w => w r)) :
    ‖LinearMap.det (fderiv ℂ (normalSliceMap F r s) z).toLinearMap‖ =
      ‖LinearMap.det (fderiv ℂ F (parameterZeroInsert r z)).toLinearMap‖ := by
  have hD := ((EuclideanSpace.proj s : ComplexModel (d + 1) →L[ℂ] ℂ).hasFDerivAt.comp
    (parameterZeroInsert r z) hF.hasFDerivAt).congr_of_eventuallyEq hcoord.symm
  have hd := hD.unique (EuclideanSpace.proj r : ComplexModel (d + 1) →L[ℂ] ℂ).hasFDerivAt
  have hrow : ∀ v, fderiv ℂ F (parameterZeroInsert r z) v s = v r := fun v => DFunLike.congr_fun hd v
  rw [(normalSliceMap_hasFDerivAt r s hF.hasFDerivAt).fderiv]
  exact normalSliceDerivative_det_norm _ r s hrow

theorem normalSliceMap_real_abs_det {F : ComplexModel (d + 1) → ComplexModel (d + 1)}
    (r s : Fin (d + 1)) {z : ComplexModel d}
    (hF : DifferentiableAt ℂ F (parameterZeroInsert r z))
    (hcoord : (fun w => F w s) =ᶠ[𝓝 (parameterZeroInsert r z)] (fun w => w r)) :
    |LinearMap.det (fderiv ℝ (normalSliceMap F r s) z).toLinearMap| =
      ‖LinearMap.det (fderiv ℂ F (parameterZeroInsert r z)).toLinearMap‖ ^ 2 := by
  have hS := (normalSliceMap_hasFDerivAt r s hF.hasFDerivAt).differentiableAt
  rw [hS.fderiv_restrictScalars ℝ]
  change |LinearMap.det (((fderiv ℂ (normalSliceMap F r s) z).toLinearMap).restrictScalars ℝ)| = _
  rw [LinearMap.det_restrictScalars,Algebra.norm_complex_apply,
    abs_of_nonneg (Complex.normSq_nonneg _),Complex.normSq_eq_norm_sq,
    normalSliceMap_complex_det_norm r s hF hcoord]

end SGPT.Trace.BertiniUniversal
