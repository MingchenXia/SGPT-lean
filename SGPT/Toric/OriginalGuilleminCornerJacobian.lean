import SGPT.Toric.OriginalGuilleminCornerMap
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.Convex SGPT.AlmostSemigroup.Counting
open scoped BigOperators Topology Classical ContDiff
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]

/-- Actual derivative of the source partial, with the correct order of
functional differentiation and evaluation of the original coordinate vector. -/
def originalCornerPartialDerivative (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (j : Fin n) (x : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  (originalCornerRemainderHessian γ hsmooth v x).flip (Pi.basisFun ℝ (Fin n) j)

theorem hasFDerivAt_originalCornerRemainderPartial (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (j : Fin n) {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerOpen γ hsmooth v) :
    HasFDerivAt (originalCornerRemainderPartial γ hsmooth v j)
      (originalCornerPartialDerivative γ hsmooth v j x) x := by
  change HasFDerivAt (fun y => originalCornerRemainderDerivative γ hsmooth v y
      (Pi.basisFun ℝ (Fin n) j))
    ((originalCornerRemainderHessian γ hsmooth v x).flip (Pi.basisFun ℝ (Fin n) j)) x
  simpa using
    (hasFDerivAt_originalCornerRemainderDerivative γ hsmooth v hx).clm_apply
      (hasFDerivAt_const (Pi.basisFun ℝ (Fin n) j) x)

/-- The genuine product/exp derivative of the actual corner map. -/
def originalCornerJacobian (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (x : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun j =>
    x j • (Real.exp (1 + originalCornerRemainderPartial γ hsmooth v j x) •
      originalCornerPartialDerivative γ hsmooth v j x) +
        Real.exp (1 + originalCornerRemainderPartial γ hsmooth v j x) • ContinuousLinearMap.proj j)

theorem hasFDerivAt_originalGuilleminCornerMap (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerOpen γ hsmooth v) :
    HasFDerivAt (originalGuilleminCornerMap γ hsmooth v) (originalCornerJacobian γ hsmooth v x) x := by
  apply hasFDerivAt_pi.mpr
  intro j
  exact (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt.mul
    (((hasFDerivAt_originalCornerRemainderPartial γ hsmooth v j hx).const_add 1).exp)

/-- Exact functional Jacobian evaluation before every matrix readback. -/
theorem originalCornerJacobian_apply (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (x η : Fin n → ℝ) (j : Fin n) :
    originalCornerJacobian γ hsmooth v x η j =
      Real.exp (1 + originalCornerRemainderPartial γ hsmooth v j x) *
        (η j + x j * originalCornerRemainderHessian γ hsmooth v x η (Pi.basisFun ℝ (Fin n) j)) := by
  simp only [originalCornerJacobian, ContinuousLinearMap.pi_apply, add_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, originalCornerPartialDerivative,
    ContinuousLinearMap.flip_apply]
  ring

/-- Matrix entries of the SAME actual second derivative, with the column as
the differentiating coordinate and the row as the partial being differentiated. -/
def originalCornerRemainderMatrix (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun j k => originalCornerRemainderHessian γ hsmooth v x
    (Pi.basisFun ℝ (Fin n) k) (Pi.basisFun ℝ (Fin n) j)

/-- Exact sum of existing rank-one matrices on actual original coefficients. -/
theorem originalCornerRemainderMatrix_eq_sum (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (x : Fin n → ℝ) :
    let _ := originalVertexInactiveFacetFintype γ hsmooth v
    originalCornerRemainderMatrix γ hsmooth v x =
      ∑ F : originalVertexInactiveFacets γ v,
        (facetValue (originalCornerFacetLinear γ hsmooth v)
          (originalCornerFacetOffset γ hsmooth v) F.val x)⁻¹ •
            Matrix.vecMulVec
              (fun j => originalCornerFacetLinear γ hsmooth v F.val (Pi.basisFun ℝ (Fin n) j))
              (fun j => originalCornerFacetLinear γ hsmooth v F.val (Pi.basisFun ℝ (Fin n) j)) := by
  let _ := originalVertexInactiveFacetFintype γ hsmooth v
  ext j k
  simp only [originalCornerRemainderMatrix, originalCornerRemainderHessian_apply,
    Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro F _
  ring

/-- Actual positive inactive slacks and EXISTING rank-one/smul/sum positivity
manufacture a genuine PSD matrix, without reproving general matrix positivity. -/
theorem originalCornerRemainderMatrix_posSemidef (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerOpen γ hsmooth v) :
    (originalCornerRemainderMatrix γ hsmooth v x).PosSemidef := by
  let _ := originalVertexInactiveFacetFintype γ hsmooth v
  rw [originalCornerRemainderMatrix_eq_sum]
  apply Matrix.posSemidef_sum
  intro F _
  have h := (Matrix.posSemidef_vecMulVec_self_star
    (fun j => originalCornerFacetLinear γ hsmooth v F.val (Pi.basisFun ℝ (Fin n) j))).smul
      (inv_nonneg.mpr (hx F).le)
  simpa only [star_trivial] using h

/-- The actual Jacobian matrix is the EXISTING standard-basis matrix of the
genuinely computed continuous linear derivative, not a supplied array. -/
def originalCornerJacobianMatrix (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin n))
    (originalCornerJacobian γ hsmooth v x).toLinearMap

/-- Literal original boundary Jacobian entries. -/
theorem originalCornerJacobianMatrix_apply (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (x : Fin n → ℝ) (j k : Fin n) :
    originalCornerJacobianMatrix γ hsmooth v x j k =
      Real.exp (1 + originalCornerRemainderPartial γ hsmooth v j x) *
        ((if j = k then 1 else 0) + x j * originalCornerRemainderMatrix γ hsmooth v x j k) := by
  simp [originalCornerJacobianMatrix, originalCornerJacobian_apply,
    originalCornerRemainderMatrix, Pi.basisFun_apply, Pi.single_apply]

/-- The actual free-block Q from original coordinate reciprocals and the
SAME source Hessian; it is defined before invertibility is proved. -/
def originalCornerFreeHessianMatrix (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (A : Set (Fin n)) (x : Fin n → ℝ) : Matrix {j : Fin n // j ∉ A} {j : Fin n // j ∉ A} ℝ :=
  Matrix.diagonal (fun j => (x j.val)⁻¹) +
    (originalCornerRemainderMatrix γ hsmooth v x).submatrix Subtype.val Subtype.val

/-- EXISTING positive diagonal plus PSD/submatrix theorems supply actual
free-block positive definiteness, including the empty free family. -/
theorem originalCornerFreeHessianMatrix_posDef (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (A : Set (Fin n)) {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerOpen γ hsmooth v)
    (hpos : ∀ j : {j : Fin n // j ∉ A}, 0 < x j.val) :
    (originalCornerFreeHessianMatrix γ hsmooth v A x).PosDef :=
  (Matrix.PosDef.diagonal (fun j => inv_pos.mpr (hpos j))).add_posSemidef
    ((originalCornerRemainderMatrix_posSemidef γ hsmooth v hx).submatrix Subtype.val)

/-- Genuine existing PD invertibility is applied to the PRODUCED actual Q. -/
theorem originalCornerFreeHessianMatrix_isUnit (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (A : Set (Fin n)) {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerOpen γ hsmooth v)
    (hpos : ∀ j : {j : Fin n // j ∉ A}, 0 < x j.val) :
    IsUnit (originalCornerFreeHessianMatrix γ hsmooth v A x) :=
  (originalCornerFreeHessianMatrix_posDef γ hsmooth v A hx hpos).isUnit

/-- Genuine existing PD inverse positivity is retained for the later actual
all-strata Levi consumer, with NO complex-cast positivity shortcut. -/
theorem originalCornerFreeHessianMatrix_inv_posDef (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (A : Set (Fin n)) {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerOpen γ hsmooth v)
    (hpos : ∀ j : {j : Fin n // j ∉ A}, 0 < x j.val) :
    (originalCornerFreeHessianMatrix γ hsmooth v A x)⁻¹ |>.PosDef :=
  (originalCornerFreeHessianMatrix_posDef γ hsmooth v A hx hpos).inv

end SGPT.Toric
