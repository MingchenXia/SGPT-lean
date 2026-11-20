import SGPT.Toric.OriginalGuilleminCornerJacobian
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.Convex SGPT.AlmostSemigroup.Counting
open scoped BigOperators Topology Classical ContDiff Matrix
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]

/-- The actual zero coordinates of the source corner point. -/
def originalCornerZeroSet (x : Fin n → ℝ) : Set (Fin n) := {j | x j = 0}

/-- Free-coordinate positivity is produced from the actual closed corner domain. -/
theorem originalCornerFree_positive (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerDomain γ hsmooth v)
    (j : {j : Fin n // j ∉ originalCornerZeroSet x}) : 0 < x j.val :=
  lt_of_le_of_ne (hx.2 j.val) (Ne.symm j.property)

/-- Literal zero/free decomposition of the SAME actual standard-basis
Jacobian. The lower-left block is retained as the actual source submatrix. -/
theorem originalCornerJacobianMatrix_blocks (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerDomain γ hsmooth v) :
    let A := originalCornerZeroSet x
    (originalCornerJacobianMatrix γ hsmooth v x).submatrix
      (Equiv.Set.sumCompl A) (Equiv.Set.sumCompl A) =
    Matrix.fromBlocks
      (Matrix.diagonal (fun j : A =>
        Real.exp (1 + originalCornerRemainderPartial γ hsmooth v j.val x))) 0
      ((originalCornerJacobianMatrix γ hsmooth v x).submatrix
        (Subtype.val : {j : Fin n // j ∉ A} → Fin n) (Subtype.val : A → Fin n))
      (Matrix.diagonal (fun j : {j : Fin n // j ∉ A} =>
        originalGuilleminCornerMap γ hsmooth v x j.val) *
          originalCornerFreeHessianMatrix γ hsmooth v A x) := by
  dsimp only
  ext j k
  rcases j with j | j <;> rcases k with k | k
  · have hj : x j.val = 0 := j.property
    simp only [Matrix.submatrix_apply, Equiv.Set.sumCompl_apply_inl,
      Matrix.fromBlocks_apply₁₁, originalCornerJacobianMatrix_apply, hj, zero_mul, add_zero]
    by_cases h : j = k
    · subst k
      simp
    · have hval : j.val ≠ k.val := fun hval => h (Subtype.ext hval)
      simp [Matrix.diagonal, h, hval]
  · have hj : x j.val = 0 := j.property
    have hval : j.val ≠ k.val := fun h => k.property (h ▸ j.property)
    simp [Matrix.submatrix_apply, originalCornerJacobianMatrix_apply, hj, hval]
  · rfl
  · have hjpos := originalCornerFree_positive γ hsmooth v hx j
    simp only [Matrix.submatrix_apply, Equiv.Set.sumCompl_apply_inr,
      Matrix.fromBlocks_apply₂₂, Matrix.diagonal_mul, originalCornerFreeHessianMatrix,
      Matrix.add_apply, originalCornerJacobianMatrix_apply, originalGuilleminCornerMap]
    by_cases h : j = k
    · subst k
      simp only [Matrix.diagonal_apply_eq, ite_true]
      field_simp [hjpos.ne']
    · have hval : j.val ≠ k.val := fun hval => h (Subtype.ext hval)
      simp [Matrix.diagonal_apply_ne _ h, hval]
      ring

/-- Existing positive-diagonal, actual free-Q, block-triangular and reindexing
invertibility mothers manufacture invertibility at EVERY boundary stratum. -/
theorem originalCornerJacobianMatrix_isUnit (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerDomain γ hsmooth v) :
    IsUnit (originalCornerJacobianMatrix γ hsmooth v x) := by
  let A := originalCornerZeroSet x
  apply (Matrix.isUnit_submatrix_equiv (Equiv.Set.sumCompl A) (Equiv.Set.sumCompl A)).mp
  rw [originalCornerJacobianMatrix_blocks γ hsmooth v hx]
  apply Matrix.isUnit_fromBlocks_zero₁₂.mpr
  constructor
  · exact (Matrix.PosDef.diagonal (fun _ => Real.exp_pos _)).isUnit
  · apply IsUnit.mul
    · apply Matrix.PosDef.isUnit
      apply Matrix.PosDef.diagonal
      intro j
      exact (originalGuilleminCornerMap_coord_pos_iff γ hsmooth v x j.val).mpr
        (originalCornerFree_positive γ hsmooth v hx j)
    · exact originalCornerFreeHessianMatrix_isUnit γ hsmooth v A hx.1
        (originalCornerFree_positive γ hsmooth v hx)

/-- Existing standard-basis matrix readback identifies the actual linear map,
not merely its formal array. -/
theorem originalCornerJacobianMatrix_mulVec (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (x η : Fin n → ℝ) :
    originalCornerJacobianMatrix γ hsmooth v x *ᵥ η =
      originalCornerJacobian γ hsmooth v x η := by
  exact LinearMap.toMatrix'_mulVec _ _

/-- Actual matrix invertibility gives genuine bijectivity of the derivative. -/
theorem originalCornerJacobian_bijective (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerDomain γ hsmooth v) :
    Function.Bijective (originalCornerJacobian γ hsmooth v x) := by
  have hu := originalCornerJacobianMatrix_isUnit γ hsmooth v hx
  have hi := Matrix.mulVec_injective_iff_isUnit.mpr hu
  have hs := Matrix.mulVec_surjective_iff_isUnit.mpr hu
  simpa only [originalCornerJacobianMatrix_mulVec] using (show Function.Bijective
    (fun η => originalCornerJacobianMatrix γ hsmooth v x *ᵥ η) from ⟨hi, hs⟩)

/-- Genuine finite-dimensional continuity turns the produced bijective
original derivative into a continuous linear equivalence, including n=0. -/
def originalCornerJacobianEquiv (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerDomain γ hsmooth v) :
    (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
  (LinearEquiv.ofBijective (originalCornerJacobian γ hsmooth v x).toLinearMap
    (originalCornerJacobian_bijective γ hsmooth v hx)).toContinuousLinearEquiv

/-- Literal readback to the actual derivative before the inverse theorem. -/
theorem originalCornerJacobianEquiv_toContinuousLinearMap (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerDomain γ hsmooth v) :
    (originalCornerJacobianEquiv γ hsmooth v hx : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) =
      originalCornerJacobian γ hsmooth v x := rfl

end SGPT.Toric
