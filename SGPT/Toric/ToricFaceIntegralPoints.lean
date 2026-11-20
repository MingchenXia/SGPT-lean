import SGPT.Toric.ToricFaceProjection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual real inverse of an integral basis preserves the literal
original integer lattice. -/
theorem integralRealBasis_inverse_integerCast
    (b : Module.Basis (Fin n) ℤ (Fin n → ℤ)) (m : Fin n → ℤ) :
    (integralRealBasis b).equivFun.symm (integerCast m) =
      integerCast (b.equivFun.symm m) := by
  apply (integralRealBasis b).equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  funext j
  change (m j : ℝ) = (integralRealBasis b).repr (integerCast (b.equivFun.symm m)) j
  rw [integralRealBasis_repr_integerCast]
  exact congrArg (fun z : ℤ => (z : ℝ)) (congrFun (b.equivFun.apply_symm_apply m) j).symm

/-- Literal integral source projection in the genuine M(σ) coordinates. -/
def toricFaceIntegralProjection (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (m : Fin n → ℤ) : Fin (toricFaceDimension J) → ℤ :=
  fun j => (originalPolytopeNativeBasis γ hs v).repr (m - v.val)
    ((Fintype.equivFin {j : Fin n // j ∉ J}).symm j).val

/-- The reverse map reconstructs an ACTUAL original integral lattice point,
using the original vertex and original integral basis. -/
def toricFaceIntegralReconstruction (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (q : Fin (toricFaceDimension J) → ℤ) : Fin n → ℤ :=
  v.val + (originalPolytopeNativeBasis γ hs v).equivFun.symm
    (fun j => if hj : j ∈ J then 0 else q ((Fintype.equivFin {j : Fin n // j ∉ J}) ⟨j, hj⟩))

/-- The real projection is the actual scalar extension of this integral map. -/
theorem toricFaceProjection_integerCast (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (m : Fin n → ℤ) :
    toricFaceProjection (hs := hs) v J (integerCast m) =
      integerCast (toricFaceIntegralProjection (hs := hs) v J m) := by
  funext j
  change (integralRealBasis (originalPolytopeNativeBasis γ hs v)).repr
    (integerCast m - integerCast v.val) _ = _
  have hcast : integerCast m - integerCast v.val = integerCast (m - v.val) := by
    ext k
    simp [integerCast]
  rw [hcast, integralRealBasis_repr_integerCast]
  rfl

/-- The real reconstruction preserves every original integral coordinate,
including the rank-zero family. -/
theorem toricFaceReconstruction_integerCast (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (q : Fin (toricFaceDimension J) → ℤ) :
    toricFaceReconstruction (hs := hs) v J (integerCast q) =
      integerCast (toricFaceIntegralReconstruction (hs := hs) v J q) := by
  let b := originalPolytopeNativeBasis γ hs v
  let t : Fin n → ℤ := fun j => if hj : j ∈ J then 0 else
    q ((Fintype.equivFin {j : Fin n // j ∉ J}) ⟨j, hj⟩)
  have hcast : (fun j => if hj : j ∈ J then (0 : ℝ) else
      integerCast q ((Fintype.equivFin {j : Fin n // j ∉ J}) ⟨j, hj⟩)) = integerCast t := by
    funext j
    by_cases hj : j ∈ J <;> simp [t, integerCast, hj]
  change integerCast v.val + (integralRealBasis b).equivFun.symm _ = integerCast (v.val + b.equivFun.symm t)
  rw [hcast, integralRealBasis_inverse_integerCast]
  ext j
  simp [integerCast]

/-- The actual integral maps are inverse in the full quotient lattice. -/
theorem toricFaceIntegralProjection_reconstruction (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (q : Fin (toricFaceDimension J) → ℤ) :
    toricFaceIntegralProjection (hs := hs) v J (toricFaceIntegralReconstruction (hs := hs) v J q) = q := by
  apply integerCast_injective
  rw [← toricFaceProjection_integerCast, ← toricFaceReconstruction_integerCast,
    toricFaceProjection_reconstruction]

/-- On the actual selected face the actual integral maps recover every full
original lattice point. -/
theorem toricFaceIntegralReconstruction_projection (v : latticePolytopeVertices γ) (J : Set (Fin n))
    {m : Fin n → ℤ} (hm : integerCast m ∈ toricNativeVertexFace (hs := hs) v J) :
    toricFaceIntegralReconstruction (hs := hs) v J (toricFaceIntegralProjection (hs := hs) v J m) = m := by
  apply integerCast_injective
  rw [← toricFaceReconstruction_integerCast, ← toricFaceProjection_integerCast,
    toricFaceReconstruction_projection v J hm]

/-- The FULL original ambient lattice-point indices lying on the actual
selected face. These are the actual homogeneous indices in the original
projective model; no sparse generator index replaces them. -/
def ToricNativeFaceFullIndex (v : latticePolytopeVertices γ) (J : Set (Fin n)) :=
  {m : latticePolytopeIntegerPoints γ // integerCast m.val ∈ toricNativeVertexFace (hs := hs) v J}

/-- Exact bijection of FULL original face lattice points and FULL original
lattice points of the constructed projected family. This supplies the actual
homogeneous index dictionary for the pending complex face realization. -/
def toricFaceFullLatticePointEquiv (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    ToricNativeFaceFullIndex (hs := hs) v J ≃
      latticePolytopeIntegerPoints (toricFaceProjectedFamily (hs := hs) v J) where
  toFun m := ⟨toricFaceIntegralProjection (hs := hs) v J m.val.val, by
    change integerCast (toricFaceIntegralProjection (hs := hs) v J m.val.val) ∈
      latticePolytope (toricFaceProjectedFamily (hs := hs) v J)
    rw [← toricFaceProjection_integerCast, ← toricFaceProjection_image_face]
    exact ⟨integerCast m.val.val, m.property, rfl⟩⟩
  invFun q := by
    have hm : integerCast (toricFaceIntegralReconstruction (hs := hs) v J q.val) ∈
        toricNativeVertexFace (hs := hs) v J := by
      rw [← toricFaceReconstruction_integerCast, ← toricFaceReconstruction_image_polytope]
      exact ⟨integerCast q.val, q.property, rfl⟩
    exact ⟨⟨toricFaceIntegralReconstruction (hs := hs) v J q.val, hm.1⟩, hm⟩
  left_inv m := by
    apply Subtype.ext
    apply Subtype.ext
    exact toricFaceIntegralReconstruction_projection (hs := hs) v J m.property
  right_inv q := by
    apply Subtype.ext
    exact toricFaceIntegralProjection_reconstruction (hs := hs) v J q.val

end SGPT.Toric
