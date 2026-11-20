import SGPT.Toric.ToricFaceNativePrimitive

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The inverse ACTUAL Mσ coordinate map sends each target native primitive
vector to the SAME actual ambient free native vector, including rank zero. -/
theorem toricFaceNativePrimitive_inverse (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J) (k : Fin (toricFaceDimension J)) :
    (toricFaceCharacterCoordinates (hs := hs) v J).symm
      (originalPolytopeNativeBasis (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
        (toricFaceVertexEquiv (hs := hs) v J w) k) =
      ⟨originalPolytopeNativeBasis γ hs w.val (toricFaceNativeFreeIndex v J w k),
        toricFaceNativeFreeIndex_annihilator v J w k⟩ := by
  apply (toricFaceCharacterCoordinates (hs := hs) v J).injective
  rw [LinearEquiv.apply_symm_apply, toricFaceNativePrimitive_vector]

/-- LITERAL dual ray dictionary on EVERY original annihilator character.
The equality is derived on actual primitive bases and extended linearly;
no quotient-normal or dual-pairing certificate is assumed. -/
theorem toricFaceNativeRay_pairing (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J) (k : Fin (toricFaceDimension J))
    (m : toricStratumCharacterLattice (polytopeToricRay γ hs v '' J)) :
    intPairing (toricFaceCharacterCoordinates (hs := hs) v J m)
      (polytopeToricRayGenerator (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
        (toricFaceVertexEquiv (hs := hs) v J w) k) =
      intPairing m.val
        (polytopeToricRayGenerator γ hs w.val (toricFaceNativeFreeIndex v J w k)) := by
  let C := toricFaceCharacterCoordinates (hs := hs) v J
  let BX := originalPolytopeNativeBasis γ hs w.val
  let BY := originalPolytopeNativeBasis (toricFaceProjectedFamily (hs := hs) v J)
    (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
    (toricFaceVertexEquiv (hs := hs) v J w)
  let L : (Fin (toricFaceDimension J) → ℤ) →ₗ[ℤ] ℤ :=
    (BX.coord (toricFaceNativeFreeIndex v J w k)).comp
      ((toricStratumCharacterLattice (polytopeToricRay γ hs v '' J)).subtype.comp C.symm.toLinearMap)
  have hL : L = BY.coord k := by
    apply BY.ext
    intro l
    change BX.repr (C.symm (BY l)).val (toricFaceNativeFreeIndex v J w k) = BY.repr (BY l) k
    rw [toricFaceNativePrimitive_inverse]
    rw [Module.Basis.repr_self_apply, Module.Basis.repr_self_apply]
    congr 1
    exact propext (toricFaceNativeFreeIndex_injective v J w).eq_iff
  have h := LinearMap.congr_fun hL (C m)
  change BX.repr (C.symm (C m)).val (toricFaceNativeFreeIndex v J w k) = BY.repr (C m) k at h
  rw [LinearEquiv.symm_apply_apply] at h
  rw [basis_repr_eq_intPairing, basis_repr_eq_intPairing] at h
  exact h.symm

/-- Actual integral affine reconstruction equals the original vertex plus
the ACTUAL inverse annihilator coordinates. -/
theorem toricFaceIntegralReconstruction_eq_vertex_add
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (q : Fin (toricFaceDimension J) → ℤ) :
    toricFaceIntegralReconstruction (hs := hs) v J q =
      v.val + ((toricFaceCharacterCoordinates (hs := hs) v J).symm q).val := by
  simp [toricFaceIntegralReconstruction, toricFaceCharacterCoordinates,
    toricStratumCharacterCoordinates, LinearEquiv.piCongrLeft']

/-- Literal translation compatibility on the ENTIRE quotient lattice, not
only on the original polytope or a sparse homogeneous family. -/
theorem toricFaceIntegralReconstruction_add_character
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (q : Fin (toricFaceDimension J) → ℤ)
    (m : toricStratumCharacterLattice (polytopeToricRay γ hs v '' J)) :
    toricFaceIntegralReconstruction (hs := hs) v J (q + toricFaceCharacterCoordinates v J m) =
      toricFaceIntegralReconstruction (hs := hs) v J q + m.val := by
  rw [toricFaceIntegralReconstruction_eq_vertex_add, map_add, LinearEquiv.symm_apply_apply,
    toricFaceIntegralReconstruction_eq_vertex_add]
  change v.val + (((toricFaceCharacterCoordinates (hs := hs) v J).symm q).val + m.val) = _
  exact (add_assoc _ _ _).symm

end SGPT.Toric
