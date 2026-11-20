import SGPT.Toric.ToricNativeVertexFace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual finite original generators on the SAME native selected face. -/
def ToricNativeFaceGenerator (v : latticePolytopeVertices γ) (J : Set (Fin n)) :=
  {k : K // integerCast (γ k) ∈ toricNativeVertexFace (hs := hs) v J}

instance toricNativeFaceGeneratorFintype (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    Fintype (ToricNativeFaceGenerator (hs := hs) v J) := by
  unfold ToricNativeFaceGenerator
  exact Fintype.ofFinite _

instance toricNativeFaceGeneratorNonempty (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    Nonempty (ToricNativeFaceGenerator (hs := hs) v J) := by
  obtain ⟨k, hk⟩ := (isOriginalPolytopeFace_toricNativeVertexFace (hs := hs) v J).exists_original_generator
  exact ⟨⟨k, hk⟩⟩

/-- The genuine dimension is the cardinal of the complementary original
rays, with no incoming dimension or basis certificate. -/
def toricFaceDimension (J : Set (Fin n)) : ℕ := Fintype.card {j : Fin n // j ∉ J}

/-- Every projected original face generator differs from the original vertex
by an actual integral character of M(σ). -/
theorem toricNativeFaceGenerator_sub_mem_annihilator (v : latticePolytopeVertices γ)
    (J : Set (Fin n)) (k : ToricNativeFaceGenerator (hs := hs) v J) :
    γ k.val - v.val ∈ toricStratumCharacterLattice (polytopeToricRay γ hs v '' J) := by
  rintro ρ ⟨j, hj, rfl⟩
  have hz := k.property.2 j hj
  rw [integralRealBasis_repr_integerCast, integralRealBasis_repr_integerCast] at hz
  have hz' : (originalPolytopeNativeBasis γ hs v).repr (γ k.val) j =
      (originalPolytopeNativeBasis γ hs v).repr v.val j := by exact_mod_cast hz
  change intPairing (γ k.val - v.val) (polytopeToricRayGenerator γ hs v j) = 0
  rw [← basis_repr_eq_intPairing, map_sub, Finsupp.sub_apply, hz', sub_self]

/-- The literal lower-dimensional integer family is made from the ACTUAL
original face generators in the ACTUAL complementary M(σ) lattice. -/
def toricFaceProjectedFamily (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    ToricNativeFaceGenerator (hs := hs) v J → Fin (toricFaceDimension J) → ℤ :=
  fun k j => toricStratumCharacterCoordinates v J
    ⟨γ k.val - v.val, toricNativeFaceGenerator_sub_mem_annihilator v J k⟩
      ((Fintype.equivFin {j : Fin n // j ∉ J}).symm j)

/-- The actual affine source projection: translate by the original vertex,
then take the genuine original free edge coordinates. -/
def toricFaceProjection (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    (Fin n → ℝ) →ᵃ[ℝ] (Fin (toricFaceDimension J) → ℝ) where
  toFun x j := (integralRealBasis (originalPolytopeNativeBasis γ hs v)).repr
    (x - integerCast v.val) ((Fintype.equivFin {j : Fin n // j ∉ J}).symm j).val
  linear := {
    toFun x j := (integralRealBasis (originalPolytopeNativeBasis γ hs v)).repr
      x ((Fintype.equivFin {j : Fin n // j ∉ J}).symm j).val
    map_add' := by intro x y; funext j; simp only [map_add, Finsupp.add_apply, Pi.add_apply]
    map_smul' := by intro c x; funext j; simp only [map_smul, Finsupp.smul_apply, Pi.smul_apply, RingHom.id_apply] }
  map_vadd' := by
    intro x y
    funext j
    change (integralRealBasis _).repr (y + x - integerCast v.val) _ =
      (integralRealBasis _).repr y _ + (integralRealBasis _).repr (x - integerCast v.val) _
    rw [show y + x - integerCast v.val = y + (x - integerCast v.val) by abel,
      map_add, Finsupp.add_apply]

/-- Projection agrees on the nose with the independently constructed integer
family, before any convex body or target toric geometry is assigned. -/
theorem toricFaceProjection_generator (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (k : ToricNativeFaceGenerator (hs := hs) v J) :
    toricFaceProjection (hs := hs) v J (integerCast (γ k.val)) =
      integerCast (toricFaceProjectedFamily (hs := hs) v J k) := by
  funext j
  change (integralRealBasis (originalPolytopeNativeBasis γ hs v)).repr
    (integerCast (γ k.val) - integerCast v.val) _ = _
  have hcast : integerCast (γ k.val) - integerCast v.val = integerCast (γ k.val - v.val) := by
    ext i
    simp [integerCast]
  rw [hcast, integralRealBasis_repr_integerCast]
  rfl

/-- The actual finite source generators give the EXACT original selected
face, now with its native-ray subtype index. -/
theorem toricNativeVertexFace_eq_convexHull_generator (v : latticePolytopeVertices γ)
    (J : Set (Fin n)) :
    toricNativeVertexFace (hs := hs) v J =
      convexHull ℝ (Set.range (fun k : ToricNativeFaceGenerator (hs := hs) v J => integerCast (γ k.val))) := by
  apply (isOriginalPolytopeFace_toricNativeVertexFace (hs := hs) v J).eq_convexHull_original_generators.trans
  apply congrArg (convexHull ℝ)
  ext x
  constructor
  · rintro ⟨⟨k, rfl⟩, hk⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨⟨k.val, rfl⟩, k.property⟩

/-- The projected polytope is the ACTUAL image of the SAME original face.
The target is defined independently as the ordinary convex hull of the
constructed integer family; no desired source equality defines it. -/
theorem toricFaceProjection_image_face (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    toricFaceProjection (hs := hs) v J '' toricNativeVertexFace (hs := hs) v J =
      latticePolytope (toricFaceProjectedFamily (hs := hs) v J) := by
  rw [toricNativeVertexFace_eq_convexHull_generator, (toricFaceProjection (hs := hs) v J).image_convexHull]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, (toricFaceProjection_generator (hs := hs) v J k).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨integerCast (γ k.val), ⟨k, rfl⟩, toricFaceProjection_generator v J k⟩

/-- The literal reverse affine coordinates insert zero in the selected
original ray coordinates and reconstruct with the SAME original basis. -/
def toricFaceReconstruction (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (y : Fin (toricFaceDimension J) → ℝ) : Fin n → ℝ :=
  integerCast v.val + (integralRealBasis (originalPolytopeNativeBasis γ hs v)).equivFun.symm
    (fun j => if hj : j ∈ J then 0 else y ((Fintype.equivFin {j : Fin n // j ∉ J}) ⟨j, hj⟩))

/-- Both coordinate maps are genuine inverses on every free coordinate,
including empty free families. -/
theorem toricFaceProjection_reconstruction (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (y : Fin (toricFaceDimension J) → ℝ) :
    toricFaceProjection (hs := hs) v J (toricFaceReconstruction (hs := hs) v J y) = y := by
  funext j
  change (integralRealBasis (originalPolytopeNativeBasis γ hs v)).equivFun
    (integerCast v.val + _ - integerCast v.val) _ = y j
  rw [add_sub_cancel_left, LinearEquiv.apply_symm_apply]
  rw [dif_neg ((Fintype.equivFin {j : Fin n // j ∉ J}).symm j).property,
    Equiv.apply_symm_apply]

/-- On the actual original face the zero-insertion reconstruction recovers
EVERY point, rather than only its dense orbit or almost-everywhere values. -/
theorem toricFaceReconstruction_projection (v : latticePolytopeVertices γ) (J : Set (Fin n))
    {x : Fin n → ℝ} (hx : x ∈ toricNativeVertexFace (hs := hs) v J) :
    toricFaceReconstruction (hs := hs) v J (toricFaceProjection (hs := hs) v J x) = x := by
  let B := integralRealBasis (originalPolytopeNativeBasis γ hs v)
  have hcoord : (fun j => if hj : j ∈ J then (0 : ℝ) else
      toricFaceProjection (hs := hs) v J x ((Fintype.equivFin {j : Fin n // j ∉ J}) ⟨j, hj⟩)) =
      B.equivFun (x - integerCast v.val) := by
    funext j
    by_cases hj : j ∈ J
    · rw [dif_pos hj]
      change 0 = B.repr (x - integerCast v.val) j
      rw [map_sub, Finsupp.sub_apply, hx.2 j hj, sub_self]
    · rw [dif_neg hj]
      change B.repr (x - integerCast v.val)
        ((Fintype.equivFin {j : Fin n // j ∉ J}).symm
          ((Fintype.equivFin {j : Fin n // j ∉ J}) ⟨j, hj⟩)).val = _
      rw [Equiv.symm_apply_apply]
      rfl
  change integerCast v.val + B.equivFun.symm _ = x
  rw [hcoord, LinearEquiv.symm_apply_apply]
  abel

/-- The actual original face and its constructed lower-dimensional integer
polytope have a literal bijective dictionary. This is still real lattice
geometry, not a claim of the pending complex toric realization. -/
theorem toricFaceReconstruction_image_polytope (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    toricFaceReconstruction (hs := hs) v J ''
      latticePolytope (toricFaceProjectedFamily (hs := hs) v J) =
      toricNativeVertexFace (hs := hs) v J := by
  rw [← toricFaceProjection_image_face, Set.image_image]
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change toricFaceReconstruction (hs := hs) v J (toricFaceProjection (hs := hs) v J x) ∈ _
    rw [toricFaceReconstruction_projection v J hx]
    exact hx
  · intro x hx
    exact ⟨x, hx, toricFaceReconstruction_projection v J hx⟩

end SGPT.Toric
