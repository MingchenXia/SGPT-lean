import SGPT.Toric.ToricFaceProjectedEdgeBasis
import SGPT.Toric.ToricFaceFlagOrdering

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Every actual original face vertex has a cone containing ALL actual
source σ rays. The genuine vertex–facet incidence theorem produces the
native indices; no containing-cone presentation is assumed. -/
theorem toricNativeFace_rays_in_vertexCone (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J) :
    ∀ ρ ∈ polytopeToricRay γ hs v '' J, ∃ k,
      polytopeToricRayGenerator γ hs w.val k = ρ.val := by
  rintro ρ ⟨j, hj, rfl⟩
  have hz := w.property.2 j hj
  rw [integralRealBasis_repr_integerCast, integralRealBasis_repr_integerCast] at hz
  have hZ : (originalPolytopeNativeBasis γ hs v).repr w.val.val j =
      (originalPolytopeNativeBasis γ hs v).repr v.val j := by exact_mod_cast hz
  have hpair : intPairing (w.val.val - v.val) (polytopeToricRayGenerator γ hs v j) = 0 := by
    rw [← basis_repr_eq_intPairing, map_sub, Finsupp.sub_apply, hZ, sub_self]
  exact exists_rayGenerator_eq_of_pairing_eq_zero hpair

/-- The actual original source edge associated with an actual target native
edge, through the proved ALL-edge correspondence. -/
def toricFaceNativeSourceEdge (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J) (k : Fin (toricFaceDimension J)) :
    {E : latticePolytopeEdgesAt γ w.val.val // E.val ⊆ toricNativeVertexFace (hs := hs) v J} :=
  (toricFaceProjectedEdgeEquiv (hs := hs) v J w).symm
    (nativeOriginalEdgeIndexEquiv
      (hs := latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
      (toricFaceVertexEquiv (hs := hs) v J w) k)

/-- The actual ambient free native coordinate index associated with the
actual target native coordinate. This is built from genuine edge bijections. -/
def toricFaceNativeFreeIndex (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J) (k : Fin (toricFaceDimension J)) : Fin n :=
  (nativeOriginalEdgeIndexEquiv (hs := hs) w.val).symm (toricFaceNativeSourceEdge v J w k).val

/-- The associated actual ambient primitive vector belongs to literal Mσ,
because its genuine first neighbor and the vertex lie on the SAME face. -/
theorem toricFaceNativeFreeIndex_annihilator (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J) (k : Fin (toricFaceDimension J)) :
    originalPolytopeNativeBasis γ hs w.val (toricFaceNativeFreeIndex v J w k) ∈
      toricStratumCharacterLattice (polytopeToricRay γ hs v '' J) := by
  let E := toricFaceNativeSourceEdge (hs := hs) v J w k
  have hp := E.property (nativeOriginalAllEdgeBasis_neighbor_mem (hs := hs) w.val E.val)
  have hd := toricNativeFace_sub_mem_annihilator v J hp w.property
  rw [nativeOriginalAllEdgeBasis, Module.Basis.reindex_apply] at hd
  simpa only [add_sub_cancel_left, toricFaceNativeFreeIndex, E] using hd

/-- The associated actual source native ray is outside the original cone,
proved by literal integral duality against the just-produced annihilator vector. -/
theorem toricFaceNativeFreeIndex_ray_not_mem (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J) (k : Fin (toricFaceDimension J)) :
    polytopeToricRay γ hs w.val (toricFaceNativeFreeIndex v J w k) ∉ polytopeToricRay γ hs v '' J := by
  intro hk
  have h := toricFaceNativeFreeIndex_annihilator v J w k
    (polytopeToricRay γ hs w.val (toricFaceNativeFreeIndex v J w k)) hk
  change intPairing _ (polytopeToricRayGenerator γ hs w.val _) = 0 at h
  rw [intPairing_basis_rayGenerator, if_pos rfl] at h
  omega

/-- LITERAL original primitive-vector dictionary: the target native chart
primitive vector is the actual Mσ-coordinate image of the associated original
ambient native chart primitive vector. Original primitive uniqueness proves
this across all independent native choices. -/
theorem toricFaceNativePrimitive_vector (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J) (k : Fin (toricFaceDimension J)) :
    toricFaceCharacterCoordinates (hs := hs) v J
      ⟨originalPolytopeNativeBasis γ hs w.val (toricFaceNativeFreeIndex v J w k),
        toricFaceNativeFreeIndex_annihilator v J w k⟩ =
      originalPolytopeNativeBasis (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
        (toricFaceVertexEquiv (hs := hs) v J w) k := by
  let b := nativeOriginalAllEdgeBasis (hs := hs) w.val
  let hb := nativeOriginalAllEdgeBasis_neighbor_mem (hs := hs) w.val
  let E := nativeOriginalEdgeIndexEquiv
    (hs := latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
    (toricFaceVertexEquiv (hs := hs) v J w) k
  let j := (toricFaceAllEdgeIndexEquiv v J w b).symm E
  have hp := toricFace_nativeBasis_eq_projectedPrimitive v J w b hb k
  have hj : latticeEdgeBasisIndexEquiv γ w.val.val b j.val =
      (toricFaceNativeSourceEdge (hs := hs) v J w k).val := by
    change (latticeEdgeBasisIndexEquiv γ w.val.val b)
      ((latticeEdgeBasisIndexEquiv γ w.val.val b).symm
        (toricFaceNativeSourceEdge (hs := hs) v J w k).val) = _
    rw [Equiv.apply_symm_apply]
  have hvec : latticeEdgeCoordinateBasis γ w.val.val b j.val =
      originalPolytopeNativeBasis γ hs w.val (toricFaceNativeFreeIndex v J w k) := by
    rw [latticeEdgeCoordinateBasis_apply, hj]
    dsimp only [b]
    rw [nativeOriginalAllEdgeBasis, Module.Basis.reindex_apply]
    rfl
  have heq : (⟨latticeEdgeCoordinateBasis γ w.val.val b j.val,
      toricNativeFace_edgeBasis_mem_annihilator v J w.val w.property b hb j.val j.property⟩ :
        toricStratumCharacterLattice (polytopeToricRay γ hs v '' J)) =
      ⟨originalPolytopeNativeBasis γ hs w.val (toricFaceNativeFreeIndex v J w k),
        toricFaceNativeFreeIndex_annihilator v J w k⟩ := Subtype.ext hvec
  exact (congrArg (toricFaceCharacterCoordinates (hs := hs) v J) heq).symm.trans hp

/-- The actual free coordinate map is injective, because actual target
native primitive vectors are an integral basis. -/
theorem toricFaceNativeFreeIndex_injective (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J) :
    Function.Injective (toricFaceNativeFreeIndex (hs := hs) v J w) := by
  intro k l hkl
  apply (originalPolytopeNativeBasis (toricFaceProjectedFamily (hs := hs) v J)
    (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
    (toricFaceVertexEquiv (hs := hs) v J w)).injective
  rw [← toricFaceNativePrimitive_vector, ← toricFaceNativePrimitive_vector]
  apply congrArg (toricFaceCharacterCoordinates (hs := hs) v J)
  apply Subtype.ext
  change originalPolytopeNativeBasis γ hs w.val (toricFaceNativeFreeIndex v J w k) =
    originalPolytopeNativeBasis γ hs w.val (toricFaceNativeFreeIndex v J w l)
  exact congrArg (originalPolytopeNativeBasis γ hs w.val) hkl

/-- At every actual original face vertex, the SAME original Cartier datum
satisfies the source σ equations, for arbitrary original divisor D. -/
theorem isToricCartierDatumAlong_face_vertex (D : ToricDivisor γ hs)
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J) :
    IsToricCartierDatumAlong D (polytopeToricRay γ hs v '' J) (toricCartierDatum D w.val) := by
  intro ρ hρ
  obtain ⟨k, hk⟩ := toricNativeFace_rays_in_vertexCone v J w ρ hρ
  have hindex : polytopeToricRay γ hs w.val k = ρ := Subtype.ext hk
  rw [← hk, toricCartierDatum_pairing, hindex]

/-- The literal ORIGINAL restricted frame character m_D(w)-mσ belongs to
ACTUAL Mσ for every arbitrary original valid representative mσ. This is an
actual frame character, not yet a claim of global target Cartier coherence. -/
def toricFaceRestrictedFrameCharacter (D : ToricDivisor γ hs)
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (mσ : Fin n → ℤ) (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v '' J) mσ)
    (w : ToricNativeFaceVertex (hs := hs) v J) :
    toricStratumCharacterLattice (polytopeToricRay γ hs v '' J) :=
  ⟨toricCartierDatum D w.val - mσ,
    sub_mem_toricStratumCharacterLattice_of_Cartier_data
      (isToricCartierDatumAlong_face_vertex D v J w) hσ⟩

end SGPT.Toric
