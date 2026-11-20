import SGPT.Toric.PositiveIntegralBasisPermutation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped BigOperators
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Every actual native chart-basis neighbor has nonnegative coordinates
in the ORIGINAL ALL-edge basis, because it is an ACTUAL original polytope
point. No relationship between the independent existential choices is assumed. -/
theorem originalAllEdge_coordinates_nativeBasis_nonneg
    (v : latticePolytopeVertices γ)
    (b : Module.Basis (latticePolytopeEdgesAt γ v.val) ℤ (Fin n → ℤ))
    (hmem : ∀ E, integerCast (v.val + b E) ∈ E.val) (i j : Fin n) :
    0 ≤ (latticeEdgeCoordinateBasis γ v.val b).repr (originalPolytopeNativeBasis γ hs v j) i := by
  have h := latticePolytope_originalEdge_real_coordinate_nonneg γ v b hmem (vertex_add_basis_mem hs v j) i
  have hcast : integerCast (v.val + originalPolytopeNativeBasis γ hs v j) - integerCast v.val =
      integerCast (originalPolytopeNativeBasis γ hs v j) := by
    ext k
    simp [integerCast]
  rw [hcast, integralRealBasis_repr_integerCast] at h
  exact_mod_cast h

/-- Conversely every ORIGINAL edge neighbor has nonnegative coordinates
in the ACTUAL native chart basis, by the actual ample-divisor dictionary. -/
theorem nativeBasis_coordinates_originalAllEdge_nonneg
    (v : latticePolytopeVertices γ)
    (b : Module.Basis (latticePolytopeEdgesAt γ v.val) ℤ (Fin n → ℤ))
    (hmem : ∀ E, integerCast (v.val + b E) ∈ E.val) (j i : Fin n) :
    0 ≤ (originalPolytopeNativeBasis γ hs v).repr (latticeEdgeCoordinateBasis γ v.val b i) j := by
  have hp := latticeEdgeCoordinateBasis_neighbor_mem γ v.val b hmem i
  have h := nativeBasisRealCoord_vertex_le (hs := hs) v hp j
  rw [integralRealBasis_repr_integerCast, integralRealBasis_repr_integerCast] at h
  have hZ : (originalPolytopeNativeBasis γ hs v).repr v.val j ≤
      (originalPolytopeNativeBasis γ hs v).repr (v.val + latticeEdgeCoordinateBasis γ v.val b i) j := by
    exact_mod_cast h
  rw [map_add, Finsupp.add_apply] at hZ
  omega

/-- Actual native chart coordinates enumerate the ACTUAL original edges.
The permutation is manufactured from the original smoothness hypothesis and
the two independently proved nonnegative coordinate dictionaries. -/
def nativeOriginalEdgeIndexEquiv (v : latticePolytopeVertices γ) :
    Fin n ≃ latticePolytopeEdgesAt γ v.val :=
  let b := (hs v).choose
  let hmem := (hs v).choose_spec
  (positiveIntegralBasisPermutation (latticeEdgeCoordinateBasis γ v.val b)
    (originalPolytopeNativeBasis γ hs v)
    (originalAllEdge_coordinates_nativeBasis_nonneg (hs := hs) v b hmem)
    (nativeBasis_coordinates_originalAllEdge_nonneg (hs := hs) v b hmem)).trans
    (latticeEdgeBasisIndexEquiv γ v.val b)

/-- Every native chart primitive vector is the SAME primitive vector on
its ACTUAL original edge; the original first-point property is produced. -/
theorem nativeOriginalEdgeIndexEquiv_neighbor_mem (v : latticePolytopeVertices γ) (j : Fin n) :
    integerCast (v.val + originalPolytopeNativeBasis γ hs v j) ∈
      (nativeOriginalEdgeIndexEquiv (hs := hs) v j).val := by
  let b := (hs v).choose
  let hmem := (hs v).choose_spec
  let p := positiveIntegralBasisPermutation (latticeEdgeCoordinateBasis γ v.val b)
    (originalPolytopeNativeBasis γ hs v)
    (originalAllEdge_coordinates_nativeBasis_nonneg (hs := hs) v b hmem)
    (nativeBasis_coordinates_originalAllEdge_nonneg (hs := hs) v b hmem)
  have heq := positiveIntegralBasisPermutation_apply (latticeEdgeCoordinateBasis γ v.val b)
    (originalPolytopeNativeBasis γ hs v)
    (originalAllEdge_coordinates_nativeBasis_nonneg (hs := hs) v b hmem)
    (nativeBasis_coordinates_originalAllEdge_nonneg (hs := hs) v b hmem) j
  rw [latticeEdgeCoordinateBasis_apply] at heq
  change integerCast (v.val + originalPolytopeNativeBasis γ hs v j) ∈
    (latticeEdgeBasisIndexEquiv γ v.val b (p j)).val
  rw [← heq]
  exact hmem _

/-- The ACTUAL native chart basis itself is an ORIGINAL ALL-edge basis,
with the actual edge index produced above. -/
def nativeOriginalAllEdgeBasis (v : latticePolytopeVertices γ) :
    Module.Basis (latticePolytopeEdgesAt γ v.val) ℤ (Fin n → ℤ) :=
  (originalPolytopeNativeBasis γ hs v).reindex (nativeOriginalEdgeIndexEquiv (hs := hs) v)

/-- The native ALL-edge basis retains the literal book first-point condition. -/
theorem nativeOriginalAllEdgeBasis_neighbor_mem (v : latticePolytopeVertices γ)
    (E : latticePolytopeEdgesAt γ v.val) :
    integerCast (v.val + nativeOriginalAllEdgeBasis (hs := hs) v E) ∈ E.val := by
  have h := nativeOriginalEdgeIndexEquiv_neighbor_mem (hs := hs) v
    ((nativeOriginalEdgeIndexEquiv (hs := hs) v).symm E)
  rw [Equiv.apply_symm_apply] at h
  simpa only [nativeOriginalAllEdgeBasis, Module.Basis.reindex_apply] using h

end SGPT.Toric
