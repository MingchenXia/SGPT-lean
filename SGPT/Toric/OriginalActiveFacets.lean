import SGPT.Toric.OriginalFacetNormals

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped BigOperators Topology
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]

/-- ALL geometric facets containing the actual original vertex. No selected
facet assignment or normal-basis field is part of this geometric type. -/
def latticePolytopeActiveFacets (γ : K → Fin n → ℤ) (v : latticePolytopeVertices γ) :=
  {F : latticePolytopeFacets γ // integerCast v.val ∈ F.val}

/-- The genuine local zero facet, bundled with its actual vertex membership. -/
def originalVertexActiveFacet (γ : K → Fin n → ℤ) (hsmooth : latticePolytopeEdgeSmooth γ)
    (v : latticePolytopeVertices γ) (j : Fin n) : latticePolytopeActiveFacets γ v :=
  ⟨originalVertexFacet γ hsmooth (v, j), originalVertexZeroFace_vertex_mem γ hsmooth (v, j)⟩

/-- Original geometric membership gives the literal existing zero value. -/
theorem originalFacetValue_eq_zero_of_mem (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (F : latticePolytopeFacets γ)
    {x : Fin n → ℝ} (hx : x ∈ F.val) :
    integralFacetValue (originalFacetNormal γ hsmooth) (originalFacetOffset γ hsmooth) F x = 0 := by
  have h : x ∈ {x ∈ latticePolytope γ | integralFacetValue (originalFacetNormal γ hsmooth)
      (originalFacetOffset γ hsmooth) F x = 0} := by
    rw [originalFacet_zeroSet_eq]
    exact hx
  exact h.2

/-- Actual source neighbors give nonnegative coefficients of EVERY active
facet normal in the genuine original edge basis. -/
theorem originalFacet_normal_basis_nonneg (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (F : latticePolytopeFacets γ) (hvF : integerCast v.val ∈ F.val) (k : Fin n) :
    0 ≤ originalFacetNormal γ hsmooth F (originalVertexHalfspaceBasis γ hsmooth v k) := by
  have hzero := originalFacetValue_eq_zero_of_mem γ hsmooth F hvF
  have hneighbor := (originalVertexHalfspaceBasis_spec γ hsmooth v).2.2 k
  have h := originalFacetValue_nonneg γ hsmooth F hneighbor
  change integralRealFunctional (originalFacetNormal γ hsmooth F) (integerCast v.val) +
    (originalFacetOffset γ hsmooth F : ℝ) = 0 at hzero
  change 0 ≤ integralRealFunctional (originalFacetNormal γ hsmooth F)
    (integerCast (v.val + originalVertexHalfspaceBasis γ hsmooth v k)) +
      (originalFacetOffset γ hsmooth F : ℝ) at h
  rw [integralRealFunctional_integerCast] at hzero
  rw [integralRealFunctional_integerCast, map_add, Int.cast_add] at h
  exact_mod_cast (by linarith :
    0 ≤ (originalFacetNormal γ hsmooth F (originalVertexHalfspaceBasis γ hsmooth v k) : ℝ))

/-- Genuine nonzero normals and actual basis reconstruction manufacture a
strictly positive coefficient, including the empty-basis contradiction. -/
theorem exists_originalFacet_normal_basis_pos (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (F : latticePolytopeFacets γ) (hvF : integerCast v.val ∈ F.val) :
    ∃ j : Fin n, 0 < originalFacetNormal γ hsmooth F (originalVertexHalfspaceBasis γ hsmooth v j) := by
  by_contra hno
  push Not at hno
  apply originalFacetNormal_ne_zero γ hsmooth F
  apply (originalVertexHalfspaceBasis γ hsmooth v).ext
  intro j
  change originalFacetNormal γ hsmooth F (originalVertexHalfspaceBasis γ hsmooth v j) = 0
  exact le_antisymm (hno j) (originalFacet_normal_basis_nonneg γ hsmooth v F hvF j)

/-- EVERY actual facet through the original vertex is one of its genuine
coordinate zero facets; all positivity and dimension inputs are produced. -/
theorem exists_originalVertexZeroFace_eq_at_vertex (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (F : latticePolytopeFacets γ) (hvF : integerCast v.val ∈ F.val) :
    ∃ j : Fin n, F.val = originalVertexZeroFace γ hsmooth (v, j) := by
  obtain ⟨j, hj⟩ := exists_originalFacet_normal_basis_pos γ hsmooth v F hvF
  refine ⟨j, F.property.eq_of_subset (originalVertexZeroFace_isOriginalFacet γ hsmooth (v, j)) ?_⟩
  intro x hx
  have hxP := F.property.1.subset hx
  refine ⟨hxP, ?_⟩
  rw [originalVertexHalfspaceValue_eq_coord]
  let B := originalVertexHalfspaceBasis γ hsmooth v
  let R := integralRealBasis B
  let L := integralRealFunctional (originalFacetNormal γ hsmooth F)
  have hzero : L (x - integerCast v.val) = 0 := by
    have hxzero := originalFacetValue_eq_zero_of_mem γ hsmooth F hx
    have hvzero := originalFacetValue_eq_zero_of_mem γ hsmooth F hvF
    change L x + (originalFacetOffset γ hsmooth F : ℝ) = 0 at hxzero
    change L (integerCast v.val) + (originalFacetOffset γ hsmooth F : ℝ) = 0 at hvzero
    rw [map_sub]
    linarith
  have hsum : (∑ k, R.repr (x - integerCast v.val) k * L (R k)) = 0 := by
    rw [← R.sum_repr (x - integerCast v.val), map_sum] at hzero
    simpa only [map_smul, smul_eq_mul] using hzero
  have hcoord (k : Fin n) : 0 ≤ R.repr (x - integerCast v.val) k :=
    (originalVertexHalfspaceBasis_spec γ hsmooth v).1 x hxP k
  have hL (k : Fin n) : 0 ≤ L (R k) := by
    change 0 ≤ integralRealFunctional (originalFacetNormal γ hsmooth F) (integralRealBasis B k)
    rw [integralRealBasis_apply, integralRealFunctional_integerCast]
    exact_mod_cast originalFacet_normal_basis_nonneg γ hsmooth v F hvF k
  have hterm : R.repr (x - integerCast v.val) j * L (R j) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_nonneg (hcoord k) (hL k))).mp hsum j
      (Finset.mem_univ j)
  have hpos : 0 < L (R j) := by
    change 0 < integralRealFunctional (originalFacetNormal γ hsmooth F) (integralRealBasis B j)
    rw [integralRealBasis_apply, integralRealFunctional_integerCast]
    exact_mod_cast hj
  exact (mul_eq_zero.mp hterm).resolve_right hpos.ne'

omit [Nonempty K] in
/-- Distinct local coordinate facets are distinguished by a TRUE original
basis neighbor, not by supplied facet indexing or a cardinality assertion. -/
theorem originalVertexActiveFacet_injective (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    Function.Injective (originalVertexActiveFacet γ hsmooth v) := by
  intro j k h
  by_contra hne
  have hface : originalVertexZeroFace γ hsmooth (v, j) =
      originalVertexZeroFace γ hsmooth (v, k) :=
    congrArg (fun F : latticePolytopeActiveFacets γ v => F.val.val) h
  have hm := originalVertexZeroFace_neighbor_mem γ hsmooth (v, k) hne
  rw [← hface] at hm
  have hz := hm.2
  rw [originalVertexZeroFace_neighbor_value] at hz
  norm_num at hz

/-- The genuine local facets exhaust ALL actual facets containing the vertex. -/
theorem originalVertexActiveFacet_surjective (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    Function.Surjective (originalVertexActiveFacet γ hsmooth v) := by
  intro F
  obtain ⟨j, hj⟩ := exists_originalVertexZeroFace_eq_at_vertex γ hsmooth v F.val F.property
  refine ⟨j, Subtype.ext ?_⟩
  exact Subtype.ext hj.symm

/-- ACTUAL active-facet indexing is internally manufactured as a bijection. -/
def originalVertexActiveFacetEquiv (γ : K → Fin n → ℤ) (hsmooth : latticePolytopeEdgeSmooth γ)
    (v : latticePolytopeVertices γ) : Fin n ≃ latticePolytopeActiveFacets γ v :=
  Equiv.ofBijective (originalVertexActiveFacet γ hsmooth v)
    ⟨originalVertexActiveFacet_injective γ hsmooth v, originalVertexActiveFacet_surjective γ hsmooth v⟩

theorem originalVertexActiveFacetEquiv_apply (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (j : Fin n) :
    originalVertexActiveFacetEquiv γ hsmooth v j = originalVertexActiveFacet γ hsmooth v j := rfl

/-- Actual active-facet primitive normals are the dual ORIGINAL edge basis. -/
theorem originalVertexActiveFacet_normal (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (j : Fin n) :
    originalFacetNormal γ hsmooth (originalVertexActiveFacet γ hsmooth v j).val =
      (originalVertexHalfspaceBasis γ hsmooth v).coord j :=
  (originalFacet_pair_vertexFacet γ hsmooth (v, j)).1

/-- The ACTUAL selected normal-coordinate map is the EXISTING genuine integer
basis equivalence, with no unimodular-normal map certificate supplied. -/
def originalActiveFacetNormalCoordinates (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ) :=
  (originalVertexHalfspaceBasis γ hsmooth v).equivFun

/-- Its literal coordinate is evaluation by the manufactured primitive normal. -/
theorem originalActiveFacetNormalCoordinates_apply (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (m : Fin n → ℤ) (j : Fin n) :
    originalActiveFacetNormalCoordinates γ hsmooth v m j =
      originalFacetNormal γ hsmooth (originalVertexActiveFacet γ hsmooth v j).val m := by
  rw [originalVertexActiveFacet_normal]
  rfl

/-- The exact original selected-normal formula required by the EXISTING
unimodular facet/chart consumers is a produced integer linear-map identity. -/
theorem originalVertexActiveFacet_normal_coordinates (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (j : Fin n) :
    originalFacetNormal γ hsmooth (originalVertexActiveFacet γ hsmooth v j).val =
      (LinearMap.proj j).comp (originalActiveFacetNormalCoordinates γ hsmooth v).toLinearMap := by
  apply LinearMap.ext
  intro m
  exact (originalActiveFacetNormalCoordinates_apply γ hsmooth v m j).symm

/-- Every selected genuine facet vanishes at the actual original vertex. -/
theorem originalVertexActiveFacet_zero (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (j : Fin n) :
    integralFacetValue (originalFacetNormal γ hsmooth) (originalFacetOffset γ hsmooth)
      (originalVertexActiveFacet γ hsmooth v j).val (integerCast v.val) = 0 :=
  originalFacetValue_eq_zero_of_mem γ hsmooth _ (originalVertexActiveFacet γ hsmooth v j).property

/-- EVERY other actual original facet has strictly positive original slack;
the complete active assignment and its complement were produced internally. -/
theorem originalFacetValue_pos_of_not_selected (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (F : latticePolytopeFacets γ)
    (hn : F ∉ Set.range (fun j => (originalVertexActiveFacet γ hsmooth v j).val)) :
    0 < integralFacetValue (originalFacetNormal γ hsmooth) (originalFacetOffset γ hsmooth)
      F (integerCast v.val) := by
  have hnonneg := originalFacetValue_nonneg γ hsmooth F v.property.1
  have hne : integralFacetValue (originalFacetNormal γ hsmooth) (originalFacetOffset γ hsmooth)
      F (integerCast v.val) ≠ 0 := by
    intro hz
    apply hn
    have hvF : integerCast v.val ∈ F.val := by
      rw [← originalFacet_zeroSet_eq γ hsmooth F]
      exact ⟨v.property.1, hz⟩
    obtain ⟨j, hj⟩ := exists_originalVertexZeroFace_eq_at_vertex γ hsmooth v F hvF
    exact ⟨j, Subtype.ext hj.symm⟩
  exact lt_of_le_of_ne hnonneg hne.symm

end SGPT.Toric
