import SGPT.Toric.OriginalFaceEdgeCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped BigOperators
variable {n : ℕ} {K : Type*} [Fintype K]
variable {γ : K → Fin n → ℤ}

omit [Fintype K] in
/-- An actual original face containing the original vertex and one further
point of an actual original edge contains that WHOLE edge. The endpoint and
open-segment cases are proved from the original face predicate. -/
theorem IsOriginalPolytopeEdgeAt.subset_originalFace_of_nonvertex_mem
    {F E : Set (Fin n → ℝ)} {v x : Fin n → ℝ}
    (hE : IsOriginalPolytopeEdgeAt (latticePolytope γ) v E)
    (hF : IsOriginalPolytopeFace γ F) (hv : v ∈ F)
    (hxE : x ∈ E) (hxF : x ∈ F) (hxne : x ≠ v) : E ⊆ F := by
  obtain ⟨w, hw, rfl, hext⟩ := hE
  have hwF : w ∈ F := by
    by_cases hxw : x = w
    · rw [← hxw]
      exact hxF
    · exact hF.isExtreme.right_mem_of_mem_openSegment (hF.subset hv)
        (hext.subset (right_mem_segment ℝ v w)) hxF
        (mem_openSegment_of_ne_left_right (Ne.symm hxne) (Ne.symm hxw) hxE)
  exact hF.convex.segment_subset hv hwF

omit [Fintype K] in
/-- The book's original primitive neighbor is in an actual face iff the
corresponding ENTIRE actual original edge is in that face. -/
theorem originalFace_edge_neighbor_mem_iff
    {F : Set (Fin n → ℝ)} (hF : IsOriginalPolytopeFace γ F)
    (v : latticePolytopeVertices γ) (hv : integerCast v.val ∈ F)
    (b : Module.Basis (latticePolytopeEdgesAt γ v.val) ℤ (Fin n → ℤ))
    (hmem : ∀ E, integerCast (v.val + b E) ∈ E.val)
    (E : latticePolytopeEdgesAt γ v.val) :
    integerCast (v.val + b E) ∈ F ↔ E.val ⊆ F := by
  constructor
  · intro hpoint
    apply E.property.subset_originalFace_of_nonvertex_mem hF hv (hmem E) hpoint
    intro heq
    have heq' : v.val + b E = v.val := integerCast_injective heq
    apply b.ne_zero E
    exact add_left_cancel (heq'.trans (add_zero v.val).symm)
  · intro hsub
    exact hsub (hmem E)

omit [Fintype K] in
/-- The ACTUAL edges of an original face are EXACTLY the original source
edges contained in it. Both directions retain literal segment sets and the
same original vertex; extremality is transported by its genuine order laws. -/
def originalFaceEdgeEquiv
    {F : Set (Fin n → ℝ)} (hF : IsOriginalPolytopeFace γ F)
    (v : Fin n → ℤ) :
    {E : latticePolytopeEdgesAt γ v // E.val ⊆ F} ≃
      {E : Set (Fin n → ℝ) // IsOriginalPolytopeEdgeAt F (integerCast v) E} where
  toFun E := ⟨E.val.val, by
    obtain ⟨w, hw, heq, hext⟩ := E.val.property
    exact ⟨w, hw, heq, hext.mono hF.subset E.property⟩⟩
  invFun E := ⟨⟨E.val, by
    obtain ⟨w, hw, heq, hext⟩ := E.property
    exact ⟨w, hw, heq, hF.isExtreme.trans hext⟩⟩, E.property.subset⟩
  left_inv E := by apply Subtype.ext; rfl
  right_inv E := by apply Subtype.ext; rfl

/-- Every actual face point has zero original coordinate along every edge
not contained in the face. This is the precise spanning statement used to
restrict the genuine original ALL-edge integral basis. -/
theorem originalFace_edgeCoordinate_eq_zero_of_edge_not_subset
    {F : Set (Fin n → ℝ)} (hF : IsOriginalPolytopeFace γ F)
    (v : latticePolytopeVertices γ) (hv : integerCast v.val ∈ F)
    (b : Module.Basis (latticePolytopeEdgesAt γ v.val) ℤ (Fin n → ℤ))
    (hmem : ∀ E, integerCast (v.val + b E) ∈ E.val)
    {x : Fin n → ℝ} (hx : x ∈ F) (j : Fin n)
    (hj : ¬ (latticeEdgeBasisIndexEquiv γ v.val b j).val ⊆ F) :
    (integralRealBasis (latticeEdgeCoordinateBasis γ v.val b)).repr
      (x - integerCast v.val) j = 0 := by
  apply originalFace_edgeCoordinate_eq_zero_of_neighbor_not_mem hF v hv b hmem hx j
  intro hpoint
  rw [latticeEdgeCoordinateBasis_apply] at hpoint
  exact hj ((originalFace_edge_neighbor_mem_iff hF v hv b hmem _).mp hpoint)

end SGPT.Toric
