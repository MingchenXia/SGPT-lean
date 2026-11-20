import SGPT.Toric.OriginalPolytopeFaces
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Fintype.OfMap

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped BigOperators Topology
variable {n : ℕ} {K : Type*} [Fintype K]

/-- The actual zero set of a manufactured original supporting inequality. -/
def originalVertexZeroFace (γ : K → Fin n → ℤ) (hsmooth : latticePolytopeEdgeSmooth γ)
    (ρ : originalVertexHalfspaceIndex γ) : Set (Fin n → ℝ) :=
  {x ∈ latticePolytope γ | integralFacetValue (originalVertexHalfspaceNormal γ hsmooth)
    (originalVertexHalfspaceOffset γ hsmooth) ρ x = 0}

/-- Its genuine original vertex is an actual zero point. -/
theorem originalVertexZeroFace_vertex_mem (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (ρ : originalVertexHalfspaceIndex γ) :
    integerCast ρ.1.val ∈ originalVertexZeroFace γ hsmooth ρ := by
  refine ⟨ρ.1.property.1, ?_⟩
  rw [originalVertexHalfspaceValue_eq_coord]
  simp

/-- Every actual original basis neighbor has the literal Kronecker slack. -/
theorem originalVertexZeroFace_neighbor_value (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (ρ : originalVertexHalfspaceIndex γ) (k : Fin n) :
    integralFacetValue (originalVertexHalfspaceNormal γ hsmooth)
      (originalVertexHalfspaceOffset γ hsmooth) ρ
      (integerCast (ρ.1.val + originalVertexHalfspaceBasis γ hsmooth ρ.1 k)) =
      if k = ρ.2 then 1 else 0 := by
  simp [integralFacetValue, facetValue, integralRealFunctional_integerCast,
    originalVertexHalfspaceOffset, map_add, originalVertexHalfspaceNormal_basis]

/-- The actual neighbors in every other basis direction belong to this face. -/
theorem originalVertexZeroFace_neighbor_mem (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (ρ : originalVertexHalfspaceIndex γ)
    {k : Fin n} (hk : k ≠ ρ.2) :
    integerCast (ρ.1.val + originalVertexHalfspaceBasis γ hsmooth ρ.1 k) ∈
      originalVertexZeroFace γ hsmooth ρ := by
  refine ⟨(originalVertexHalfspaceBasis_spec γ hsmooth ρ.1).2.2 k, ?_⟩
  rw [originalVertexZeroFace_neighbor_value, if_neg hk]

/-- The SAME actual zero set is the existing exposed maximizer set for the
negative genuine original normal, rather than an exposedness certificate. -/
theorem originalVertexZeroFace_eq_toExposed (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (ρ : originalVertexHalfspaceIndex γ) :
    originalVertexZeroFace γ hsmooth ρ =
      (-integralRealFunctional (originalVertexHalfspaceNormal γ hsmooth ρ)).toExposed
        (latticePolytope γ) := by
  let L := integralRealFunctional (originalVertexHalfspaceNormal γ hsmooth ρ)
  let a : ℝ := originalVertexHalfspaceOffset γ hsmooth ρ
  have hzero : L (integerCast ρ.1.val) + a = 0 :=
    (originalVertexZeroFace_vertex_mem γ hsmooth ρ).2
  ext x
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    intro y hy
    have hnonneg := latticePolytope_subset_originalVertexHalfspaces γ hsmooth hy ρ
    change 0 ≤ L y + a at hnonneg
    have hxzero : L x + a = 0 := hx.2
    change -L y ≤ -L x
    linarith
  · intro hx
    refine ⟨hx.1, ?_⟩
    have hnonneg := latticePolytope_subset_originalVertexHalfspaces γ hsmooth hx.1 ρ
    have hmax := hx.2 (integerCast ρ.1.val)
      (originalVertexZeroFace_vertex_mem γ hsmooth ρ).1
    change -L (integerCast ρ.1.val) ≤ -L x at hmax
    change 0 ≤ L x + a at hnonneg
    change L x + a = 0
    linarith

/-- Existing genuine exposed-face machinery applies to this produced set. -/
theorem originalVertexZeroFace_isExposed (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (ρ : originalVertexHalfspaceIndex γ) :
    IsExposed ℝ (latticePolytope γ) (originalVertexZeroFace γ hsmooth ρ) := by
  rw [originalVertexZeroFace_eq_toExposed]
  exact ContinuousLinearMap.toExposed.isExposed

/-- The produced zero set is a literal original closed geometric face. -/
theorem originalVertexZeroFace_isOriginalFace (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (ρ : originalVertexHalfspaceIndex γ) :
    IsOriginalPolytopeFace γ (originalVertexZeroFace γ hsmooth ρ) := by
  have h := originalVertexZeroFace_isExposed γ hsmooth ρ
  exact ⟨h.isClosed (isCompact_latticePolytope γ).isClosed,
    h.convex (convex_latticePolytope γ),
    ⟨integerCast ρ.1.val, originalVertexZeroFace_vertex_mem γ hsmooth ρ⟩, h.isExtreme⟩

/-- Actual original basis neighbors span the WHOLE original zero hyperplane. -/
theorem affineSpan_originalVertexZeroFace (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (ρ : originalVertexHalfspaceIndex γ) :
    affineSpan ℝ (originalVertexZeroFace γ hsmooth ρ) =
      AffineSubspace.mk' (integerCast ρ.1.val)
        (LinearMap.ker (integralRealFunctional (originalVertexHalfspaceNormal γ hsmooth ρ)).toLinearMap) := by
  let A := affineSpan ℝ (originalVertexZeroFace γ hsmooth ρ)
  let B := originalVertexHalfspaceBasis γ hsmooth ρ.1
  let R := integralRealBasis B
  let L := integralRealFunctional (originalVertexHalfspaceNormal γ hsmooth ρ)
  have hbase : integerCast ρ.1.val ∈ A :=
    subset_affineSpan ℝ _ (originalVertexZeroFace_vertex_mem γ hsmooth ρ)
  have hzero : L (integerCast ρ.1.val) +
      (originalVertexHalfspaceOffset γ hsmooth ρ : ℝ) = 0 :=
    (originalVertexZeroFace_vertex_mem γ hsmooth ρ).2
  apply le_antisymm
  · apply affineSpan_le.mpr
    intro x hx
    change L (x - integerCast ρ.1.val) = 0
    rw [map_sub]
    have hxzero : L x + (originalVertexHalfspaceOffset γ hsmooth ρ : ℝ) = 0 := hx.2
    linarith
  · intro x hx
    change L (x - integerCast ρ.1.val) = 0 at hx
    have hxj : R.repr (x - integerCast ρ.1.val) ρ.2 = 0 := by
      rw [← integralRealFunctional_basis_coord]
      exact hx
    have hdir (k : Fin n) (hk : k ≠ ρ.2) : R k ∈ A.direction := by
      have h := A.vsub_mem_direction
        (subset_affineSpan ℝ _ (originalVertexZeroFace_neighbor_mem γ hsmooth ρ hk)) hbase
      convert h using 1
      ext i
      simp [R, B, integralRealBasis_apply, integerCast, vsub_eq_sub]
    apply (A.vsub_right_mem_direction_iff_mem hbase x).mp
    change x - integerCast ρ.1.val ∈ A.direction
    rw [← R.sum_repr (x - integerCast ρ.1.val)]
    apply A.direction.sum_mem
    intro k _
    by_cases hk : k = ρ.2
    · subst k
      rw [hxj, zero_smul]
      exact A.direction.zero_mem
    · exact A.direction.smul_mem _ (hdir k hk)

/-- The actual unit original basis evaluation manufactures normal surjectivity. -/
theorem originalVertexHalfspaceRealNormal_surjective (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (ρ : originalVertexHalfspaceIndex γ) :
    Function.Surjective (integralRealFunctional (originalVertexHalfspaceNormal γ hsmooth ρ)) := by
  intro t
  refine ⟨t • integerCast (originalVertexHalfspaceBasis γ hsmooth ρ.1 ρ.2), ?_⟩
  simp [map_smul, integralRealFunctional_integerCast, originalVertexHalfspaceNormal_basis]

/-- Existing genuine rank-nullity gives actual intrinsic codimension one. -/
theorem originalVertexZeroFace_isOriginalFacet (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (ρ : originalVertexHalfspaceIndex γ) :
    IsOriginalPolytopeFacet γ (originalVertexZeroFace γ hsmooth ρ) := by
  refine ⟨originalVertexZeroFace_isOriginalFace γ hsmooth ρ, ?_⟩
  rw [affineSpan_originalVertexZeroFace, AffineSubspace.direction_mk']
  let f := (integralRealFunctional (originalVertexHalfspaceNormal γ hsmooth ρ)).toLinearMap
  have hrange : f.range = ⊤ :=
    LinearMap.range_eq_top.mpr (originalVertexHalfspaceRealNormal_surjective γ hsmooth ρ)
  have h := f.finrank_range_add_finrank_ker
  rw [hrange] at h
  simpa [f, add_comm] using h

omit [Fintype K] in
/-- Nested ACTUAL geometric facets have equal affine directions by genuine
dimension equality, hence equal faces by the produced saturation theorem. -/
theorem IsOriginalPolytopeFacet.eq_of_subset
    {γ : K → Fin n → ℤ} {F G : Set (Fin n → ℝ)}
    (hF : IsOriginalPolytopeFacet γ F) (hG : IsOriginalPolytopeFacet γ G)
    (hFG : F ⊆ G) : F = G := by
  have hle := AffineSubspace.direction_le (affineSpan_mono ℝ hFG)
  have hdim : Module.finrank ℝ (affineSpan ℝ F).direction =
      Module.finrank ℝ (affineSpan ℝ G).direction := by
    have hFdim := hF.2
    have hGdim := hG.2
    omega
  have hdir := Submodule.eq_of_le_of_finrank_eq hle hdim
  obtain ⟨p, hp⟩ := hF.1.nonempty
  have hspan := (AffineSubspace.eq_iff_direction_eq_of_mem
    (subset_affineSpan ℝ F hp) (subset_affineSpan ℝ G (hFG hp))).mpr hdir
  rw [hF.1.eq_inter_affineSpan, hG.1.eq_inter_affineSpan, hspan]

/-- Finite strict original halfspaces give an actual ordinary neighborhood
inside the SAME source hull, using its PRODUCED exact presentation. -/
theorem mem_interior_latticePolytope_of_originalHalfspaces_pos [Nonempty K]
    (γ : K → Fin n → ℤ) (hsmooth : latticePolytopeEdgeSmooth γ) {p : Fin n → ℝ}
    (hp : ∀ ρ, 0 < integralFacetValue (originalVertexHalfspaceNormal γ hsmooth)
      (originalVertexHalfspaceOffset γ hsmooth) ρ p) :
    p ∈ interior (latticePolytope γ) := by
  let U : Set (Fin n → ℝ) := ⋂ ρ : originalVertexHalfspaceIndex γ,
    {x | 0 < integralFacetValue (originalVertexHalfspaceNormal γ hsmooth)
      (originalVertexHalfspaceOffset γ hsmooth) ρ x}
  have hopen : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro ρ
    exact isOpen_lt continuous_const
      ((integralRealFunctional (originalVertexHalfspaceNormal γ hsmooth ρ)).continuous.add
        continuous_const)
  have hpU : p ∈ U := by exact Set.mem_iInter.mpr hp
  have hUP : U ⊆ latticePolytope γ := by
    intro x hx
    rw [latticePolytope_eq_originalVertexHalfspaces γ hsmooth]
    intro ρ
    exact (Set.mem_iInter.mp hx ρ).le
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hopen.mem_nhds hpU) hUP)

/-- An actual codimension-one face cannot be the full-dimensional original hull. -/
theorem IsOriginalPolytopeFacet.ne_polytope [Nonempty K]
    {γ : K → Fin n → ℤ} (hsmooth : latticePolytopeEdgeSmooth γ)
    {F : Set (Fin n → ℝ)} (hF : IsOriginalPolytopeFacet γ F) :
    F ≠ latticePolytope γ := by
  intro heq
  have hdim := hF.2
  rw [heq, affineSpan_latticePolytope_eq_top γ hsmooth, AffineSubspace.direction_top] at hdim
  simp only [finrank_top, Module.finrank_pi, Fintype.card_fin] at hdim
  omega

/-- EVERY actual geometric facet is one of the genuinely manufactured zero
faces; no exposedness, enumeration, normal or boundary certificate is supplied. -/
theorem exists_originalVertexZeroFace_eq [Nonempty K]
    (γ : K → Fin n → ℤ) (hsmooth : latticePolytopeEdgeSmooth γ)
    {F : Set (Fin n → ℝ)} (hF : IsOriginalPolytopeFacet γ F) :
    ∃ ρ : originalVertexHalfspaceIndex γ, F = originalVertexZeroFace γ hsmooth ρ := by
  obtain ⟨p, hp⟩ := hF.1.nonempty.intrinsicInterior hF.1.convex
  have hpF := intrinsicInterior_subset hp
  have hpP := hF.1.subset hpF
  have hpnot : p ∉ interior (latticePolytope γ) :=
    Set.disjoint_left.mp (hF.1.disjoint_interior_of_ne (hF.ne_polytope hsmooth)) hpF
  have hex : ∃ ρ : originalVertexHalfspaceIndex γ,
      integralFacetValue (originalVertexHalfspaceNormal γ hsmooth)
        (originalVertexHalfspaceOffset γ hsmooth) ρ p = 0 := by
    by_contra hno
    apply hpnot
    apply mem_interior_latticePolytope_of_originalHalfspaces_pos γ hsmooth
    intro ρ
    exact lt_of_le_of_ne (latticePolytope_subset_originalVertexHalfspaces γ hsmooth hpP ρ)
      (Ne.symm (not_exists.mp hno ρ))
  obtain ⟨ρ, hzero⟩ := hex
  refine ⟨ρ, hF.eq_of_subset (originalVertexZeroFace_isOriginalFacet γ hsmooth ρ) ?_⟩
  intro y hy
  obtain ⟨z, hz, hseg⟩ :=
    SGPT.Convex.exists_mem_openSegment_of_mem_intrinsicInterior hp hy
  exact (originalVertexZeroFace_isOriginalFace γ hsmooth ρ).isExtreme.left_mem_of_mem_openSegment
    (hF.1.subset hy) (hF.1.subset hz) ⟨hpP, hzero⟩ hseg

/-- The actual raw finite halfspace family maps to ALL actual source facets. -/
def originalVertexFacet (γ : K → Fin n → ℤ) (hsmooth : latticePolytopeEdgeSmooth γ)
    (ρ : originalVertexHalfspaceIndex γ) : latticePolytopeFacets γ :=
  ⟨originalVertexZeroFace γ hsmooth ρ, originalVertexZeroFace_isOriginalFacet γ hsmooth ρ⟩

/-- The map genuinely exhausts the actual geometric facet type. -/
theorem originalVertexFacet_surjective [Nonempty K]
    (γ : K → Fin n → ℤ) (hsmooth : latticePolytopeEdgeSmooth γ) :
    Function.Surjective (originalVertexFacet γ hsmooth) := by
  intro F
  obtain ⟨ρ, hρ⟩ := exists_originalVertexZeroFace_eq γ hsmooth F.property
  exact ⟨ρ, Subtype.ext hρ.symm⟩

/-- Finiteness of ALL actual geometric facets is an OUTPUT of the genuine
source surjection; smoothness is not a field of the geometric facet type. -/
@[instance_reducible] def originalPolytopeFacetFintype [Nonempty K]
    (γ : K → Fin n → ℤ) (hsmooth : latticePolytopeEdgeSmooth γ) :
    Fintype (latticePolytopeFacets γ) := by
  classical
  exact Fintype.ofSurjective (originalVertexFacet γ hsmooth)
    (originalVertexFacet_surjective γ hsmooth)

omit [Fintype K] in
/-- Rank zero has no actual geometric facets. -/
theorem latticePolytopeFacets_zero_isEmpty (γ : K → Fin 0 → ℤ) :
    IsEmpty (latticePolytopeFacets γ) :=
  ⟨fun F => not_isOriginalPolytopeFacet_zero F.property⟩

end SGPT.Toric
