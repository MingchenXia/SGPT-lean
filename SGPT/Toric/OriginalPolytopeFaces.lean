import SGPT.Toric.OriginalVertexHalfspaces
import SGPT.Convex.CommonDomainFamily

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped BigOperators Topology

variable {n : ℕ} {K : Type*}

/-- A literal original closed geometric face. No normal, exposedness, finite
index or target geometry is included in this source object. -/
def IsOriginalPolytopeFace (γ : K → Fin n → ℤ) (F : Set (Fin n → ℝ)) : Prop :=
  IsClosed F ∧ Convex ℝ F ∧ F.Nonempty ∧ IsExtreme ℝ (latticePolytope γ) F

/-- Actual intrinsic codimension one, measured in the SAME ambient space. -/
def IsOriginalPolytopeFacet (γ : K → Fin n → ℤ) (F : Set (Fin n → ℝ)) : Prop :=
  IsOriginalPolytopeFace γ F ∧
    Module.finrank ℝ (affineSpan ℝ F).direction + 1 = n

/-- ALL original geometric facets, before any finite indexing is produced. -/
def latticePolytopeFacets (γ : K → Fin n → ℤ) :=
  {F : Set (Fin n → ℝ) // IsOriginalPolytopeFacet γ F}

theorem IsOriginalPolytopeFace.isClosed {γ : K → Fin n → ℤ} {F : Set (Fin n → ℝ)}
    (hF : IsOriginalPolytopeFace γ F) : IsClosed F := hF.1

theorem IsOriginalPolytopeFace.convex {γ : K → Fin n → ℤ} {F : Set (Fin n → ℝ)}
    (hF : IsOriginalPolytopeFace γ F) : Convex ℝ F := hF.2.1

theorem IsOriginalPolytopeFace.nonempty {γ : K → Fin n → ℤ} {F : Set (Fin n → ℝ)}
    (hF : IsOriginalPolytopeFace γ F) : F.Nonempty := hF.2.2.1

theorem IsOriginalPolytopeFace.isExtreme {γ : K → Fin n → ℤ} {F : Set (Fin n → ℝ)}
    (hF : IsOriginalPolytopeFace γ F) : IsExtreme ℝ (latticePolytope γ) F := hF.2.2.2

theorem IsOriginalPolytopeFace.subset {γ : K → Fin n → ℤ} {F : Set (Fin n → ℝ)}
    (hF : IsOriginalPolytopeFace γ F) : F ⊆ latticePolytope γ := hF.isExtreme.subset

/-- Closedness inside the genuinely compact original hull gives compactness. -/
theorem IsOriginalPolytopeFace.isCompact [Fintype K] {γ : K → Fin n → ℤ} {F : Set (Fin n → ℝ)}
    (hF : IsOriginalPolytopeFace γ F) : IsCompact F :=
  (isCompact_latticePolytope γ).of_isClosed_subset hF.isClosed hF.subset

/-- Actual original neighbors and the genuine existing real basis manufacture
full affine span from the book's ALL-edge condition, including rank zero. -/
theorem affineSpan_latticePolytope_eq_top [Fintype K] [Nonempty K]
    (γ : K → Fin n → ℤ) (hsmooth : latticePolytopeEdgeSmooth γ) :
    affineSpan ℝ (latticePolytope γ) = ⊤ := by
  obtain ⟨v, hv⟩ := nonempty_latticePolytopeVertices γ
  let V : latticePolytopeVertices γ := ⟨v, hv⟩
  let B := originalVertexHalfspaceBasis γ hsmooth V
  let R := integralRealBasis B
  have hspan : Submodule.span ℝ (Set.range ((↑) : Set.range R → (Fin n → ℝ))) = ⊤ := by
    simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using R.span_eq
  have hfull := affineSpan_singleton_union_vadd_eq_top_of_span_eq_top
    (integerCast v) hspan
  have hsource : ({integerCast v} ∪ (fun z => z +ᵥ integerCast v) '' Set.range R) ⊆
      latticePolytope γ := by
    rintro x (hx | ⟨z, ⟨j, rfl⟩, rfl⟩)
    · exact (Set.mem_singleton_iff.mp hx) ▸ hv.1
    · have hneighbor := (originalVertexHalfspaceBasis_spec γ hsmooth V).2.2 j
      change integerCast (v + B j) ∈ latticePolytope γ at hneighbor
      convert hneighbor using 1
      ext i
      simp [R, integralRealBasis_apply, integerCast, vadd_eq_add, add_comm]
  have hle := affineSpan_mono ℝ hsource
  rw [hfull] at hle
  exact top_unique hle

/-- Pure existing intrinsic-interior inclusion and segment extension give the
original face saturation. No new affine-path analysis is introduced. -/
theorem IsOriginalPolytopeFace.eq_inter_affineSpan
    {γ : K → Fin n → ℤ} {F : Set (Fin n → ℝ)} (hF : IsOriginalPolytopeFace γ F) :
    F = latticePolytope γ ∩ (affineSpan ℝ F : Set (Fin n → ℝ)) := by
  apply Set.Subset.antisymm
  · exact fun x hx => ⟨hF.subset hx, subset_affineSpan ℝ F hx⟩
  · intro y hy
    obtain ⟨p, hp⟩ := hF.nonempty.intrinsicInterior hF.convex
    have hpF := intrinsicInterior_subset hp
    have hpD : p ∈ intrinsicInterior ℝ (insert y F) :=
      SGPT.Convex.mem_intrinsicInterior_of_subset_of_affineSpan_eq
        (Set.subset_insert y F) (affineSpan_insert_eq_affineSpan ℝ hy.2).symm hp
    obtain ⟨z, hz, hseg⟩ :=
      SGPT.Convex.exists_mem_openSegment_of_mem_intrinsicInterior hpD (Set.mem_insert y F)
    rcases Set.mem_insert_iff.mp hz with hzy | hz
    · rw [hzy] at hseg
      have hpy : p = y := by simpa only [openSegment_same, Set.mem_singleton_iff] using hseg
      exact hpy ▸ hpF
    · exact hF.isExtreme.left_mem_of_mem_openSegment hy.1 (hF.subset hz) hpF hseg

/-- An actual proper face avoids the ordinary interior of the SAME original
hull, by directly reusing genuine existing segment extension on that hull. -/
theorem IsOriginalPolytopeFace.disjoint_interior_of_ne
    {γ : K → Fin n → ℤ} {F : Set (Fin n → ℝ)} (hF : IsOriginalPolytopeFace γ F)
    (hne : F ≠ latticePolytope γ) : Disjoint F (interior (latticePolytope γ)) := by
  apply Set.disjoint_left.mpr
  intro p hpF hpP
  apply hne
  apply Set.Subset.antisymm hF.subset
  intro y hy
  obtain ⟨z, hz, hseg⟩ := SGPT.Convex.exists_mem_openSegment_of_mem_intrinsicInterior
    (interior_subset_intrinsicInterior (𝕜 := ℝ) hpP) hy
  exact hF.isExtreme.left_mem_of_mem_openSegment hy hz hpF hseg

/-- In rank zero the genuine codimension-one condition is impossible. -/
theorem not_isOriginalPolytopeFacet_zero {γ : K → Fin 0 → ℤ} {F : Set (Fin 0 → ℝ)} :
    ¬ IsOriginalPolytopeFacet γ F := by
  intro hF
  have hdim := hF.2
  omega

end SGPT.Toric
