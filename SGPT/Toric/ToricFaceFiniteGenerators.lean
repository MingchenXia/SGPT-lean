import SGPT.Toric.OriginalGuilleminCoordinateFaces
import Mathlib.Analysis.Convex.KreinMilman

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators

variable {n : ℕ} {K : Type*} [Fintype K]
variable {γ : K → Fin n → ℤ}

omit [Fintype K] in
/-- An original geometric face has exactly the original extreme points
lying on it. Neither a finite generator list nor a lower-dimensional model
is assumed. -/
theorem IsOriginalPolytopeFace.extremePoints_eq_original
    {F : Set (Fin n → ℝ)} (hF : IsOriginalPolytopeFace γ F) :
    F.extremePoints ℝ = F ∩ (latticePolytope γ).extremePoints ℝ :=
  hF.isExtreme.extremePoints_eq

/-- Every original geometric face is the convex hull of those ACTUAL
original integer generators lying on it. Compact Krein-Milman is made
finite by genuine original extreme-point inclusion; this does not supply
a hypothetical face polytope. -/
theorem IsOriginalPolytopeFace.eq_convexHull_original_generators
    {F : Set (Fin n → ℝ)} (hF : IsOriginalPolytopeFace γ F) :
    F = convexHull ℝ (Set.range (fun k => integerCast (γ k)) ∩ F) := by
  let s : Set (Fin n → ℝ) := Set.range (fun k => integerCast (γ k)) ∩ F
  have hsfin : s.Finite := (Set.finite_range _).inter_of_left _
  have hext : F.extremePoints ℝ ⊆ s := by
    intro x hx
    refine ⟨?_, hx.1⟩
    exact extremePoints_convexHull_subset
      (hF.isExtreme.extremePoints_subset_extremePoints hx)
  apply Set.Subset.antisymm
  · have hclosure : F ⊆ closure (convexHull ℝ (F.extremePoints ℝ)) := by
      rw [closure_convexHull_extremePoints hF.isCompact hF.convex]
    exact hclosure.trans (closure_minimal (convexHull_mono hext) (hsfin.isClosed_convexHull ℝ))
  · exact convexHull_min (fun _ hx => hx.2) hF.convex

/-- There is an ACTUAL original finite integer generator on every nonempty
original face, even in rank zero. -/
theorem IsOriginalPolytopeFace.exists_original_generator
    {F : Set (Fin n → ℝ)} (hF : IsOriginalPolytopeFace γ F) :
    ∃ k : K, integerCast (γ k) ∈ F := by
  obtain ⟨x, hx⟩ := hF.isCompact.extremePoints_nonempty hF.nonempty
  obtain ⟨k, hk⟩ := extremePoints_convexHull_subset
    (hF.isExtreme.extremePoints_subset_extremePoints hx)
  change integerCast (γ k) = x at hk
  refine ⟨k, ?_⟩
  rw [hk]
  exact hx.1

/-- The literal finite generator index for the original selected facet
intersection. No abstract finite polytope is a field of this object. -/
def toricFaceGeneratorIndex (hs : latticePolytopeEdgeSmooth γ)
    (v : latticePolytopeVertices γ) (J : Set (Fin n)) :=
  {k : K // integerCast (γ k) ∈ originalVertexFacetIntersection γ hs v J}

/-- The original selected face really has a nonempty finite generator index. -/
theorem toricFaceGeneratorIndex_nonempty (hs : latticePolytopeEdgeSmooth γ)
    (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    Nonempty (toricFaceGeneratorIndex hs v J) := by
  obtain ⟨k, hk⟩ := (isOriginalPolytopeFace_originalVertexFacetIntersection γ hs v J).exists_original_generator
  exact ⟨⟨k, hk⟩⟩

/-- Exact source face equality, now indexed by its actual selected original
integer generators, so the lower-dimensional monomial model can be built
from original data. -/
theorem originalVertexFacetIntersection_eq_convexHull_generatorIndex
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    originalVertexFacetIntersection γ hs v J =
      convexHull ℝ (Set.range (fun k : toricFaceGeneratorIndex hs v J => integerCast (γ k.val))) := by
  apply (isOriginalPolytopeFace_originalVertexFacetIntersection γ hs v J).eq_convexHull_original_generators.trans
  apply congrArg (convexHull ℝ)
  ext x
  constructor
  · rintro ⟨⟨k, rfl⟩, hk⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨⟨k.val, rfl⟩, k.property⟩

end SGPT.Toric
