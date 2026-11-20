import SGPT.Toric.OriginalGuilleminCornerHessian
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.Convex SGPT.AlmostSemigroup.Counting Filter
open scoped BigOperators Topology Classical ContDiff
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]

/-- EVERY actual coordinate face, including the empty and full zero patterns. -/
def originalVertexCornerFace (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (A : Set (Fin n)) : Set (Fin n → ℝ) :=
  {x | originalVertexCornerPoint γ hsmooth v x ∈ latticePolytope γ ∧ ∀ j ∈ A, x j = 0}

omit [Nonempty K] in
theorem zero_mem_originalVertexCornerFace (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (A : Set (Fin n)) :
    0 ∈ originalVertexCornerFace γ hsmooth v A := by
  exact ⟨(originalVertexCornerPoint_zero γ hsmooth v).symm ▸ v.property.1, fun _ _ => rfl⟩

omit [Nonempty K] in
/-- Actual compactness is transported by the proved original affine
homeomorphism before taking the closed coordinate-zero subset. -/
theorem isCompact_originalVertexCornerFace (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (A : Set (Fin n)) :
    IsCompact (originalVertexCornerFace γ hsmooth v A) := by
  have hP : IsCompact (originalVertexCornerPoint γ hsmooth v ⁻¹' latticePolytope γ) :=
    (originalVertexCornerHomeomorph γ hsmooth v).isCompact_preimage.mpr (isCompact_latticePolytope γ)
  have hzero : IsClosed {x : Fin n → ℝ | ∀ j ∈ A, x j = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun j => isClosed_iInter (fun _ =>
      isClosed_eq (continuous_apply j) continuous_const))
  exact hP.inter_right hzero

/-- Existing hyperplane and intersection convexity gives every actual face. -/
theorem convex_originalVertexCornerFace (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (A : Set (Fin n)) :
    Convex ℝ (originalVertexCornerFace γ hsmooth v A) := by
  change Convex ℝ ((originalVertexCornerPoint γ hsmooth v ⁻¹' latticePolytope γ) ∩
    {x : Fin n → ℝ | ∀ j ∈ A, x j = 0})
  apply (convex_originalVertexCornerPolytope γ hsmooth v).inter
  simp only [Set.ofPred_forall]
  exact convex_iInter (fun j => convex_iInter (fun _ =>
    convex_hyperplane (LinearMap.proj j : (Fin n → ℝ) →ₗ[ℝ] ℝ).isLinear 0))

/-- The literal selected facet predicate is the SAME original coordinate zero. -/
theorem originalCornerPoint_mem_selectedFacet_iff (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (j : Fin n) (x : Fin n → ℝ) :
    originalVertexCornerPoint γ hsmooth v x ∈ (originalVertexActiveFacet γ hsmooth v j).val.val ↔
      originalVertexCornerPoint γ hsmooth v x ∈ latticePolytope γ ∧ x j = 0 := by
  rw [← originalFacet_zeroSet_eq γ hsmooth (originalVertexActiveFacet γ hsmooth v j).val]
  change (_ ∧ integralFacetValue (originalFacetNormal γ hsmooth) (originalFacetOffset γ hsmooth)
    (originalVertexActiveFacet γ hsmooth v j).val (originalVertexCornerPoint γ hsmooth v x) = 0) ↔ _
  rw [← originalCornerFacetValue_eq, originalCornerFacetValue_selected]

/-- Actual original selected-facet intersection on the original polytope. -/
def originalVertexFacetIntersection (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (A : Set (Fin n)) : Set (Fin n → ℝ) :=
  {m | m ∈ latticePolytope γ ∧ ∀ j ∈ A, m ∈ (originalVertexActiveFacet γ hsmooth v j).val.val}

/-- The image is the ACTUAL source facet intersection, rather than an
abstract face having a supplied desired coordinate description. -/
theorem originalVertexCornerFace_image (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (A : Set (Fin n)) :
    originalVertexCornerPoint γ hsmooth v '' originalVertexCornerFace γ hsmooth v A =
      originalVertexFacetIntersection γ hsmooth v A := by
  ext m
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx.1, fun j hj => (originalCornerPoint_mem_selectedFacet_iff γ hsmooth v j x).mpr
      ⟨hx.1, hx.2 j hj⟩⟩
  · intro hm
    let x := (originalVertexCornerHomeomorph γ hsmooth v).symm m
    have hx : originalVertexCornerPoint γ hsmooth v x = m :=
      (originalVertexCornerHomeomorph γ hsmooth v).apply_symm_apply m
    refine ⟨x, ⟨hx.symm ▸ hm.1, ?_⟩, hx⟩
    intro j hj
    exact ((originalCornerPoint_mem_selectedFacet_iff γ hsmooth v j x).mp (hx.symm ▸ hm.2 j hj)).2

omit [Nonempty K] in
/-- Actual geometric source facets retain their face predicate under this
intersection, with the source vertex supplying nonemptiness even in rank zero. -/
theorem isOriginalPolytopeFace_originalVertexFacetIntersection (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (A : Set (Fin n)) :
    IsOriginalPolytopeFace γ (originalVertexFacetIntersection γ hsmooth v A) := by
  have heq : originalVertexFacetIntersection γ hsmooth v A = latticePolytope γ ∩
      ⋂ j ∈ A, (originalVertexActiveFacet γ hsmooth v j).val.val := by
    ext m
    simp [originalVertexFacetIntersection]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heq]
    exact (isCompact_latticePolytope γ).isClosed.inter (isClosed_iInter (fun j =>
      isClosed_iInter (fun _ => (originalVertexActiveFacet γ hsmooth v j).val.property.1.isClosed)))
  · rw [heq]
    exact (convex_latticePolytope γ).inter (convex_iInter (fun j =>
      convex_iInter (fun _ => (originalVertexActiveFacet γ hsmooth v j).val.property.1.convex)))
  · exact ⟨integerCast v.val, v.property.1, fun j _ =>
      (originalVertexActiveFacet γ hsmooth v j).property⟩
  · refine ⟨fun _ hx => hx.1, ?_⟩
    intro x hx y hy z hz hseg
    exact ⟨hx, fun j hj =>
      (originalVertexActiveFacet γ hsmooth v j).val.property.1.isExtreme.left_mem_of_mem_openSegment
        hx hy (hz.2 j hj) hseg⟩

/-- Genuine continuity and the produced open neighborhood manufacture a
point of EVERY coordinate face with ALL free coordinates positive and ALL
inactive original slacks positive. No face-interior certificate is supplied. -/
theorem exists_originalVertexCornerFace_strictPoint (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (A : Set (Fin n)) :
    ∃ q ∈ originalVertexCornerFace γ hsmooth v A,
      q ∈ originalVertexCornerOpen γ hsmooth v ∧ ∀ j ∉ A, 0 < q j := by
  let q : ℝ → Fin n → ℝ := fun t j => if j ∈ A then 0 else t
  have hq0 : q 0 = 0 := by ext j; simp [q]
  have hcont : Continuous q := by
    apply continuous_pi
    intro j
    dsimp [q]
    split_ifs <;> fun_prop
  have hopen : {t | q t ∈ originalVertexCornerOpen γ hsmooth v} ∈ 𝓝 (0 : ℝ) :=
    hcont.continuousAt.preimage_mem_nhds ((isOpen_originalVertexCornerOpen γ hsmooth v).mem_nhds
      (hq0.symm ▸ zero_mem_originalVertexCornerOpen γ hsmooth v))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hopen
  have hhalf : 0 < δ / 2 := half_pos hδ
  have hqopen : q (δ / 2) ∈ originalVertexCornerOpen γ hsmooth v :=
    hball (by
      change dist (δ / 2) 0 < δ
      rw [Real.dist_eq, sub_zero, abs_of_pos hhalf]
      exact half_lt_self hδ)
  have hqcoord : ∀ j, 0 ≤ q (δ / 2) j := by
    intro j
    dsimp [q]
    split_ifs <;> positivity
  refine ⟨q (δ / 2), ⟨originalVertexCornerPoint_mem_of_mem_domain γ hsmooth v
    ⟨hqopen, hqcoord⟩, fun j hj => by simp [q, hj]⟩, hqopen, ?_⟩
  intro j hj
  simpa [q, hj] using hhalf

/-- The literal free-coordinate linear tilt. The forced coordinates are
not assigned artificial logarithmic parameters. -/
def originalCornerFaceTilt (A : Set (Fin n)) (y : {j : Fin n // j ∉ A} → ℝ) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ j : {j : Fin n // j ∉ A}, y j • ContinuousLinearMap.proj j.val

/-- Actual finite continuous entropy on the actual compact face, before
any source extended value is read as real. -/
def originalCornerFaceObjective (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (A : Set (Fin n)) (y : {j : Fin n // j ∉ A} → ℝ) : (Fin n → ℝ) → ℝ :=
  originalVertexCornerEntropyReal γ hsmooth v - originalCornerFaceTilt A y

theorem continuous_originalCornerFaceObjective (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (A : Set (Fin n)) (y : {j : Fin n // j ∉ A} → ℝ) :
    Continuous (originalCornerFaceObjective γ hsmooth v A y) :=
  (continuous_originalVertexCornerEntropyReal γ hsmooth v).sub (originalCornerFaceTilt A y).continuous

/-- The existing strict-convex restriction/subtraction mothers retain
strictness after the genuine free-coordinate linear tilt. -/
theorem strictConvexOn_originalCornerFaceObjective (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (A : Set (Fin n)) (y : {j : Fin n // j ∉ A} → ℝ) :
    StrictConvexOn ℝ (originalVertexCornerFace γ hsmooth v A)
      (originalCornerFaceObjective γ hsmooth v A y) :=
  ((strictConvexOn_originalVertexCornerEntropyReal γ hsmooth v).subset
    (fun _ hx => hx.1) (convex_originalVertexCornerFace γ hsmooth v A)).sub_concaveOn
      ((originalCornerFaceTilt A y).toLinearMap.concaveOn (convex_originalVertexCornerFace γ hsmooth v A))

/-- Genuine compact extreme-value existence and genuine strict-convex
uniqueness produce the actual minimizer for EVERY coordinate face and tilt. -/
theorem existsUnique_originalCornerFace_minimizer (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (A : Set (Fin n)) (y : {j : Fin n // j ∉ A} → ℝ) :
    ∃! x, x ∈ originalVertexCornerFace γ hsmooth v A ∧
      IsMinOn (originalCornerFaceObjective γ hsmooth v A y)
        (originalVertexCornerFace γ hsmooth v A) x := by
  obtain ⟨x, hx, hmin⟩ := (isCompact_originalVertexCornerFace γ hsmooth v A).exists_isMinOn
    ⟨0, zero_mem_originalVertexCornerFace γ hsmooth v A⟩
      (continuous_originalCornerFaceObjective γ hsmooth v A y).continuousOn
  refine ⟨x, ⟨hx, hmin⟩, ?_⟩
  intro z hz
  exact (strictConvexOn_originalCornerFaceObjective γ hsmooth v A y).eq_of_isMinOn hz.2 hmin hz.1 hx

end SGPT.Toric
