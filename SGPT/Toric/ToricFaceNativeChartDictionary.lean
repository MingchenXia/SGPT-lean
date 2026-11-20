import SGPT.Toric.ToricFaceNativeDual
import SGPT.Toric.ToricFaceInverseRatios

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators Classical
attribute [local instance] monomialProjectiveTopology
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual target vertex homogeneous coordinate is the SAME original
ambient vertex coordinate, through the FULL lattice-point correspondence. -/
theorem toricFaceHomogeneousIndex_vertex (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J) :
    (toricFaceHomogeneousIndexEquiv (hs := hs) v J
      (originalPolytopeNativeVertexIndex (toricFaceProjectedFamily (hs := hs) v J)
        (toricFaceVertexEquiv (hs := hs) v J w))).val =
      originalPolytopeNativeVertexIndex γ w.val := by
  apply (originalPolytopeFullEnumeration γ).injective
  apply Subtype.ext
  change originalPolytopeFullExponents γ _ = originalPolytopeFullExponents γ _
  rw [toricFaceHomogeneousIndexEquiv_exponent, fullExponents_vertexIndex,
    fullExponents_vertexIndex, toricFaceVertexEquiv_val,
    toricFaceIntegralReconstruction_projection v J w.property]

/-- The actual target native neighbor homogeneous coordinate is the SAME
original ambient free native neighbor, with no chosen-coordinate equality
assumed between the independently constructed native bases. -/
theorem toricFaceHomogeneousIndex_neighbor (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J) (k : Fin (toricFaceDimension J)) :
    (toricFaceHomogeneousIndexEquiv (hs := hs) v J
      (originalPolytopeNativeNeighborIndex (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
        (toricFaceVertexEquiv (hs := hs) v J w) k)).val =
      originalPolytopeNativeNeighborIndex γ hs w.val (toricFaceNativeFreeIndex v J w k) := by
  apply (originalPolytopeFullEnumeration γ).injective
  apply Subtype.ext
  change originalPolytopeFullExponents γ _ = originalPolytopeFullExponents γ _
  rw [toricFaceHomogeneousIndexEquiv_exponent, fullExponents_neighborIndex,
    fullExponents_neighborIndex, ← toricFaceNativePrimitive_vector v J w k,
    toricFaceIntegralReconstruction_add_character, toricFaceVertexEquiv_val,
    toricFaceIntegralReconstruction_projection v J w.property]

/-- Exact equality of the original vertex-source opens under the actual
face embedding, at EVERY point including every boundary and point stratum. -/
theorem toricFaceNativeEmbedding_mem_chart_source_iff
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J)
    (p : originalPolytopeNativeSpace (toricFaceProjectedFamily (hs := hs) v J)) :
    toricFaceNativeEmbedding (hs := hs) v J p ∈ (originalPolytopeNativePiChart γ hs w.val).source ↔
      p ∈ (originalPolytopeNativePiChart (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
        (toricFaceVertexEquiv (hs := hs) v J w)).source := by
  let q := toricFaceNativeEmbedding (hs := hs) v J p
  have hrep : Projectivization.mk ℂ q.val.rep q.val.rep_nonzero =
      toricFaceProjectiveEmbedding (hs := hs) v J
        (Projectivization.mk ℂ p.val.rep p.val.rep_nonzero) := by
    rw [p.val.mk_rep]
    exact q.val.mk_rep
  rw [originalPolytopeNativePiChart_mem_source_iff γ hs w.val q _ _ q.val.mk_rep.symm,
    originalPolytopeNativePiChart_mem_source_iff _ _ _ p _ _ p.val.mk_rep.symm]
  rw [← toricFaceHomogeneousIndex_vertex (hs := hs) v J w]
  exact toricFaceProjectiveEmbedding_selected_ne_zero_iff v J _ _ _ _ hrep _

/-- On the ENTIRE actual native chart, each target native coordinate is the
literal original ambient free native coordinate. This follows from genuine
homogeneous ratios and the proved vertex/primitive-neighbor dictionary. -/
theorem toricFaceNativeEmbedding_chart_free_coordinate
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J)
    (p : originalPolytopeNativeSpace (toricFaceProjectedFamily (hs := hs) v J))
    (hp : p ∈ (originalPolytopeNativePiChart (toricFaceProjectedFamily (hs := hs) v J)
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
      (toricFaceVertexEquiv (hs := hs) v J w)).source)
    (k : Fin (toricFaceDimension J)) :
    originalPolytopeNativePiChart (toricFaceProjectedFamily (hs := hs) v J)
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
      (toricFaceVertexEquiv (hs := hs) v J w) p k =
    originalPolytopeNativePiChart γ hs w.val (toricFaceNativeEmbedding (hs := hs) v J p)
      (toricFaceNativeFreeIndex v J w k) := by
  let q := toricFaceNativeEmbedding (hs := hs) v J p
  have hq := (toricFaceNativeEmbedding_mem_chart_source_iff v J w p).mpr hp
  have htarget := toricFaceNativeEmbedding_inverse_chart_ratios v J
    (toricFaceVertexEquiv (hs := hs) v J w) p hp q.val.rep q.val.rep_nonzero q.val.mk_rep.symm
  have hsource := (originalPolytopeNativePiChart_spec γ hs w.val).2.2.2.2.2
    q hq q.val.rep q.val.rep_nonzero q.val.mk_rep.symm
  rw [htarget.2 k, toricFaceHomogeneousIndex_neighbor, toricFaceHomogeneousIndex_vertex]
  exact (hsource.2 _).symm

end SGPT.Toric
