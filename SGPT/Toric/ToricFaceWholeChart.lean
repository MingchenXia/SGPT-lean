import SGPT.Toric.ToricFaceNativeChartDictionary
import SGPT.Toric.ToricFaceNativeFreeCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Actual whole-chart coordinate insertion:0 on the original σ rays and
the SAME native target coordinates on all actual free original native factors. -/
def toricFaceNativeCoordinateInsertion (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J) :
    ComplexModel (toricFaceDimension J) →ₗ[ℂ] ComplexModel n where
  toFun z := modelPoint fun k => if hk : polytopeToricRay γ hs w.val k ∈ polytopeToricRay γ hs v '' J
    then 0 else z ((toricFaceNativeFreeEquiv v J w).symm ⟨k, hk⟩)
  map_add' := by
    intro a b
    ext k
    simp only [modelPoint_apply, PiLp.add_apply]
    split_ifs <;> simp
  map_smul' := by
    intro c a
    ext k
    simp only [modelPoint_apply, PiLp.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

/-- Literal free-coordinate readback for the actual whole-chart insertion. -/
theorem toricFaceNativeCoordinateInsertion_free (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J) (z : ComplexModel (toricFaceDimension J))
    (k : Fin (toricFaceDimension J)) :
    toricFaceNativeCoordinateInsertion v J w z (toricFaceNativeFreeIndex v J w k) = z k := by
  change (if hk : polytopeToricRay γ hs w.val (toricFaceNativeFreeIndex v J w k) ∈
    polytopeToricRay γ hs v '' J then 0 else
      z ((toricFaceNativeFreeEquiv v J w).symm ⟨toricFaceNativeFreeIndex v J w k, hk⟩)) = _
  rw [dif_neg (toricFaceNativeFreeIndex_ray_not_mem v J w k)]
  change z ((toricFaceNativeFreeEquiv v J w).symm ((toricFaceNativeFreeEquiv v J w) k)) = _
  rw [Equiv.symm_apply_apply]

/-- Literal zero-coordinate readback on EVERY original σ factor. -/
theorem toricFaceNativeCoordinateInsertion_selected (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J) (z : ComplexModel (toricFaceDimension J))
    (k : Fin n) (hk : polytopeToricRay γ hs w.val k ∈ polytopeToricRay γ hs v '' J) :
    toricFaceNativeCoordinateInsertion v J w z k = 0 := dif_pos hk

/-- The SAME actual embedding has literal0 on every original σ coordinate,
proved from its true orbit-closure membership in the original source chart. -/
theorem toricFaceNativeEmbedding_chart_selected_coordinate
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J)
    (p : originalPolytopeNativeSpace (toricFaceProjectedFamily (hs := hs) v J))
    (hp : p ∈ (originalPolytopeNativePiChart (toricFaceProjectedFamily (hs := hs) v J)
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
      (toricFaceVertexEquiv (hs := hs) v J w)).source)
    (k : Fin n) (hk : polytopeToricRay γ hs w.val k ∈ polytopeToricRay γ hs v '' J) :
    originalPolytopeNativeModelChart γ hs w.val (toricFaceNativeEmbedding (hs := hs) v J p) k = 0 := by
  have hq : toricFaceNativeEmbedding (hs := hs) v J p ∈
      (originalPolytopeNativeModelChart γ hs w.val).source := by
    rw [originalPolytopeNativeModelChart_source]
    exact (toricFaceNativeEmbedding_mem_chart_source_iff v J w p).mpr hp
  obtain ⟨l, hl, hz⟩ := (mem_toricOrbitClosure_iff_chart hq).mp
    (toricFaceNativeEmbedding_mem_orbitClosure v J p) (polytopeToricRay γ hs w.val k) hk
  rwa [polytopeToricRayGenerator_injective hs w.val hl] at hz

/-- The ENTIRE actual native chart map is the literal linear insertion
above, at every original boundary point. Both chosen native bases and their
free permutation are derived internally from genuine original geometry. -/
theorem toricFaceNativeEmbedding_whole_chart
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J)
    (p : originalPolytopeNativeSpace (toricFaceProjectedFamily (hs := hs) v J))
    (hp : p ∈ (originalPolytopeNativePiChart (toricFaceProjectedFamily (hs := hs) v J)
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
      (toricFaceVertexEquiv (hs := hs) v J w)).source) :
    originalPolytopeNativeModelChart γ hs w.val (toricFaceNativeEmbedding (hs := hs) v J p) =
      toricFaceNativeCoordinateInsertion v J w
        (originalPolytopeNativeModelChart (toricFaceProjectedFamily (hs := hs) v J)
          (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
          (toricFaceVertexEquiv (hs := hs) v J w) p) := by
  ext k
  by_cases hk : polytopeToricRay γ hs w.val k ∈ polytopeToricRay γ hs v '' J
  · rw [toricFaceNativeCoordinateInsertion_selected v J w _ k hk]
    exact toricFaceNativeEmbedding_chart_selected_coordinate v J w p hp k hk
  · obtain ⟨j, rfl⟩ := toricFaceNativeFreeIndex_surjective v J w k hk
    rw [toricFaceNativeCoordinateInsertion_free]
    exact (toricFaceNativeEmbedding_chart_free_coordinate v J w p hp j).symm

/-- Actual whole-chart parametrizations commute LITERALLY with the actual
embedding. This supplies the real coordinate map for restricting the SAME
smooth metric and its curvature; no chart-presentation certificate is used. -/
theorem toricFaceNativeEmbedding_vertexPoint
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J) (z : ComplexModel (toricFaceDimension J)) :
    toricFaceNativeEmbedding (hs := hs) v J
      (vertexPoint (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
        (toricFaceVertexEquiv (hs := hs) v J w) z) =
      vertexPoint hs w.val (toricFaceNativeCoordinateInsertion v J w z) := by
  let p := vertexPoint (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
    (toricFaceVertexEquiv (hs := hs) v J w) z
  have hp : p ∈ (originalPolytopeNativePiChart (toricFaceProjectedFamily (hs := hs) v J)
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
      (toricFaceVertexEquiv (hs := hs) v J w)).source := by
    rw [← originalPolytopeNativeModelChart_source]
    exact vertexPoint_mem_source _ z
  have hq : toricFaceNativeEmbedding (hs := hs) v J p ∈
      (originalPolytopeNativeModelChart γ hs w.val).source := by
    rw [originalPolytopeNativeModelChart_source]
    exact (toricFaceNativeEmbedding_mem_chart_source_iff v J w p).mpr hp
  have heq := toricFaceNativeEmbedding_whole_chart v J w p hp
  change originalPolytopeNativeModelChart γ hs w.val (toricFaceNativeEmbedding v J p) =
    toricFaceNativeCoordinateInsertion v J w
      (originalPolytopeNativeModelChart _ _ _ (vertexPoint _ _ z)) at heq
  rw [chart_vertexPoint] at heq
  exact (vertexPoint_chart w.val hq).symm.trans (congrArg (vertexPoint hs w.val) heq)

end SGPT.Toric
