import SGPT.Toric.AffineOriginalEdges
import SGPT.Toric.ToricFaceIntegralPoints

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Extremality of every FULL original face lattice point is preserved in
both directions by the actual affine face dictionary. The ambient original
face predicate supplies the source extremality, not a vertex certificate. -/
theorem toricFace_integralProjection_extreme_iff
    (v : latticePolytopeVertices γ) (J : Set (Fin n)) {m : Fin n → ℤ}
    (hm : integerCast m ∈ toricNativeVertexFace (hs := hs) v J) :
    integerCast (toricFaceIntegralProjection (hs := hs) v J m) ∈
        (latticePolytope (toricFaceProjectedFamily (hs := hs) v J)).extremePoints ℝ ↔
      integerCast m ∈ (latticePolytope γ).extremePoints ℝ := by
  let F := toricNativeVertexFace (hs := hs) v J
  have hF : IsOriginalPolytopeFace γ F := isOriginalPolytopeFace_toricNativeVertexFace v J
  constructor
  · intro htarget
    have hsng := isExtreme_affine_image_of_injOn
      (convex_latticePolytope (toricFaceProjectedFamily (hs := hs) v J))
      (isExtreme_singleton.mpr htarget) (toricFaceReconstructionAffine (hs := hs) v J)
      (toricFaceReconstruction_injective (hs := hs) v J).injOn
    rw [Set.image_singleton] at hsng
    change IsExtreme ℝ
      (toricFaceReconstruction (hs := hs) v J '' latticePolytope (toricFaceProjectedFamily (hs := hs) v J))
      {toricFaceReconstruction (hs := hs) v J (integerCast (toricFaceIntegralProjection (hs := hs) v J m))} at hsng
    rw [toricFaceReconstruction_image_polytope, ← toricFaceProjection_integerCast,
      toricFaceReconstruction_projection v J hm] at hsng
    exact (hF.isExtreme.trans hsng).mem_extremePoints
  · intro hsource
    have hsngF : IsExtreme ℝ F {integerCast m} :=
      (isExtreme_singleton.mpr hsource).mono hF.subset (Set.singleton_subset_iff.mpr hm)
    have hsng := isExtreme_affine_image_of_injOn hF.convex hsngF
      (toricFaceProjection (hs := hs) v J) (toricFaceProjection_injOn_face (hs := hs) v J)
    rw [Set.image_singleton, toricFaceProjection_image_face, toricFaceProjection_integerCast] at hsng
    exact hsng.mem_extremePoints

/-- The actual original vertices on the literal source face. -/
def ToricNativeFaceVertex (v : latticePolytopeVertices γ) (J : Set (Fin n)) :=
  {w : latticePolytopeVertices γ // integerCast w.val ∈ toricNativeVertexFace (hs := hs) v J}

/-- Exact actual vertex bijection for the constructed lower-dimensional
integer polytope. The same original integral maps give both directions. -/
def toricFaceVertexEquiv (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    ToricNativeFaceVertex (hs := hs) v J ≃
      latticePolytopeVertices (toricFaceProjectedFamily (hs := hs) v J) where
  toFun w := ⟨toricFaceIntegralProjection (hs := hs) v J w.val.val,
    (toricFaceFullLatticePointEquiv (hs := hs) v J ⟨⟨w.val.val, w.val.property.1⟩, w.property⟩).property,
    (toricFace_integralProjection_extreme_iff v J w.property).mpr w.val.property.2⟩
  invFun q := by
    let m := (toricFaceFullLatticePointEquiv (hs := hs) v J).symm ⟨q.val, q.property.1⟩
    have hq : toricFaceIntegralProjection (hs := hs) v J m.val.val = q.val :=
      toricFaceIntegralProjection_reconstruction (hs := hs) v J q.val
    have hmext : integerCast m.val.val ∈ (latticePolytope γ).extremePoints ℝ := by
      apply (toricFace_integralProjection_extreme_iff v J m.property).mp
      rw [hq]
      exact q.property.2
    exact ⟨⟨m.val.val, m.val.property, hmext⟩, m.property⟩
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    exact toricFaceIntegralReconstruction_projection (hs := hs) v J w.property
  right_inv q := by
    apply Subtype.ext
    exact toricFaceIntegralProjection_reconstruction (hs := hs) v J q.val

/-- The vertex dictionary is literally the original integral source
projection, before choosing a target edge basis or complex chart. -/
theorem toricFaceVertexEquiv_val (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J) :
    (toricFaceVertexEquiv (hs := hs) v J w).val =
      toricFaceIntegralProjection (hs := hs) v J w.val.val := rfl

end SGPT.Toric
