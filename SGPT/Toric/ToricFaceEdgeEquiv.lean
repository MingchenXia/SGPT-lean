import SGPT.Toric.ToricFaceVertices
import SGPT.Toric.ToricFaceDirectionLattice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- ALL actual target edges are exactly the actual original edges contained
in the face. Both directions are the SAME affine maps on the SAME segment
sets; no target edge presentation is an input. -/
def toricFaceProjectedEdgeEquiv (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J) :
    {E : latticePolytopeEdgesAt γ w.val.val // E.val ⊆ toricNativeVertexFace (hs := hs) v J} ≃
      latticePolytopeEdgesAt (toricFaceProjectedFamily (hs := hs) v J)
        (toricFaceVertexEquiv (hs := hs) v J w).val where
  toFun E := by
    let hF := isOriginalPolytopeFace_toricNativeVertexFace (hs := hs) v J
    have hE := ((originalFaceEdgeEquiv hF w.val.val) E).property.affine_image
      hF.convex (toricFaceProjection (hs := hs) v J) (toricFaceProjection_injOn_face (hs := hs) v J)
    rw [toricFaceProjection_image_face, toricFaceProjection_integerCast] at hE
    exact ⟨toricFaceProjection (hs := hs) v J '' E.val.val, hE⟩
  invFun E := by
    let hF := isOriginalPolytopeFace_toricNativeVertexFace (hs := hs) v J
    have hE := E.property.affine_image
      (convex_latticePolytope (toricFaceProjectedFamily (hs := hs) v J))
      (toricFaceReconstructionAffine (hs := hs) v J)
      (toricFaceReconstruction_injective (hs := hs) v J).injOn
    change IsOriginalPolytopeEdgeAt
      (toricFaceReconstruction (hs := hs) v J '' latticePolytope (toricFaceProjectedFamily (hs := hs) v J))
      (toricFaceReconstruction (hs := hs) v J
        (integerCast (toricFaceIntegralProjection (hs := hs) v J w.val.val)))
      (toricFaceReconstruction (hs := hs) v J '' E.val) at hE
    rw [toricFaceReconstruction_image_polytope, ← toricFaceProjection_integerCast,
      toricFaceReconstruction_projection v J w.property] at hE
    have hsub := hE.subset
    refine ⟨⟨toricFaceReconstruction (hs := hs) v J '' E.val, ?_⟩, hsub⟩
    obtain ⟨u, hu, heq, hext⟩ := hE
    exact ⟨u, hu, heq, hF.isExtreme.trans hext⟩
  left_inv E := by
    apply Subtype.ext
    apply Subtype.ext
    change toricFaceReconstruction (hs := hs) v J ''
      (toricFaceProjection (hs := hs) v J '' E.val.val) = E.val.val
    rw [Set.image_image]
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change toricFaceReconstruction (hs := hs) v J (toricFaceProjection (hs := hs) v J x) ∈ E.val.val
      rw [toricFaceReconstruction_projection v J (E.property hx)]
      exact hx
    · intro x hx
      exact ⟨x, hx, toricFaceReconstruction_projection v J (E.property hx)⟩
  right_inv E := by
    apply Subtype.ext
    change toricFaceProjection (hs := hs) v J ''
      (toricFaceReconstruction (hs := hs) v J '' E.val) = E.val
    rw [Set.image_image]
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change toricFaceProjection (hs := hs) v J (toricFaceReconstruction (hs := hs) v J x) ∈ E.val
      rw [toricFaceProjection_reconstruction]
      exact hx
    · intro x hx
      exact ⟨x, hx, toricFaceProjection_reconstruction v J x⟩

/-- Literal segment-set readback of the actual edge correspondence. -/
theorem toricFaceProjectedEdgeEquiv_val (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J)
    (E : {E : latticePolytopeEdgesAt γ w.val.val // E.val ⊆ toricNativeVertexFace (hs := hs) v J}) :
    (toricFaceProjectedEdgeEquiv (hs := hs) v J w E).val =
      toricFaceProjection (hs := hs) v J '' E.val.val := rfl

end SGPT.Toric
