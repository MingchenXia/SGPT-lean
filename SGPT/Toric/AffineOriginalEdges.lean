import SGPT.Toric.ToricFaceProjection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators Classical

/-- Actual affine injection on a convex source transports its actual
extreme faces, with segment preimages constructed by affine segment laws. -/
theorem isExtreme_affine_image_of_injOn
    {E E' : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
    {P F : Set E} (hP : Convex ℝ P) (hF : IsExtreme ℝ P F)
    (f : E →ᵃ[ℝ] E') (hf : Set.InjOn f P) :
    IsExtreme ℝ (f '' P) (f '' F) := by
  refine ⟨Set.image_mono hF.subset, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hseg
  have himage : f z ∈ f '' openSegment ℝ x y := by
    rw [image_openSegment]
    exact hseg
  obtain ⟨z₀, hz₀, hzmap⟩ := himage
  have hz₀P : z₀ ∈ P := hP.segment_subset hx hy (openSegment_subset_segment _ _ _ hz₀)
  have hzeq : z₀ = z := hf hz₀P (hF.subset hz) hzmap
  refine ⟨x, hF.left_mem_of_mem_openSegment hx hy hz ?_, rfl⟩
  simpa only [hzeq] using hz₀

/-- The actual affine image of an original nondegenerate segment edge is an
actual edge of the image whenever the map is injective on the whole source. -/
theorem IsOriginalPolytopeEdgeAt.affine_image
    {n d : ℕ} {P E : Set (Fin n → ℝ)} {v : Fin n → ℝ}
    (hE : IsOriginalPolytopeEdgeAt P v E) (hP : Convex ℝ P)
    (f : (Fin n → ℝ) →ᵃ[ℝ] (Fin d → ℝ)) (hf : Set.InjOn f P) :
    IsOriginalPolytopeEdgeAt (f '' P) (f v) (f '' E) := by
  obtain ⟨w, hw, heq, hext⟩ := hE
  refine ⟨f w, ?_, ?_, isExtreme_affine_image_of_injOn hP hext f hf⟩
  · intro hfw
    apply hw
    exact hf (hext.subset (heq.symm ▸ right_mem_segment ℝ v w))
      (hext.subset (heq.symm ▸ left_mem_segment ℝ v w)) hfw
  · rw [heq, image_segment]

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual zero-insertion linear map in the original native coordinates. -/
def toricFaceZeroInsertion (J : Set (Fin n)) :
    (Fin (toricFaceDimension J) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun y j := if hj : j ∈ J then 0 else y ((Fintype.equivFin {j : Fin n // j ∉ J}) ⟨j, hj⟩)
  map_add' := by
    intro x y
    funext j
    by_cases hj : j ∈ J <;> simp [hj]
  map_smul' := by
    intro c x
    funext j
    by_cases hj : j ∈ J <;> simp [hj]

/-- The same all-point reconstruction, now bundled as its genuine affine map. -/
def toricFaceReconstructionAffine (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    (Fin (toricFaceDimension J) → ℝ) →ᵃ[ℝ] (Fin n → ℝ) where
  toFun := toricFaceReconstruction (hs := hs) v J
  linear := (integralRealBasis (originalPolytopeNativeBasis γ hs v)).equivFun.symm.toLinearMap.comp
    (toricFaceZeroInsertion J)
  map_vadd' := by
    intro x y
    change integerCast v.val + (integralRealBasis (originalPolytopeNativeBasis γ hs v)).equivFun.symm
      (toricFaceZeroInsertion J (y + x)) =
      (integralRealBasis (originalPolytopeNativeBasis γ hs v)).equivFun.symm (toricFaceZeroInsertion J y) +
        (integerCast v.val + (integralRealBasis (originalPolytopeNativeBasis γ hs v)).equivFun.symm
          (toricFaceZeroInsertion J x))
    rw [map_add, map_add]
    abel

/-- The projection is injective on the ENTIRE actual original face. -/
theorem toricFaceProjection_injOn_face (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    Set.InjOn (toricFaceProjection (hs := hs) v J) (toricNativeVertexFace (hs := hs) v J) := by
  intro x hx y hy hxy
  have heq := congrArg (toricFaceReconstruction (hs := hs) v J) hxy
  rwa [toricFaceReconstruction_projection v J hx, toricFaceReconstruction_projection v J hy] at heq

/-- Reconstruction is injective on its entire actual free lattice space. -/
theorem toricFaceReconstruction_injective (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    Function.Injective (toricFaceReconstruction (hs := hs) v J) := by
  intro x y hxy
  have heq := congrArg (toricFaceProjection (hs := hs) v J) hxy
  rwa [toricFaceProjection_reconstruction, toricFaceProjection_reconstruction] at heq

end SGPT.Toric
