import SGPT.Toric.ToricFaceTailOrder
import SGPT.Toric.ToricFaceOrbitClosures

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The ORIGINAL ambient index of each remaining genuine target stage. -/
def toricFaceTailAmbientIndex (e : Fin n ≃ Fin n) (i : Fin (n + 1))
    (s : Fin (toricFaceDimension (toricFlagSelectedIndices e i) + 1)) : Fin (n + 1) :=
  ⟨i.val + s.val, by
    have hd := toricFaceDimension_flagSelectedIndices e i
    have hi := i.isLt
    have hs := s.isLt
    omega⟩

/-- Every actual target tail ray lifts to the SAME remaining original
ambient ray, with its literal original order. -/
theorem toricFaceTailOrder_rayLift (v : latticePolytopeVertices γ)
    (e : Fin n ≃ Fin n) (i : Fin (n + 1))
    (j : Fin (toricFaceDimension (toricFlagSelectedIndices e i))) :
    toricFaceRayLift (hs := hs) v (toricFlagSelectedIndices e i)
      (polytopeToricRay (toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e i))
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e i))
        (toricFaceVertexEquiv (hs := hs) v (toricFlagSelectedIndices e i)
          (toricFaceBaseVertex (hs := hs) v (toricFlagSelectedIndices e i))) (toricFaceTailOrder (hs := hs) v e i j)) =
      polytopeToricRay γ hs v
        (e ⟨i.val + j.val, by have := j.isLt; have hd := toricFaceDimension_flagSelectedIndices e i; omega⟩) := by
  rw [toricFaceRayLift_native, toricFaceTailOrder_free_index]
  rfl

/-- The union of ORIGINAL σ with each actual lifted target flag prefix is
EXACTLY the original ambient prefix i+s. This is literal finite-index
splitting, including both extreme stages and every dimension0 convention. -/
theorem toricFaceRemainingFlagRays (v : latticePolytopeVertices γ)
    (e : Fin n ≃ Fin n) (i : Fin (n + 1))
    (s : Fin (toricFaceDimension (toricFlagSelectedIndices e i) + 1)) :
    (polytopeToricRay γ hs v '' toricFlagSelectedIndices e i) ∪
      toricFaceRayLift (hs := hs) v (toricFlagSelectedIndices e i) ''
        toricFlagRays
          (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e i))
          (toricFaceVertexEquiv (hs := hs) v (toricFlagSelectedIndices e i)
            (toricFaceBaseVertex (hs := hs) v (toricFlagSelectedIndices e i)))
          (toricFaceTailOrder (hs := hs) v e i) s =
      toricFlagRays hs v e (toricFaceTailAmbientIndex e i s) := by
  ext ρ
  constructor
  · rintro (⟨k, ⟨l, hl, rfl⟩, rfl⟩ | ⟨ρ, ⟨j, hj, rfl⟩, rfl⟩)
    · change l.val < i.val at hl
      exact ⟨l, by change l.val < i.val + s.val; omega, rfl⟩
    · change j.val < s.val at hj
      rw [toricFaceTailOrder_rayLift]
      refine ⟨⟨i.val + j.val, ?_⟩, ?_, rfl⟩
      · have h := j.isLt
        have hd := toricFaceDimension_flagSelectedIndices e i
        omega
      · change i.val + j.val < i.val + s.val
        omega
  · rintro ⟨l, hl, rfl⟩
    change l.val < i.val + s.val at hl
    by_cases hli : l.val < i.val
    · exact Or.inl ⟨e l, ⟨l, hli, rfl⟩, rfl⟩
    · let j : Fin (toricFaceDimension (toricFlagSelectedIndices e i)) :=
        ⟨l.val - i.val, by rw [toricFaceDimension_flagSelectedIndices e i]; omega⟩
      refine Or.inr ⟨_, ⟨j, ?_, rfl⟩, ?_⟩
      · change j.val < s.val
        dsimp only [j]
        omega
      · rw [toricFaceTailOrder_rayLift]
        congr 2
        apply Fin.ext
        dsimp only [j]
        omega

/-- The SAME original embedding identifies EVERY ENTIRE remaining native
target flag stage with the SAME original ambient Y_(i+s), pointwise. -/
theorem toricFaceNativeEmbedding_mem_remainingFlag_iff
    (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n) (i : Fin (n + 1))
    (s : Fin (toricFaceDimension (toricFlagSelectedIndices e i) + 1))
    (p : PolytopeToricVariety (toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e i))
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e i))) :
    toricFaceNativeEmbedding (hs := hs) v (toricFlagSelectedIndices e i) p ∈
        toricFlag hs v e (toricFaceTailAmbientIndex e i s) ↔
      p ∈ toricFlag
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e i))
        (toricFaceVertexEquiv (hs := hs) v (toricFlagSelectedIndices e i)
          (toricFaceBaseVertex (hs := hs) v (toricFlagSelectedIndices e i))) (toricFaceTailOrder (hs := hs) v e i) s := by
  simp only [toricFlag]
  rw [← toricFaceRemainingFlagRays v e i s]
  exact toricFaceNativeEmbedding_mem_orbitClosure_iff v (toricFlagSelectedIndices e i) _ p

/-- The ACTUAL full-carrier homeomorphism carries EVERY ENTIRE remaining
native target flag onto the SAME remaining original flag, including its
original subspace topology and literal point readback. -/
theorem toricFaceFlagHomeomorph_image_remainingFlag
    (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n) (i : Fin (n + 1))
    (s : Fin (toricFaceDimension (toricFlagSelectedIndices e i) + 1)) :
    toricFaceFlagHomeomorph (hs := hs) v e i ''
      toricFlag
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e i))
        (toricFaceVertexEquiv (hs := hs) v (toricFlagSelectedIndices e i)
          (toricFaceBaseVertex (hs := hs) v (toricFlagSelectedIndices e i))) (toricFaceTailOrder (hs := hs) v e i) s =
      {y : toricFlag hs v e i | y.val ∈ toricFlag hs v e (toricFaceTailAmbientIndex e i s)} := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (toricFaceNativeEmbedding_mem_remainingFlag_iff v e i s p).mpr hp
  · intro hy
    refine ⟨(toricFaceFlagHomeomorph (hs := hs) v e i).symm y, ?_, Homeomorph.apply_symm_apply _ y⟩
    apply (toricFaceNativeEmbedding_mem_remainingFlag_iff v e i s _).mp
    have hpoint := congrArg Subtype.val ((toricFaceFlagHomeomorph (hs := hs) v e i).apply_symm_apply y)
    change toricFaceNativeEmbedding v (toricFlagSelectedIndices e i)
      ((toricFaceFlagHomeomorph (hs := hs) v e i).symm y) = y.val at hpoint
    rw [hpoint]
    exact hy

end SGPT.Toric
