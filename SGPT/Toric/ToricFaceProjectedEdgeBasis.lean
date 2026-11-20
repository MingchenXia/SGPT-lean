import SGPT.Toric.OriginalEdgePrimitiveUnique
import SGPT.Toric.ToricFaceSmooth

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The ACTUAL original ALL-edge basis of the actual projected face, built
by restricting the actual source edge basis to Mσ and transporting through
the actual integral lattice/ALL-edge correspondences. -/
def toricFaceProjectedAllEdgeBasis (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J)
    (b : Module.Basis (latticePolytopeEdgesAt γ w.val.val) ℤ (Fin n → ℤ))
    (hb : ∀ E, integerCast (w.val.val + b E) ∈ E.val) :
    Module.Basis (latticePolytopeEdgesAt (toricFaceProjectedFamily (hs := hs) v J)
      (toricFaceVertexEquiv (hs := hs) v J w).val) ℤ (Fin (toricFaceDimension J) → ℤ) :=
  ((toricFaceAllEdgeBasis v J w.val w.property b hb).map (toricFaceCharacterCoordinates (hs := hs) v J)).reindex
    (toricFaceAllEdgeIndexEquiv v J w b)

/-- The actual primitive vector is the SAME integral source edge vector
read in the actual Mσ coordinates; no vector correspondence is assumed. -/
theorem toricFaceProjectedAllEdgeBasis_apply (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J)
    (b : Module.Basis (latticePolytopeEdgesAt γ w.val.val) ℤ (Fin n → ℤ))
    (hb : ∀ E, integerCast (w.val.val + b E) ∈ E.val)
    (j : {j : Fin n // (latticeEdgeBasisIndexEquiv γ w.val.val b j).val ⊆
      toricNativeVertexFace (hs := hs) v J}) :
    toricFaceProjectedAllEdgeBasis v J w b hb (toricFaceAllEdgeIndexEquiv v J w b j) =
      toricFaceCharacterCoordinates (hs := hs) v J
        ⟨latticeEdgeCoordinateBasis γ w.val.val b j.val,
          toricNativeFace_edgeBasis_mem_annihilator v J w.val w.property b hb j.val j.property⟩ := by
  rw [toricFaceProjectedAllEdgeBasis, Module.Basis.reindex_apply, Equiv.symm_apply_apply,
    Module.Basis.map_apply, toricFaceAllEdgeBasis_apply]

/-- Every actual projected primitive neighbor lies on its ENTIRE actual
target edge, with the original book first-point condition. -/
theorem toricFaceProjectedAllEdgeBasis_neighbor_mem (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J)
    (b : Module.Basis (latticePolytopeEdgesAt γ w.val.val) ℤ (Fin n → ℤ))
    (hb : ∀ E, integerCast (w.val.val + b E) ∈ E.val)
    (E : latticePolytopeEdgesAt (toricFaceProjectedFamily (hs := hs) v J)
      (toricFaceVertexEquiv (hs := hs) v J w).val) :
    integerCast ((toricFaceVertexEquiv (hs := hs) v J w).val +
      toricFaceProjectedAllEdgeBasis v J w b hb E) ∈ E.val := by
  obtain ⟨j, rfl⟩ := (toricFaceAllEdgeIndexEquiv v J w b).surjective E
  rw [toricFaceProjectedAllEdgeBasis_apply]
  let m : toricStratumCharacterLattice (polytopeToricRay γ hs v '' J) :=
    ⟨latticeEdgeCoordinateBasis γ w.val.val b j.val,
      toricNativeFace_edgeBasis_mem_annihilator v J w.val w.property b hb j.val j.property⟩
  have hp : toricFaceProjection (hs := hs) v J (integerCast (w.val.val + m.val)) ∈
      (toricFaceAllEdgeIndexEquiv v J w b j).val := by
    change toricFaceProjection (hs := hs) v J (integerCast (w.val.val + m.val)) ∈
      toricFaceProjection (hs := hs) v J '' (latticeEdgeBasisIndexEquiv γ w.val.val b j.val).val
    refine ⟨integerCast (w.val.val + m.val), ?_, rfl⟩
    change integerCast (w.val.val + latticeEdgeCoordinateBasis γ w.val.val b j.val) ∈ _
    rw [latticeEdgeCoordinateBasis_apply]
    exact hb _
  rw [toricFaceProjection_integerCast, toricFaceIntegralProjection_add_character] at hp
  exact hp

/-- The chosen target native primitive vector is the SAME actual projected
source primitive edge vector, by uniqueness of the original first lattice
point on the actual edge. Independent native choices are not identified by
fiat; the genuine original first-point theorem proves the equality. -/
theorem toricFace_nativeBasis_eq_projectedPrimitive
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J)
    (b : Module.Basis (latticePolytopeEdgesAt γ w.val.val) ℤ (Fin n → ℤ))
    (hb : ∀ E, integerCast (w.val.val + b E) ∈ E.val)
    (k : Fin (toricFaceDimension J)) :
    let E := nativeOriginalEdgeIndexEquiv
      (hs := latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
      (toricFaceVertexEquiv (hs := hs) v J w) k
    let j := (toricFaceAllEdgeIndexEquiv v J w b).symm E
    toricFaceCharacterCoordinates (hs := hs) v J
      ⟨latticeEdgeCoordinateBasis γ w.val.val b j.val,
        toricNativeFace_edgeBasis_mem_annihilator v J w.val w.property b hb j.val j.property⟩ =
      originalPolytopeNativeBasis (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
        (toricFaceVertexEquiv (hs := hs) v J w) k := by
  let E := nativeOriginalEdgeIndexEquiv
    (hs := latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
    (toricFaceVertexEquiv (hs := hs) v J w) k
  let j := (toricFaceAllEdgeIndexEquiv v J w b).symm E
  change toricFaceCharacterCoordinates (hs := hs) v J
    ⟨latticeEdgeCoordinateBasis γ w.val.val b j.val,
      toricNativeFace_edgeBasis_mem_annihilator v J w.val w.property b hb j.val j.property⟩ = _
  let γY := toricFaceProjectedFamily (hs := hs) v J
  let hY := latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J
  let wY := toricFaceVertexEquiv (hs := hs) v J w
  have hu := originalEdgeBasis_primitive_unique γY wY.val
    (nativeOriginalAllEdgeBasis (hs := hY) wY) (toricFaceProjectedAllEdgeBasis v J w b hb)
    (nativeOriginalAllEdgeBasis_neighbor_mem (hs := hY) wY)
    (toricFaceProjectedAllEdgeBasis_neighbor_mem v J w b hb) E
  have hp := toricFaceProjectedAllEdgeBasis_apply v J w b hb j
  rw [Equiv.apply_symm_apply] at hp
  have hn : nativeOriginalAllEdgeBasis (hs := hY) wY E = originalPolytopeNativeBasis γY hY wY k := by
    rw [nativeOriginalAllEdgeBasis, Module.Basis.reindex_apply]
    change (originalPolytopeNativeBasis γY hY wY)
      ((nativeOriginalEdgeIndexEquiv (hs := hY) wY).symm ((nativeOriginalEdgeIndexEquiv (hs := hY) wY) k)) = _
    rw [Equiv.symm_apply_apply]
  exact hp.symm.trans (hu.symm.trans hn)

end SGPT.Toric
