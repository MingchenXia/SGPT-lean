import SGPT.Toric.ToricFaceIntegralPoints
import SGPT.Toric.OriginalFaceEdges

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Differences of any two actual original integral face points belong to
the literal source M(σ), not just those in a chosen finite generator list. -/
theorem toricNativeFace_sub_mem_annihilator (v : latticePolytopeVertices γ) (J : Set (Fin n))
    {a b : Fin n → ℤ} (ha : integerCast a ∈ toricNativeVertexFace (hs := hs) v J)
    (hb : integerCast b ∈ toricNativeVertexFace (hs := hs) v J) :
    a - b ∈ toricStratumCharacterLattice (polytopeToricRay γ hs v '' J) := by
  rintro ρ ⟨j, hj, rfl⟩
  have hzero := (ha.2 j hj).trans (hb.2 j hj).symm
  rw [integralRealBasis_repr_integerCast, integralRealBasis_repr_integerCast] at hzero
  have hz : (originalPolytopeNativeBasis γ hs v).repr a j =
      (originalPolytopeNativeBasis γ hs v).repr b j := by exact_mod_cast hzero
  change intPairing (a - b) (polytopeToricRayGenerator γ hs v j) = 0
  rw [← basis_repr_eq_intPairing, map_sub, Finsupp.sub_apply, hz, sub_self]

/-- Every actual free native edge neighbor is in the SAME original selected
face. These original integral points manufacture the full annihilator span. -/
theorem toricNativeFace_free_neighbor_mem (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (k : Fin n) (hk : k ∉ J) :
    integerCast (v.val + originalPolytopeNativeBasis γ hs v k) ∈
      toricNativeVertexFace (hs := hs) v J := by
  refine ⟨vertex_add_basis_mem hs v k, ?_⟩
  intro j hj
  have hkj : k ≠ j := by intro heq; exact hk (heq ▸ hj)
  have hcast : integerCast (v.val + originalPolytopeNativeBasis γ hs v k) =
      integerCast v.val + integralRealBasis (originalPolytopeNativeBasis γ hs v) k := by
    ext l
    simp [integralRealBasis_apply, integerCast]
  rw [hcast, map_add, Finsupp.add_apply, Module.Basis.repr_self_apply, if_neg hkj, add_zero]

/-- The literal original base vertex is on its selected face. -/
theorem toricNativeFace_vertex_mem (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    integerCast v.val ∈ toricNativeVertexFace (hs := hs) v J :=
  ⟨v.property.1, fun _ _ => rfl⟩

/-- At ANY actual face vertex, the original ALL-edge coordinates outside
the face vanish on the ENTIRE actual integral annihilator lattice. The free
native neighbors prove the converse span internally; no lattice-span or
face-presentation certificate is assumed. -/
theorem toricNativeFace_annihilator_edgeCoordinate_zero
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : latticePolytopeVertices γ)
    (hw : integerCast w.val ∈ toricNativeVertexFace (hs := hs) v J)
    (b : Module.Basis (latticePolytopeEdgesAt γ w.val) ℤ (Fin n → ℤ))
    (hmem : ∀ E, integerCast (w.val + b E) ∈ E.val)
    (j : Fin n)
    (hj : ¬ (latticeEdgeBasisIndexEquiv γ w.val b j).val ⊆ toricNativeVertexFace (hs := hs) v J)
    (m : toricStratumCharacterLattice (polytopeToricRay γ hs v '' J)) :
    (latticeEdgeCoordinateBasis γ w.val b).repr m.val j = 0 := by
  let F := toricNativeVertexFace (hs := hs) v J
  let Bw := latticeEdgeCoordinateBasis γ w.val b
  let Rw := integralRealBasis Bw
  let Bv := originalPolytopeNativeBasis γ hs v
  let Rv := integralRealBasis Bv
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := Rw.coord j
  have hF : IsOriginalPolytopeFace γ F := isOriginalPolytopeFace_toricNativeVertexFace v J
  have hzero {x : Fin n → ℝ} (hx : x ∈ F) : L (x - integerCast w.val) = 0 :=
    originalFace_edgeCoordinate_eq_zero_of_edge_not_subset hF w hw b hmem hx j hj
  have hvzero : L (integerCast v.val - integerCast w.val) = 0 :=
    hzero (toricNativeFace_vertex_mem v J)
  have hfree (k : Fin n) (hk : k ∉ J) : L (Rv k) = 0 := by
    have hp := hzero (toricNativeFace_free_neighbor_mem v J k hk)
    have hcast : integerCast (v.val + Bv k) - integerCast w.val =
        (integerCast v.val - integerCast w.val) + Rv k := by
      ext l
      simp [Rv, integralRealBasis_apply, integerCast]
      ring
    change L (integerCast (v.val + Bv k) - integerCast w.val) = 0 at hp
    rw [hcast, map_add, hvzero, zero_add] at hp
    exact hp
  have hselected (k : Fin n) (hk : k ∈ J) : Bv.repr m.val k = 0 := by
    have hm := m.property (polytopeToricRay γ hs v k) ⟨k, hk, rfl⟩
    change intPairing m.val (polytopeToricRayGenerator γ hs v k) = 0 at hm
    exact (basis_repr_eq_intPairing hs v m.val k).trans hm
  have hmzero : L (integerCast m.val) = 0 := by
    rw [← Rv.sum_repr (integerCast m.val), map_sum]
    apply Finset.sum_eq_zero
    intro k _
    rw [map_smul, smul_eq_mul]
    by_cases hk : k ∈ J
    · rw [integralRealBasis_repr_integerCast, hselected k hk, Int.cast_zero, zero_mul]
    · rw [hfree k hk, mul_zero]
  change Rw.repr (integerCast m.val) j = 0 at hmzero
  rw [integralRealBasis_repr_integerCast] at hmzero
  exact_mod_cast hmzero

/-- Every actual original edge contained in the face has its primitive
integral vector in the literal M(σ), at every actual face vertex. -/
theorem toricNativeFace_edgeBasis_mem_annihilator
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : latticePolytopeVertices γ)
    (hw : integerCast w.val ∈ toricNativeVertexFace (hs := hs) v J)
    (b : Module.Basis (latticePolytopeEdgesAt γ w.val) ℤ (Fin n → ℤ))
    (hmem : ∀ E, integerCast (w.val + b E) ∈ E.val)
    (j : Fin n)
    (hj : (latticeEdgeBasisIndexEquiv γ w.val b j).val ⊆ toricNativeVertexFace (hs := hs) v J) :
    latticeEdgeCoordinateBasis γ w.val b j ∈
      toricStratumCharacterLattice (polytopeToricRay γ hs v '' J) := by
  have hp := hj (hmem (latticeEdgeBasisIndexEquiv γ w.val b j))
  rw [← latticeEdgeCoordinateBasis_apply] at hp
  have hd := toricNativeFace_sub_mem_annihilator v J hp hw
  simpa only [add_sub_cancel_left] using hd

/-- The selected ACTUAL original edges give genuine integral coordinates
on the whole literal annihilator. Both inverses are constructed, not assumed.
The incoming b/hmem is exactly the original ALL-edge smoothness definition. -/
def toricFaceAllEdgeCharacterCoordinates
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : latticePolytopeVertices γ)
    (hw : integerCast w.val ∈ toricNativeVertexFace (hs := hs) v J)
    (b : Module.Basis (latticePolytopeEdgesAt γ w.val) ℤ (Fin n → ℤ))
    (hmem : ∀ E, integerCast (w.val + b E) ∈ E.val) :
    toricStratumCharacterLattice (polytopeToricRay γ hs v '' J) ≃ₗ[ℤ]
      ({j : Fin n // (latticeEdgeBasisIndexEquiv γ w.val b j).val ⊆
        toricNativeVertexFace (hs := hs) v J} → ℤ) := by
  classical
  let S : Set (Fin n) := {j | (latticeEdgeBasisIndexEquiv γ w.val b j).val ⊆ toricNativeVertexFace (hs := hs) v J}
  let B := latticeEdgeCoordinateBasis γ w.val b
  let extend : (S → ℤ) → Fin n → ℤ := fun f j => if hj : j ∈ S then f ⟨j, hj⟩ else 0
  have hmemExt (f : S → ℤ) : B.equivFun.symm (extend f) ∈
      toricStratumCharacterLattice (polytopeToricRay γ hs v '' J) := by
    rw [← B.sum_repr (B.equivFun.symm (extend f))]
    apply Submodule.sum_mem
    intro j _
    have hcoeff : B.repr (B.equivFun.symm (extend f)) j = extend f j :=
      congrFun (B.equivFun.apply_symm_apply (extend f)) j
    rw [hcoeff]
    by_cases hj : j ∈ S
    · exact Submodule.smul_mem _ _ (toricNativeFace_edgeBasis_mem_annihilator v J w hw b hmem j hj)
    · rw [show extend f j = 0 from dif_neg hj, zero_smul]
      exact Submodule.zero_mem _
  exact {
    toFun := fun m j => B.equivFun m.val j.val
    invFun := fun f => ⟨B.equivFun.symm (extend f), hmemExt f⟩
    left_inv := by
      intro m
      apply Subtype.ext
      apply B.equivFun.injective
      funext j
      rw [B.equivFun.apply_symm_apply]
      by_cases hj : j ∈ S
      · exact dif_pos hj
      · dsimp only [extend]
        rw [dif_neg hj]
        exact (toricNativeFace_annihilator_edgeCoordinate_zero v J w hw b hmem j hj m).symm
    right_inv := by
      intro f
      funext j
      change B.equivFun (B.equivFun.symm (extend f)) j.val = f j
      rw [B.equivFun.apply_symm_apply]
      exact dif_pos j.property
    map_add' := by intro a b; funext j; exact congrFun (map_add B.equivFun a.val b.val) j.val
    map_smul' := by intro c m; funext j; exact congrFun (map_smul B.equivFun c m.val) j.val }

end SGPT.Toric
