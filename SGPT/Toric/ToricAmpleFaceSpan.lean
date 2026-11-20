import SGPT.Toric.ToricAugmentedBaseLocus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The SAME original edge basis, transported only through the defining
Euclidean coordinate equivalence. -/
def toricOriginalEuclideanEdgeBasis (v : latticePolytopeVertices γ) :
    Module.Basis (Fin n) ℝ E :=
  (integralRealBasis (originalPolytopeNativeBasis γ hs v)).map
    (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearEquiv

theorem toricOriginalEuclideanEdgeBasis_apply (v : latticePolytopeVertices γ) (j : Fin n) :
    toricOriginalEuclideanEdgeBasis (hs := hs) v j =
      latticeVector (originalPolytopeNativeBasis γ hs v j) := by
  ext k
  simp [toricOriginalEuclideanEdgeBasis, Module.Basis.map_apply,
    integralRealBasis_apply, latticeVector, integerCast]

theorem latticeFunctional_toricOriginalEuclideanEdgeBasis (v : latticePolytopeVertices γ)
    (i j : Fin n) :
    latticeFunctional (polytopeToricRayGenerator γ hs v j)
      (toricOriginalEuclideanEdgeBasis (hs := hs) v i) = if i = j then 1 else 0 := by
  rw [toricOriginalEuclideanEdgeBasis_apply, latticeFunctional_latticeVector, intPairing_comm,
    intPairing_basis_rayGenerator]
  split_ifs <;> norm_num

theorem toricOriginalEuclideanEdgeBasis_repr (v : latticePolytopeVertices γ)
    (x : E) (j : Fin n) :
    (toricOriginalEuclideanEdgeBasis (hs := hs) v).repr x j =
      latticeFunctional (polytopeToricRayGenerator γ hs v j) x := by
  let B := toricOriginalEuclideanEdgeBasis (hs := hs) v
  have heq : B.coord j = latticeFunctional (polytopeToricRayGenerator γ hs v j) := by
    apply B.ext
    intro i
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self_apply]
    exact (latticeFunctional_toricOriginalEuclideanEdgeBasis (hs := hs) v i j).symm
  exact LinearMap.congr_fun heq x

theorem toricOriginalEuclideanEdgeBasis_mem_annihilator (v : latticePolytopeVertices γ)
    (J : Set (Fin n)) (k : Fin n) (hk : k ∉ J) :
    toricOriginalEuclideanEdgeBasis (hs := hs) v k ∈
      toricStratumRealSpace (polytopeToricRay γ hs v '' J) := by
  rintro ρ ⟨j, hj, rfl⟩
  change latticeFunctional (polytopeToricRayGenerator γ hs v j) _ = 0
  rw [latticeFunctional_toricOriginalEuclideanEdgeBasis, if_neg]
  intro heq
  exact hk (heq ▸ hj)

theorem toricAmpleDivisorFace_vertex_mem (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    latticeVector v.val ∈ toricDivisorFace (polytopeToricAmpleDivisor γ hs)
      (polytopeToricRay γ hs v '' J) := by
  refine ⟨latticeVector_vertex_mem_ampleDivisorPolytope γ hs v, ?_⟩
  intro ρ hρ
  have hm := isToricCartierDatumAlong_vertex (polytopeToricAmpleDivisor γ hs) v J ρ hρ
  rw [toricCartierDatum_ampleDivisor] at hm
  rw [latticeFunctional_latticeVector, intPairing_comm, hm, Int.cast_neg]

theorem toricAmpleDivisorFace_free_neighbor_mem (v : latticePolytopeVertices γ)
    (J : Set (Fin n)) (k : Fin n) (hk : k ∉ J) :
    latticeVector (v.val + originalPolytopeNativeBasis γ hs v k) ∈
      toricDivisorFace (polytopeToricAmpleDivisor γ hs) (polytopeToricRay γ hs v '' J) := by
  have hh := toricNativeFace_free_neighbor_mem (hs := hs) v J k hk
  rw [toricNativeVertexFace_eq_ampleDivisorFace] at hh
  exact hh

/-- Actual primitive free neighbors of the SAME original reference vertex
manufacture its entire affine-face span. No fullness or target-dimension
certificate is supplied. -/
theorem toricAmpleDivisorFace_full (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    ToricDivisorFaceFull (polytopeToricAmpleDivisor γ hs) (polytopeToricRay γ hs v '' J) := by
  let Q := toricDivisorFace (polytopeToricAmpleDivisor γ hs) (polytopeToricRay γ hs v '' J)
  let B := toricOriginalEuclideanEdgeBasis (hs := hs) v
  have hv : latticeVector v.val ∈ Q := toricAmpleDivisorFace_vertex_mem v J
  refine ⟨⟨_, hv⟩, le_antisymm (vectorSpan_toricDivisorFace_le _ _) ?_⟩
  intro x hx
  have hb (k : Fin n) (hk : k ∉ J) : B k ∈ vectorSpan ℝ Q := by
    have hneighbor := toricAmpleDivisorFace_free_neighbor_mem (hs := hs) v J k hk
    have hh := vsub_mem_vectorSpan ℝ hneighbor hv
    have heq : latticeVector (v.val + originalPolytopeNativeBasis γ hs v k) -
        latticeVector v.val = B k := by
      rw [show B k = latticeVector (originalPolytopeNativeBasis γ hs v k) from
        toricOriginalEuclideanEdgeBasis_apply v k]
      ext i
      simp only [PiLp.sub_apply, latticeVector_apply, Pi.add_apply, Int.cast_add]
      ring
    exact heq ▸ hh
  rw [← B.sum_repr x]
  apply Submodule.sum_mem
  intro k _
  by_cases hk : k ∈ J
  · have hz : B.repr x k = 0 :=
      (toricOriginalEuclideanEdgeBasis_repr v x k).trans
        (hx (polytopeToricRay γ hs v k) ⟨k, hk, rfl⟩)
    rw [hz, zero_smul]
    exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (hb k hk)

theorem toricAmpleDivisorFace_full_of_fanCone {R : Set (PolytopeToricRays γ hs)}
    (hR : IsToricFanCone R) : ToricDivisorFaceFull (polytopeToricAmpleDivisor γ hs) R := by
  obtain ⟨v, J, rfl⟩ := hR
  exact toricAmpleDivisorFace_full v J

end SGPT.Toric
