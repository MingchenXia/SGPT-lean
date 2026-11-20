import SGPT.Toric.ToricFaceFiniteGenerators
import SGPT.Toric.ToricStratumRealCoordinates
import SGPT.Toric.BigToricAmple

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The genuine real extension of the SAME native integral edge coordinate
is the original pairing with its actual fan ray. -/
theorem nativeBasisRealCoord_eq_rayPairing (v : latticePolytopeVertices γ)
    (x : Fin n → ℝ) (j : Fin n) :
    (integralRealBasis (originalPolytopeNativeBasis γ hs v)).repr x j =
      latticeFunctional (polytopeToricRayGenerator γ hs v j)
        ((EuclideanSpace.equiv (Fin n) ℝ).symm x) := by
  rw [← integralRealFunctional_basis_coord, integralRealFunctional_apply, latticeFunctional_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Module.Basis.coord_apply, Pi.basisFun_apply, polytopeToricRayGenerator]
  exact mul_comm _ _

/-- The ACTUAL original ample divisor identifies the vertex coordinate with
its literal supporting constant, independently of any face certificate. -/
theorem nativeBasisRealCoord_vertex_eq_ampleCoefficient (v : latticePolytopeVertices γ)
    (j : Fin n) :
    (integralRealBasis (originalPolytopeNativeBasis γ hs v)).repr (integerCast v.val) j =
      -((polytopeToricAmpleDivisor γ hs) (polytopeToricRay γ hs v j) : ℝ) := by
  rw [integralRealBasis_repr_integerCast, basis_repr_eq_intPairing]
  have h := toricCartierDatum_pairing (polytopeToricAmpleDivisor γ hs) v j
  rw [toricCartierDatum_ampleDivisor] at h
  exact_mod_cast h

/-- Every original real point has nonnegative native edge coordinates. The
actual ample polytope equality and its literal inequalities manufacture this
sign for the chosen native basis; no coordinate positivity is supplied. -/
theorem nativeBasisRealCoord_vertex_le (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ latticePolytope γ) (j : Fin n) :
    (integralRealBasis (originalPolytopeNativeBasis γ hs v)).repr (integerCast v.val) j ≤
      (integralRealBasis (originalPolytopeNativeBasis γ hs v)).repr x j := by
  have hxE : (EuclideanSpace.equiv (Fin n) ℝ).symm x ∈
      toricDivisorPolytope (polytopeToricAmpleDivisor γ hs) := by
    rw [toricDivisorPolytope_ampleDivisor]
    exact hx
  rw [nativeBasisRealCoord_vertex_eq_ampleCoefficient, nativeBasisRealCoord_eq_rayPairing]
  exact hxE (polytopeToricRay γ hs v j)

/-- The literal original selected native-ray face inside the SAME original
real lattice polytope, before assigning any lower-dimensional model. -/
def toricNativeVertexFace (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    Set (Fin n → ℝ) :=
  {x | x ∈ latticePolytope γ ∧ ∀ j ∈ J,
    (integralRealBasis (originalPolytopeNativeBasis γ hs v)).repr x j =
      (integralRealBasis (originalPolytopeNativeBasis γ hs v)).repr (integerCast v.val) j}

/-- Actual supporting inequalities prove the actual selected fan face is
closed, convex, nonempty and extreme, in every codimension including n. -/
theorem isOriginalPolytopeFace_toricNativeVertexFace (v : latticePolytopeVertices γ)
    (J : Set (Fin n)) : IsOriginalPolytopeFace γ (toricNativeVertexFace (hs := hs) v J) := by
  let B := integralRealBasis (originalPolytopeNativeBasis γ hs v)
  have heq : toricNativeVertexFace (hs := hs) v J = latticePolytope γ ∩
      ⋂ j ∈ J, {x | B.repr x j = B.repr (integerCast v.val) j} := by
    ext x
    simp [toricNativeVertexFace, B]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heq]
    exact (isCompact_latticePolytope γ).isClosed.inter (isClosed_iInter fun j =>
      isClosed_iInter fun _ => isClosed_eq ((continuous_apply j).comp B.equivFunL.continuous)
        continuous_const)
  · rw [heq]
    exact (convex_latticePolytope γ).inter (convex_iInter fun j => convex_iInter fun _ =>
      convex_hyperplane (B.coord j).isLinear _)
  · exact ⟨integerCast v.val, v.property.1, fun _ _ => rfl⟩
  · refine ⟨fun _ hx => hx.1, ?_⟩
    intro x hx y hy z hz hseg
    refine ⟨hx, ?_⟩
    intro j hj
    obtain ⟨a, b, ha, hb, hab, hzxy⟩ := hseg
    have hzero : a * B.repr x j + b * B.repr y j = B.repr (integerCast v.val) j := by
      rw [← hzxy] at hz
      simpa only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] using hz.2 j hj
    have hxge := nativeBasisRealCoord_vertex_le (hs := hs) v hx j
    have hyge := nativeBasisRealCoord_vertex_le (hs := hs) v hy j
    have habv : (a + b) * B.repr (integerCast v.val) j = B.repr (integerCast v.val) j := by
      rw [hab, one_mul]
    change B.repr x j = B.repr (integerCast v.val) j
    change B.repr (integerCast v.val) j ≤ B.repr x j at hxge
    change B.repr (integerCast v.val) j ≤ B.repr y j at hyge
    nlinarith

/-- The native selected face is EXACTLY the original ample divisor face
for the ACTUAL fan cone. This binds combinatorics to the original toric
source objects, rather than assigning a compatible abstract polytope. -/
theorem toricNativeVertexFace_eq_ampleDivisorFace (v : latticePolytopeVertices γ)
    (J : Set (Fin n)) :
    toricNativeVertexFace (hs := hs) v J =
      (EuclideanSpace.equiv (Fin n) ℝ).symm ⁻¹'
        toricDivisorFace (polytopeToricAmpleDivisor γ hs) (polytopeToricRay γ hs v '' J) := by
  ext x
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · rw [toricDivisorPolytope_ampleDivisor]
      exact hx.1
    · rintro ρ ⟨j, hj, rfl⟩
      change latticeFunctional (polytopeToricRayGenerator γ hs v j) _ = _
      rw [← nativeBasisRealCoord_eq_rayPairing, hx.2 j hj,
        nativeBasisRealCoord_vertex_eq_ampleCoefficient]
  · intro hx
    refine ⟨?_, ?_⟩
    · have hp := hx.1
      rw [toricDivisorPolytope_ampleDivisor] at hp
      exact hp
    · intro j hj
      rw [nativeBasisRealCoord_eq_rayPairing, nativeBasisRealCoord_vertex_eq_ampleCoefficient]
      exact hx.2 (polytopeToricRay γ hs v j) ⟨j, hj, rfl⟩

end SGPT.Toric
