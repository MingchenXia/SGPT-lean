import SGPT.Toric.OriginalEdgeConeCoordinates
import SGPT.Toric.UnimodularFacetNeighbors

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped BigOperators Topology

variable {n : ℕ} {K : Type*} [Fintype K]

/-- The existing genuine integer-functional extension of an actual dual basis
coordinate is EXACTLY the same original real-basis coordinate. -/
theorem integralRealFunctional_basis_coord
    (B : Module.Basis (Fin n) ℤ (Fin n → ℤ)) (j : Fin n) (x : Fin n → ℝ) :
    integralRealFunctional (B.coord j) x = (integralRealBasis B).repr x j := by
  have heq : (integralRealFunctional (B.coord j)).toLinearMap = (integralRealBasis B).coord j := by
    apply (integralRealBasis B).ext
    intro k
    rw [integralRealBasis_apply]
    change integralRealFunctional (B.coord j) (integerCast (B k)) =
      (integralRealBasis B).repr (integerCast (B k)) j
    rw [integralRealFunctional_integerCast, integralRealBasis_repr_integerCast]
    rfl
  exact congrArg (fun f : (Fin n → ℝ) →ₗ[ℝ] ℝ => f x) heq

/-- Choose from the genuine ORIGINAL-edge-only sign/neighbor producer.
No basis, signs, neighbors or halfspace presentation are additional inputs. -/
def originalVertexHalfspaceBasis (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    Module.Basis (Fin n) ℤ (Fin n → ℤ) :=
  (exists_latticePolytope_originalEdge_coordinate_basis γ v (hsmooth v)).choose

/-- All real-source signs and actual original neighbors are genuine produced fields. -/
theorem originalVertexHalfspaceBasis_spec (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    (∀ x ∈ latticePolytope γ, ∀ j,
      0 ≤ (integralRealBasis (originalVertexHalfspaceBasis γ hsmooth v)).repr
        (x - integerCast v.val) j) ∧
    (∀ m : latticePolytopeIntegerPoints γ, ∀ j,
      0 ≤ (originalVertexHalfspaceBasis γ hsmooth v).repr (m.val - v.val) j) ∧
    ∀ j, v.val + originalVertexHalfspaceBasis γ hsmooth v j ∈ latticePolytopeIntegerPoints γ :=
  (exists_latticePolytope_originalEdge_coordinate_basis γ v (hsmooth v)).choose_spec

/-- Actual original vertices and the actual basis coordinate index; this may
repeat a supporting hyperplane and is NOT yet the source facet index. -/
abbrev originalVertexHalfspaceIndex (γ : K → Fin n → ℤ) :=
  latticePolytopeVertices γ × Fin n

/-- Finiteness is manufactured from the genuine original finite vertex set. -/
instance originalVertexHalfspaceIndexFintype (γ : K → Fin n → ℤ) :
    Fintype (originalVertexHalfspaceIndex γ) := by
  letI := (finite_latticePolytopeVertices γ).fintype
  infer_instance

/-- The literal ORIGINAL integral dual coordinate, in the existing lattice dual. -/
def originalVertexHalfspaceNormal (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (ρ : originalVertexHalfspaceIndex γ) :
    (Fin n → ℤ) →ₗ[ℤ] ℤ :=
  (originalVertexHalfspaceBasis γ hsmooth ρ.1).coord ρ.2

/-- The exact original integral offset, manufactured rather than supplied. -/
def originalVertexHalfspaceOffset (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (ρ : originalVertexHalfspaceIndex γ) : ℤ :=
  -originalVertexHalfspaceNormal γ hsmooth ρ ρ.1.val

/-- Genuine original dual-basis readback gives the integer unit evaluation. -/
theorem originalVertexHalfspaceNormal_basis (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (ρ : originalVertexHalfspaceIndex γ) (k : Fin n) :
    originalVertexHalfspaceNormal γ hsmooth ρ (originalVertexHalfspaceBasis γ hsmooth ρ.1 k) =
      if k = ρ.2 then 1 else 0 := by
  change (originalVertexHalfspaceBasis γ hsmooth ρ.1).repr
    (originalVertexHalfspaceBasis γ hsmooth ρ.1 k) ρ.2 = _
  exact Module.Basis.repr_self_apply _ _ _

/-- In particular EVERY manufactured original normal is nonzero. -/
theorem originalVertexHalfspaceNormal_ne_zero (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (ρ : originalVertexHalfspaceIndex γ) :
    originalVertexHalfspaceNormal γ hsmooth ρ ≠ 0 := by
  intro hzero
  have h := originalVertexHalfspaceNormal_basis γ hsmooth ρ ρ.2
  rw [hzero] at h
  simp at h

/-- The EXISTING actual integral-halfspace value is the literal original real
vertex difference coordinate, before every inequality or real readback. -/
theorem originalVertexHalfspaceValue_eq_coord (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (ρ : originalVertexHalfspaceIndex γ)
    (x : Fin n → ℝ) :
    integralFacetValue (originalVertexHalfspaceNormal γ hsmooth)
      (originalVertexHalfspaceOffset γ hsmooth) ρ x =
      (integralRealBasis (originalVertexHalfspaceBasis γ hsmooth ρ.1)).repr
        (x - integerCast ρ.1.val) ρ.2 := by
  change integralRealFunctional ((originalVertexHalfspaceBasis γ hsmooth ρ.1).coord ρ.2) x +
    (-(originalVertexHalfspaceNormal γ hsmooth ρ ρ.1.val) : ℤ) = _
  rw [Int.cast_neg, integralRealFunctional_basis_coord, map_sub, Finsupp.sub_apply,
    integralRealBasis_repr_integerCast]
  rfl

/-- Every original source point satisfies EVERY actual manufactured integer
halfspace, by the genuine ORIGINAL-edge coordinate producer. -/
theorem latticePolytope_subset_originalVertexHalfspaces (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) :
    latticePolytope γ ⊆ integralFacetRegion (originalVertexHalfspaceNormal γ hsmooth)
      (originalVertexHalfspaceOffset γ hsmooth) := by
  intro x hx ρ
  change 0 ≤ integralFacetValue (originalVertexHalfspaceNormal γ hsmooth)
    (originalVertexHalfspaceOffset γ hsmooth) ρ x
  rw [originalVertexHalfspaceValue_eq_coord]
  exact (originalVertexHalfspaceBasis_spec γ hsmooth ρ.1).1 x hx ρ.2

/-- The actual first positive integral point of the original real normal ray
is produced from the unit basis evaluation. No primitivity certificate is input. -/
theorem originalVertexHalfspaceNormal_first_integer_ray (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (ρ : originalVertexHalfspaceIndex γ)
    (q : (Fin n → ℤ) →ₗ[ℤ] ℤ) {t : ℝ} (ht : 0 < t)
    (hscale : integralRealFunctional q =
      t • integralRealFunctional (originalVertexHalfspaceNormal γ hsmooth ρ)) :
    ∃ k : ℤ, 1 ≤ k ∧ t = (k : ℝ) ∧ q = k • originalVertexHalfspaceNormal γ hsmooth ρ := by
  have hq (m : Fin n → ℤ) : (q m : ℝ) =
      t * (originalVertexHalfspaceNormal γ hsmooth ρ m : ℝ) := by
    have h := congrArg (fun f : (Fin n → ℝ) →L[ℝ] ℝ => f (integerCast m)) hscale
    simpa only [smul_apply, smul_eq_mul, integralRealFunctional_integerCast] using h
  let k := q (originalVertexHalfspaceBasis γ hsmooth ρ.1 ρ.2)
  have hkcast : (k : ℝ) = t := by
    have h := hq (originalVertexHalfspaceBasis γ hsmooth ρ.1 ρ.2)
    simpa [k, originalVertexHalfspaceNormal_basis] using h
  have hkpos : 0 < k := by exact_mod_cast (hkcast.symm ▸ ht)
  refine ⟨k, by omega, hkcast.symm, ?_⟩
  apply LinearMap.ext
  intro m
  have h := hq m
  rw [← hkcast] at h
  change q m = k * originalVertexHalfspaceNormal γ hsmooth ρ m
  exact_mod_cast h

/-- The source-only primitive supporting integer halfspaces give EXACTLY the
SAME original hull. Genuine separation, the actual vertex hull, actual original
neighbors and existing basis reconstruction supply the reverse inclusion. -/
theorem latticePolytope_eq_originalVertexHalfspaces [Nonempty K]
    (γ : K → Fin n → ℤ) (hsmooth : latticePolytopeEdgeSmooth γ) :
    latticePolytope γ = integralFacetRegion (originalVertexHalfspaceNormal γ hsmooth)
      (originalVertexHalfspaceOffset γ hsmooth) := by
  apply Set.Subset.antisymm (latticePolytope_subset_originalVertexHalfspaces γ hsmooth)
  intro x hx
  by_contra hxP
  obtain ⟨h, c, hxc, hPc⟩ := geometric_hahn_banach_point_closed
    (convex_latticePolytope γ) (isCompact_latticePolytope γ).isClosed hxP
  obtain ⟨v, hv, hmin⟩ := Set.exists_min_image (latticePolytopeVertices γ)
    (fun m => h (integerCast m)) (finite_latticePolytopeVertices γ)
    (nonempty_latticePolytopeVertices γ)
  let V : latticePolytopeVertices γ := ⟨v, hv⟩
  let B := originalVertexHalfspaceBasis γ hsmooth V
  have hPmin : ∀ y ∈ latticePolytope γ, h (integerCast v) ≤ h y := by
    intro y hy
    rw [← convexHull_latticePolytopeVertices γ] at hy
    apply convexHull_min (t := {z | h (integerCast v) ≤ h z}) ?_ ?_ hy
    · rintro z ⟨w, hw, rfl⟩
      exact hmin w hw
    · exact convex_halfSpace_ge h.toLinearMap.isLinear _
  have hB (j : Fin n) : 0 ≤ h (integralRealBasis B j) := by
    have hneighbor := (originalVertexHalfspaceBasis_spec γ hsmooth V).2.2 j
    have h := hPmin (integerCast (v + B j)) hneighbor
    have heq : integerCast (v + B j) = integerCast v + integerCast (B j) := by
      ext i
      simp [integerCast]
    rw [heq, map_add] at h
    rw [integralRealBasis_apply]
    linarith
  have hcoord (j : Fin n) : 0 ≤ (integralRealBasis B).repr (x - integerCast v) j := by
    have hj := hx (V, j)
    change 0 ≤ integralFacetValue (originalVertexHalfspaceNormal γ hsmooth)
      (originalVertexHalfspaceOffset γ hsmooth) (V, j) x at hj
    rw [originalVertexHalfspaceValue_eq_coord] at hj
    exact hj
  have hnonneg : 0 ≤ h (x - integerCast v) := by
    rw [← (integralRealBasis B).sum_repr (x - integerCast v), map_sum]
    apply Finset.sum_nonneg
    intro j _
    rw [map_smul, smul_eq_mul]
    exact mul_nonneg (hcoord j) (hB j)
  have hvc := hPc (integerCast v) hv.1
  rw [map_sub] at hnonneg
  linarith

end SGPT.Toric
