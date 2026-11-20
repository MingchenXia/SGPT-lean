import SGPT.Toric.ToricAmpleFaceSpan

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

def toricDivisorSlack (D : ToricDivisor γ hs) (ρ : PolytopeToricRays γ hs) (x : E) : ℝ :=
  (D ρ : ℝ) + latticeFunctional ρ.val x

theorem toricDivisorSlack_nonneg {D : ToricDivisor γ hs} {x : E}
    (hx : x ∈ toricDivisorPolytope D) (ρ : PolytopeToricRays γ hs) :
    0 ≤ toricDivisorSlack D ρ x := by
  have hh := hx ρ
  change -(D ρ : ℝ) ≤ latticeFunctional ρ.val x at hh
  change 0 ≤ (D ρ : ℝ) + latticeFunctional ρ.val x
  linarith

theorem toricDivisorSlack_eq_zero_of_mem_face {D : ToricDivisor γ hs}
    {R : Set (PolytopeToricRays γ hs)} {x : E} (hx : x ∈ toricDivisorFace D R)
    {ρ : PolytopeToricRays γ hs} (hρ : ρ ∈ R) : toricDivisorSlack D ρ x = 0 := by
  unfold toricDivisorSlack
  rw [hx.2 ρ hρ]
  ring

theorem latticeFunctional_toricOriginalEuclideanEdgeBasis_general
    (v : latticePolytopeVertices γ) (ρ : PolytopeToricRays γ hs) (j : Fin n) :
    latticeFunctional ρ.val (toricOriginalEuclideanEdgeBasis (hs := hs) v j) =
      (intPairing (originalPolytopeNativeBasis γ hs v j) ρ.val : ℝ) := by
  rw [toricOriginalEuclideanEdgeBasis_apply, latticeFunctional_latticeVector, intPairing_comm]

/-- The real slack expansion uses the SAME actual integral dual basis and
the SAME original Cartier datum. -/
theorem toricDivisorSlack_expand (D : ToricDivisor γ hs) (v : latticePolytopeVertices γ)
    (ρ : PolytopeToricRays γ hs) (x : E) :
    toricDivisorSlack D ρ x =
      toricDivisorSlack D ρ (latticeVector (toricCartierDatum D v)) +
        ∑ j : Fin n, (intPairing (originalPolytopeNativeBasis γ hs v j) ρ.val : ℝ) *
          toricDivisorSlack D (polytopeToricRay γ hs v j) x := by
  let B := toricOriginalEuclideanEdgeBasis (hs := hs) v
  let m := latticeVector (toricCartierDatum D v)
  have hrepr (j : Fin n) : B.repr (x - m) j =
      toricDivisorSlack D (polytopeToricRay γ hs v j) x := by
    rw [toricOriginalEuclideanEdgeBasis_repr, map_sub, latticeFunctional_latticeVector,
      intPairing_comm, toricCartierDatum_pairing, Int.cast_neg]
    simp only [toricDivisorSlack]
    change latticeFunctional (polytopeToricRayGenerator γ hs v j) x -
        -(D (polytopeToricRay γ hs v j) : ℝ) =
      (D (polytopeToricRay γ hs v j) : ℝ) +
        latticeFunctional (polytopeToricRayGenerator γ hs v j) x
    ring
  have hlin : latticeFunctional ρ.val (x - m) =
      ∑ j : Fin n, (intPairing (originalPolytopeNativeBasis γ hs v j) ρ.val : ℝ) *
        toricDivisorSlack D (polytopeToricRay γ hs v j) x := by
    conv_lhs => rw [← B.sum_repr (x - m)]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, smul_eq_mul, hrepr,
      latticeFunctional_toricOriginalEuclideanEdgeBasis_general]
    ring
  rw [map_sub] at hlin
  unfold toricDivisorSlack at hlin ⊢
  dsimp only [m] at hlin
  linarith

/-- An actual ray outside the original vertex cone has a negative
coefficient in its actual integral ray basis. This is proved from the
reference polytope's genuine supporting inequalities and facet incidence. -/
theorem exists_negative_edge_pairing_of_ray_not_at_vertex (v : latticePolytopeVertices γ)
    (ρ : PolytopeToricRays γ hs) (hout : ρ ∉ Set.range (polytopeToricRay γ hs v)) :
    ∃ j : Fin n, intPairing (originalPolytopeNativeBasis γ hs v j) ρ.val < 0 := by
  by_contra hneg
  push Not at hneg
  obtain ⟨w, j, hrho⟩ := ρ.property
  have hpos : 0 ≤ intPairing (w.val - v.val) ρ.val := by
    rw [intPairing_expand hs v]
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (intPairing_sub_vertex_nonneg hs v i w.property.1) (hneg i)
  have hpos' := intPairing_sub_vertex_nonneg hs w j v.property.1
  rw [hrho] at hpos'
  have hzero : intPairing (v.val - w.val) (polytopeToricRayGenerator γ hs w j) = 0 := by
    rw [hrho]
    rw [intPairing_sub] at hpos hpos' ⊢
    omega
  obtain ⟨i, hi⟩ := exists_rayGenerator_eq_of_pairing_eq_zero hzero
  apply hout
  refine ⟨i, ?_⟩
  apply Subtype.ext
  exact hi.trans hrho

/-- If the actual original slack is zero on an entire actual face, its
linear part vanishes on that face's actual difference span. -/
theorem vectorSpan_toricDivisorFace_le_ker_of_slack_zero
    (D : ToricDivisor γ hs) (R : Set (PolytopeToricRays γ hs))
    (ρ : PolytopeToricRays γ hs)
    (hz : ∀ x ∈ toricDivisorFace D R, toricDivisorSlack D ρ x = 0) :
    vectorSpan ℝ (toricDivisorFace D R) ≤ (latticeFunctional ρ.val).ker := by
  apply Submodule.span_le.mpr
  rintro z ⟨x, hx, y, hy, rfl⟩
  change latticeFunctional ρ.val (x - y) = 0
  have hx' := hz x hx
  have hy' := hz y hy
  unfold toricDivisorSlack at hx' hy'
  rw [map_sub]
  linarith

theorem latticeFunctional_annihilator_eq_zero_of_full_face_slack_zero
    (D : ToricDivisor γ hs) {R : Set (PolytopeToricRays γ hs)}
    (hfull : ToricDivisorFaceFull D R) (ρ : PolytopeToricRays γ hs)
    (hz : ∀ x ∈ toricDivisorFace D R, toricDivisorSlack D ρ x = 0)
    {x : E} (hx : x ∈ toricStratumRealSpace R) : latticeFunctional ρ.val x = 0 := by
  have hle := vectorSpan_toricDivisorFace_le_ker_of_slack_zero D R ρ hz
  rw [hfull.2] at hle
  exact hle hx

end SGPT.Toric
