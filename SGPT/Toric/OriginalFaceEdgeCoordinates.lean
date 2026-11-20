import SGPT.Toric.ExtremeConvexCombination

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped BigOperators
variable {n : ℕ} {K : Type*} [Fintype K]
variable {γ : K → Fin n → ℤ}

/-- Every actual original face point has zero coordinate along each genuine
original edge whose primitive neighbor lies outside the face. The finite
convex combination and its positive weights are manufactured internally
from the actual ALL-edge basis and the original geometric face. -/
theorem originalFace_edgeCoordinate_eq_zero_of_neighbor_not_mem
    {F : Set (Fin n → ℝ)} (hF : IsOriginalPolytopeFace γ F)
    (v : latticePolytopeVertices γ) (hv : integerCast v.val ∈ F)
    (b : Module.Basis (latticePolytopeEdgesAt γ v.val) ℤ (Fin n → ℤ))
    (hmem : ∀ E, integerCast (v.val + b E) ∈ E.val)
    {x : Fin n → ℝ} (hx : x ∈ F) (j : Fin n)
    (hj : integerCast (v.val + latticeEdgeCoordinateBasis γ v.val b j) ∉ F) :
    (integralRealBasis (latticeEdgeCoordinateBasis γ v.val b)).repr
      (x - integerCast v.val) j = 0 := by
  classical
  let B := latticeEdgeCoordinateBasis γ v.val b
  let R := integralRealBasis B
  let α : Fin n → ℝ := fun k => R.repr (x - integerCast v.val) k
  have hα : ∀ k, 0 ≤ α k := fun k =>
    latticePolytope_originalEdge_real_coordinate_nonneg γ v b hmem (hF.subset hx) k
  let S : ℝ := ∑ k, α k
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => hα k
  let ε : ℝ := (1 + S)⁻¹
  have hden : 0 < 1 + S := by linarith
  have hε : 0 < ε := inv_pos.mpr hden
  have hεle : ε ≤ 1 := by
    change (1 + S)⁻¹ ≤ 1
    exact (inv_le_one₀ hden).mpr (by linarith)
  let p : Option (Fin n) → (Fin n → ℝ)
    | none => integerCast v.val
    | some k => integerCast v.val + R k
  let w : Option (Fin n) → ℝ
    | none => ε
    | some k => ε * α k
  have hp : ∀ k, p k ∈ latticePolytope γ := by
    intro k
    cases k with
    | none => exact v.property.1
    | some k =>
      have hk := latticeEdgeCoordinateBasis_neighbor_mem γ v.val b hmem k
      change integerCast (v.val + B k) ∈ latticePolytope γ at hk
      convert hk using 1
      ext l
      simp [p, R, integralRealBasis_apply, integerCast]
  have hw : ∀ k, 0 ≤ w k := by
    intro k
    cases k with
    | none => exact hε.le
    | some k => exact mul_nonneg hε.le (hα k)
  have hcoeff : ε + ∑ k, ε * α k = 1 := by
    rw [← Finset.mul_sum]
    change ε + ε * S = 1
    dsimp only [ε]
    field_simp
  have hws : ∑ k, w k = 1 := by
    simpa only [Fintype.sum_option, w] using hcoeff
  have hvec : (∑ k, w k • p k) = (1 - ε) • integerCast v.val + ε • x := by
    simp only [Fintype.sum_option, w, p, smul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_smul]
    simp_rw [mul_smul]
    rw [← Finset.smul_sum]
    change ε • integerCast v.val + ((∑ k, ε * α k) • integerCast v.val +
      ε • ∑ k, α k • R k) = _
    rw [show (∑ k, α k • R k) = x - integerCast v.val from R.sum_repr _]
    have hc : ∑ k, ε * α k = 1 - ε := by linarith [hcoeff]
    rw [hc]
    module
  have hz : (∑ k, w k • p k) ∈ F := by
    rw [hvec]
    exact hF.convex hv hx (sub_nonneg.mpr hεle) hε.le (by ring)
  by_contra hj0
  have hαj : 0 < α j := lt_of_le_of_ne (hα j) (Ne.symm hj0)
  have hpoint := mem_extreme_of_sum_smul_mem (convex_latticePolytope γ) hF.isExtreme
    w p hw hws hp hz (some j) (mul_pos hε hαj)
  apply hj
  change integerCast v.val + R j ∈ F at hpoint
  convert hpoint using 1
  ext l
  simp [B, R, integralRealBasis_apply, integerCast]

end SGPT.Toric
