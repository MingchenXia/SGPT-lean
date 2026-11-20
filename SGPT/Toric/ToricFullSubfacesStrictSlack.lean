import SGPT.Toric.ToricDivisorSlack

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

theorem edge_pairing_zero_outside_selected_of_full_face_slack_zero
    (D : ToricDivisor γ hs) (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (hfull : ToricDivisorFaceFull D (polytopeToricRay γ hs v '' J))
    (ρ : PolytopeToricRays γ hs)
    (hz : ∀ x ∈ toricDivisorFace D (polytopeToricRay γ hs v '' J),
      toricDivisorSlack D ρ x = 0)
    (k : Fin n) (hk : k ∉ J) :
    intPairing (originalPolytopeNativeBasis γ hs v k) ρ.val = 0 := by
  have hh := latticeFunctional_annihilator_eq_zero_of_full_face_slack_zero D hfull ρ hz
    (toricOriginalEuclideanEdgeBasis_mem_annihilator (hs := hs) v J k hk)
  rw [latticeFunctional_toricOriginalEuclideanEdgeBasis_general] at hh
  exact_mod_cast hh

theorem toricDivisorSlack_cartier_eq_zero_of_full_face_slack_zero
    (D : ToricDivisor γ hs) (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (hfull : ToricDivisorFaceFull D (polytopeToricRay γ hs v '' J))
    (ρ : PolytopeToricRays γ hs)
    (hz : ∀ x ∈ toricDivisorFace D (polytopeToricRay γ hs v '' J),
      toricDivisorSlack D ρ x = 0) :
    toricDivisorSlack D ρ (latticeVector (toricCartierDatum D v)) = 0 := by
  obtain ⟨x, hx⟩ := hfull.1
  have hexp := toricDivisorSlack_expand D v ρ x
  have hsum : (∑ j : Fin n,
      (intPairing (originalPolytopeNativeBasis γ hs v j) ρ.val : ℝ) *
        toricDivisorSlack D (polytopeToricRay γ hs v j) x) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j ∈ J
    · rw [toricDivisorSlack_eq_zero_of_mem_face hx ⟨j, hj, rfl⟩, mul_zero]
    · rw [edge_pairing_zero_outside_selected_of_full_face_slack_zero D v J hfull ρ hz j hj,
        Int.cast_zero, zero_mul]
  rw [hsum, add_zero, hz x hx] at hexp
  exact hexp.symm

/-- Fullness of ALL actual subcones forces strict slack on every original
ray outside the vertex cone. In particular this does not use the false
individual-stratum iff from the book's proof of cor:augbl. -/
theorem exists_pos_toricDivisorSlack_of_all_subfaces_full
    (D : ToricDivisor γ hs) (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (hfull : ∀ I : Set (Fin n), I ⊆ J →
      ToricDivisorFaceFull D (polytopeToricRay γ hs v '' I))
    (ρ : PolytopeToricRays γ hs) (hout : ρ ∉ Set.range (polytopeToricRay γ hs v)) :
    ∃ x ∈ toricDivisorFace D (polytopeToricRay γ hs v '' J),
      0 < toricDivisorSlack D ρ x := by
  by_contra hpos
  push Not at hpos
  have hz : ∀ x ∈ toricDivisorFace D (polytopeToricRay γ hs v '' J),
      toricDivisorSlack D ρ x = 0 := by
    intro x hx
    exact le_antisymm (hpos x hx) (toricDivisorSlack_nonneg hx.1 ρ)
  have hJ := hfull J (Set.Subset.refl J)
  have hc0 := edge_pairing_zero_outside_selected_of_full_face_slack_zero D v J hJ ρ hz
  have hb0 := toricDivisorSlack_cartier_eq_zero_of_full_face_slack_zero D v J hJ ρ hz
  obtain ⟨k, hkneg⟩ := exists_negative_edge_pairing_of_ray_not_at_vertex (hs := hs) v ρ hout
  let I : Set (Fin n) := {j | j ∈ J ∧ 0 < intPairing (originalPolytopeNativeBasis γ hs v j) ρ.val}
  have hIJ : I ⊆ J := fun _ hj => hj.1
  have hkI : k ∉ I := by
    intro hk
    exact (not_lt_of_ge (le_of_lt hkneg)) hk.2
  have hI := hfull I hIJ
  have hzeroI : ∀ x ∈ toricDivisorFace D (polytopeToricRay γ hs v '' I),
      toricDivisorSlack D (polytopeToricRay γ hs v k) x = 0 := by
    intro x hx
    have hnonpos (j : Fin n) :
        (intPairing (originalPolytopeNativeBasis γ hs v j) ρ.val : ℝ) *
          toricDivisorSlack D (polytopeToricRay γ hs v j) x ≤ 0 := by
      by_cases hj : j ∈ I
      · rw [toricDivisorSlack_eq_zero_of_mem_face hx ⟨j, hj, rfl⟩, mul_zero]
      · have hcj : intPairing (originalPolytopeNativeBasis γ hs v j) ρ.val ≤ 0 := by
          by_cases hjJ : j ∈ J
          · exact le_of_not_gt (fun hjpos => hj ⟨hjJ, hjpos⟩)
          · rw [hc0 j hjJ]
        exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hcj)
          (toricDivisorSlack_nonneg hx.1 _)
    have hexp := toricDivisorSlack_expand D v ρ x
    rw [hb0, zero_add] at hexp
    have hsum0 : (∑ j : Fin n,
        (intPairing (originalPolytopeNativeBasis γ hs v j) ρ.val : ℝ) *
          toricDivisorSlack D (polytopeToricRay γ hs v j) x) = 0 := by
      apply le_antisymm (Finset.sum_nonpos fun j _ => hnonpos j)
      rw [← hexp]
      exact toricDivisorSlack_nonneg hx.1 ρ
    have hterm := (Finset.sum_eq_zero_iff_of_nonpos (fun j (_ : j ∈ Finset.univ) =>
      hnonpos j)).mp hsum0 k (Finset.mem_univ k)
    exact (mul_eq_zero.mp hterm).resolve_left (by exact_mod_cast hkneg.ne)
  have hann := toricOriginalEuclideanEdgeBasis_mem_annihilator (hs := hs) v I k hkI
  have hbad := latticeFunctional_annihilator_eq_zero_of_full_face_slack_zero
    D hI (polytopeToricRay γ hs v k) hzeroI hann
  change latticeFunctional (polytopeToricRayGenerator γ hs v k)
    (toricOriginalEuclideanEdgeBasis (hs := hs) v k) = 0 at hbad
  rw [latticeFunctional_toricOriginalEuclideanEdgeBasis, if_pos rfl] at hbad
  norm_num at hbad

end SGPT.Toric
