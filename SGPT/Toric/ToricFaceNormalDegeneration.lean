import SGPT.Toric.ToricFaceTorusEquivariance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.AlmostSemigroup.Counting
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The genuine original normal cocharacter: the sum of ALL σ primitive
rays, defined before any metric or target trace is chosen. -/
def toricFaceNormalCocharacter (v : latticePolytopeVertices γ) (J : Set (Fin n)) : Fin n → ℤ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ∈ J), polytopeToricRayGenerator γ hs v j

/-- Original duality gives normal weight1 exactly on σ and0 elsewhere. -/
theorem toricFaceNormalCocharacter_pairing (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (k : Fin n) :
    intPairing (originalPolytopeNativeBasis γ hs v k) (toricFaceNormalCocharacter (hs := hs) v J) =
      if k ∈ J then 1 else 0 := by
  simp [toricFaceNormalCocharacter, intPairing_sum_right, intPairing_basis_rayGenerator]

/-- EVERY actual annihilator character is constant along the actual normal
cocharacter; this follows from its original defining equations. -/
theorem toricFaceNormalCocharacter_annihilator (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (m : toricStratumCharacterLattice (polytopeToricRay γ hs v '' J)) :
    intPairing m.val (toricFaceNormalCocharacter (hs := hs) v J) = 0 := by
  rw [toricFaceNormalCocharacter, intPairing_sum_right]
  apply Finset.sum_eq_zero
  intro j hj
  exact m.property (polytopeToricRay γ hs v j) ⟨j, (Finset.mem_filter.mp hj).2, rfl⟩

/-- The actual original torus lift has the genuine base-chart coordinates:
1 on σ, and the SAME target torus factors on the actual complementary basis. -/
theorem toricFaceTorusSection_character (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (a : Fin (toricFaceDimension J) → ℂˣ) (k : Fin n) :
    latticeCharacter (originalPolytopeNativeBasis γ hs v k)
      (toricFaceTorusSection (hs := hs) v J a) =
      if hk : k ∈ J then 1 else a ((Fintype.equivFin {j : Fin n // j ∉ J}) ⟨k, hk⟩) :=
  toricStratumTorusSection_character v J _ k

/-- A concrete genuine complex-unit sequence approaching0. -/
def toricFaceNormalParameter (N : ℕ) : ℂˣ :=
  Units.mk0 ((N + 1 : ℂ)⁻¹) (by apply inv_ne_zero; exact_mod_cast Nat.succ_ne_zero N)

theorem tendsto_toricFaceNormalParameter :
    Tendsto (fun N => (toricFaceNormalParameter N : ℂ)) atTop (𝓝 0) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
  refine h.congr fun N => ?_
  simp [toricFaceNormalParameter, one_div]

/-- ACTUAL original dense-torus points degenerating normally to the SAME
original stratum. Every term remains an original ambient torus point. -/
def toricFaceNormalCurve (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (a : Fin (toricFaceDimension J) → ℂˣ) (N : ℕ) : Fin n → ℂˣ :=
  toricFaceTorusSection (hs := hs) v J a *
    torusCocharacter (toricFaceNormalCocharacter (hs := hs) v J) (toricFaceNormalParameter N)

/-- The concrete original torus degeneration converges in the SAME actual
ambient native space to the actual embedded target orbit point. This is the
genuine boundary-limit producer needed to restrict ambient metric transitions. -/
theorem tendsto_toricFaceNormalCurve (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (a : Fin (toricFaceDimension J) → ℂˣ) :
    Tendsto (fun N => polytopeToricEmbedding γ hs (toricFaceNormalCurve (hs := hs) v J a N)) atTop
      (𝓝 (toricFaceNativeEmbedding (hs := hs) v J
        (originalPolytopeNativeOrbitMap (toricFaceProjectedFamily (hs := hs) v J) a))) := by
  have hformula (N : ℕ) :
      polytopeToricEmbedding γ hs (toricFaceNormalCurve (hs := hs) v J a N) =
        vertexPoint hs v (modelPoint fun k => if hk : k ∈ J then (toricFaceNormalParameter N : ℂ)
          else (a ((Fintype.equivFin {j : Fin n // j ∉ J}) ⟨k, hk⟩) : ℂ)) := by
    have hsrc : polytopeToricEmbedding γ hs (toricFaceNormalCurve (hs := hs) v J a N) ∈
        (originalPolytopeNativeModelChart γ hs v).source := by
      rw [originalPolytopeNativeModelChart_source]
      exact originalPolytopeNativeOrbitMap_mem_chart_source γ hs v _
    rw [← vertexPoint_chart v hsrc]
    apply congrArg (vertexPoint hs v)
    rw [toricFaceNormalCurve, vertexChart_embedding_mul_torusCocharacter]
    ext k
    rw [modelPoint_apply, modelPoint_apply, vertexChart_embedding, modelPoint_apply,
      toricFaceTorusSection_character, toricFaceNormalCocharacter_pairing]
    by_cases hk : k ∈ J <;> simp [hk]
  rw [toricFaceNativeEmbedding_orbit, nativePiChart_symm_eq_vertexPoint]
  simp only [hformula]
  apply ((continuous_vertexPoint v).tendsto _).comp
  apply (continuous_modelPoint.tendsto _).comp
  rw [tendsto_pi_nhds]
  intro k
  by_cases hk : k ∈ J
  · simpa [toricFaceBoundaryCoordinates, hk] using tendsto_toricFaceNormalParameter
  · simp only [toricFaceBoundaryCoordinates, dif_neg hk]
    exact tendsto_const_nhds

/-- Actual source characters in Mσ are CONSTANT on every original point of
the degeneration, including arbitrary original poles of unrelated potentials. -/
theorem latticeCharacter_toricFaceNormalCurve (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (m : toricStratumCharacterLattice (polytopeToricRay γ hs v '' J))
    (a : Fin (toricFaceDimension J) → ℂˣ) (N : ℕ) :
    latticeCharacter m.val (toricFaceNormalCurve (hs := hs) v J a N) =
      latticeCharacter m.val (toricFaceTorusSection (hs := hs) v J a) := by
  rw [toricFaceNormalCurve, map_mul, latticeCharacter_torusCocharacter]
  change latticeCharacter m.val (toricFaceTorusSection v J a) *
    toricFaceNormalParameter N ^ intPairing m.val (toricFaceNormalCocharacter v J) = _
  rw [toricFaceNormalCocharacter_annihilator, zpow_zero, mul_one]

end SGPT.Toric
