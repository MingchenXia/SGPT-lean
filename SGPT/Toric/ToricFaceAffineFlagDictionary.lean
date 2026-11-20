import SGPT.Toric.ToricFaceRealCharacterCoordinates
import SGPT.Toric.ToricFaceRestrictedDivisor
import SGPT.Toric.ToricFaceRemainingFlags
import SGPT.Toric.Toric3OkounkovBody

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The LITERAL source affine diagram Ψ_R(Cσ,R(x))=tail_i Φ_R(x+mσ)
on EVERY real annihilator point, with arbitrary ORIGINAL valid mσ. Actual
dual rays, actual DY Cartier datum and the ORIGINAL remaining flag order
produce the equality; no affine/body dictionary certificate is an input. -/
theorem toricFaceFlagRealMap_translation
    (D : ToricDivisor γ hs) (v : latticePolytopeVertices γ)
    (e : Fin n ≃ Fin n) (i : Fin (n + 1))
    (mσ : Fin n → ℤ)
    (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v '' toricFlagSelectedIndices e i) mσ)
    (x : toricStratumRealSpace (polytopeToricRay γ hs v '' toricFlagSelectedIndices e i))
    (j : Fin (toricFaceDimension (toricFlagSelectedIndices e i))) :
    toricFlagRealMap
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e i))
      (toricFaceVertexEquiv (hs := hs) v (toricFlagSelectedIndices e i)
        (toricFaceBaseVertex (hs := hs) v (toricFlagSelectedIndices e i)))
      (toricFaceTailOrder (hs := hs) v e i) (toricFaceRestrictedDivisor D v (toricFlagSelectedIndices e i) mσ)
      (toricFaceRealCharacterCoordinates (hs := hs) v (toricFlagSelectedIndices e i) x) j =
      toricFlagRealMap hs v e D (x.val + latticeVector mσ)
        ⟨i.val + j.val, by have := j.isLt; have hd := toricFaceDimension_flagSelectedIndices e i; omega⟩ := by
  let J := toricFlagSelectedIndices e i
  let w := toricFaceBaseVertex (hs := hs) v J
  let k := toricFaceTailOrder (hs := hs) v e i j
  let ρ := polytopeToricRay (toricFaceProjectedFamily (hs := hs) v J)
    (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
    (toricFaceVertexEquiv (hs := hs) v J w) k
  have hreal := toricFaceRealCharacterCoordinates_ray_pairing v J ρ x
  rw [toricFaceRayLift_native, toricFaceTailOrder_free_index] at hreal
  dsimp only [ρ, k, w, J, toricFaceBaseVertex, polytopeToricRay] at hreal
  have hInt := toricFaceNativeRay_pairing v J w k (toricFaceRestrictedFrameCharacter D v J mσ hσ w)
  rw [toricFaceTailOrder_free_index] at hInt
  have hInt' : intPairing
      (toricCartierDatum (toricFaceRestrictedDivisor D v J mσ) (toricFaceVertexEquiv v J w)) ρ.val =
      intPairing (toricCartierDatum D v - mσ)
        (polytopeToricRayGenerator γ hs v (e ⟨i.val + j.val, by
          have := j.isLt; have hd := toricFaceDimension_flagSelectedIndices e i; omega⟩)) := by
    rw [toricFaceRestrictedDivisor_cartier D v J mσ hσ w]
    exact hInt
  dsimp only [ρ, k, w, J, toricFaceBaseVertex, polytopeToricRay] at hInt'
  simp only [toricFlagRealMap]
  dsimp only [toricFaceBaseVertex]
  rw [hreal, hInt']
  change latticeFunctional _ x.val -
    (intPairing (toricCartierDatum D v - mσ) _ : ℝ) = _
  rw [intPairing_sub, map_add, latticeFunctional_latticeVector, intPairing_comm]
  rw [intPairing_comm mσ]
  push_cast
  linarith

/-- On every actual translated source annihilator point, the selected
ORIGINAL Φ coordinates are literally0, including empty/full prefixes. -/
theorem toricFlagRealMap_selected_zero_of_annihilator
    (D : ToricDivisor γ hs) (v : latticePolytopeVertices γ)
    (e : Fin n ≃ Fin n) (i : Fin (n + 1))
    (mσ : Fin n → ℤ)
    (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v '' toricFlagSelectedIndices e i) mσ)
    (x : toricStratumRealSpace (polytopeToricRay γ hs v '' toricFlagSelectedIndices e i))
    (l : Fin n) (hl : l.val < i.val) :
    toricFlagRealMap hs v e D (x.val + latticeVector mσ) l = 0 := by
  have hmem : polytopeToricRay γ hs v (e l) ∈
      polytopeToricRay γ hs v '' toricFlagSelectedIndices e i :=
    ⟨e l, ⟨l, hl, rfl⟩, rfl⟩
  have hx := x.property (polytopeToricRay γ hs v (e l)) hmem
  have hm := hσ (polytopeToricRay γ hs v (e l)) hmem
  change latticeFunctional (polytopeToricRayGenerator γ hs v (e l)) x.val = 0 at hx
  change intPairing mσ (polytopeToricRayGenerator γ hs v (e l)) = _ at hm
  simp only [toricFlagRealMap, map_add]
  rw [hx, zero_add, latticeFunctional_latticeVector, intPairing_comm, hm, toricCartierDatum_pairing]
  exact sub_self _

end SGPT.Toric
