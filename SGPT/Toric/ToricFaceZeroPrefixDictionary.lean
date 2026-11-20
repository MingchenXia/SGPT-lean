import SGPT.Toric.ToricFaceAffineFlagDictionary
import SGPT.Okounkov.SourceMultiSliceRemainingFlag

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.Okounkov.SourceMultiSlice
open scoped Topology Classical
variable {m k : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin (m + k) → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The ENTIRE original affine flag vector consists of exactly k zeros
followed by the SAME genuine target vector, under the proved equal finite
rank. This is the literal source multi-slice coordinate dictionary, including
all zero/full dimensional cases, not an assumed body comparison. -/
theorem toricFace_zeroPrefix_flagRealMap
    (D : ToricDivisor γ hs) (v : latticePolytopeVertices γ)
    (e : Fin (m + k) ≃ Fin (m + k))
    (mσ : Fin (m + k) → ℤ)
    (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v ''
      toricFlagSelectedIndices e (originalIndex m k)) mσ)
    (x : toricStratumRealSpace (polytopeToricRay γ hs v ''
      toricFlagSelectedIndices e (originalIndex m k))) :
    let hd : toricFaceDimension (toricFlagSelectedIndices e (originalIndex m k)) = m :=
      (toricFaceDimension_flagSelectedIndices e (originalIndex m k)).trans (Nat.add_sub_cancel_right m k)
    zeroPrefix m k (fun j =>
      toricFlagRealMap
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v
          (toricFlagSelectedIndices e (originalIndex m k)))
        (toricFaceVertexEquiv (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k))
          (toricFaceBaseVertex (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k))))
        (toricFaceTailOrder (hs := hs) v e (originalIndex m k))
        (toricFaceRestrictedDivisor D v (toricFlagSelectedIndices e (originalIndex m k)) mσ)
        (toricFaceRealCharacterCoordinates (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k)) x)
        (Fin.cast hd.symm j)) =
      toricFlagRealMap hs v e D (x.val + latticeVector mσ) := by
  intro hd
  ext l
  by_cases hl : l.val < k
  · rw [zeroPrefix_first m k _ l hl]
    exact (toricFlagRealMap_selected_zero_of_annihilator D v e (originalIndex m k) mσ hσ x l hl).symm
  · let j : Fin m := ⟨l.val - k, by omega⟩
    have hindex : l = (⟨k + j.val, by omega⟩ : Fin (m + k)) := by apply Fin.ext; dsimp only [j]; omega
    rw [hindex, zeroPrefix_tail]
    exact toricFaceFlagRealMap_translation D v e (originalIndex m k) mσ hσ x (Fin.cast hd.symm j)

/-- Every actual translated annihilator point satisfying the original
polytope inequalities is on the LITERAL original Qσ face. -/
theorem toricDivisorFace_add_Cartier_of_annihilator
    {D : ToricDivisor γ hs} {R : Set (PolytopeToricRays γ hs)} {mσ : Fin (m + k) → ℤ}
    (hσ : IsToricCartierDatumAlong D R mσ) (x : toricStratumRealSpace R)
    (hx : x.val + latticeVector mσ ∈ toricDivisorPolytope D) :
    x.val + latticeVector mσ ∈ toricDivisorFace D R := by
  refine ⟨hx, ?_⟩
  intro ρ hρ
  rw [map_add, x.property ρ hρ, zero_add, latticeFunctional_latticeVector, intPairing_comm, hσ ρ hρ]
  norm_cast

end SGPT.Toric
