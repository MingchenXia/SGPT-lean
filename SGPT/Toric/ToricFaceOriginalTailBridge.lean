import SGPT.Toric.ToricFaceRemainingFlags
import SGPT.Toric.ToricFaceFlagInverseHolomorphic
import SGPT.Toric.ToricFaceSourceTracePotential
import SGPT.Okounkov.FlagDimensionSubmanifold
import SGPT.Okounkov.SourceMultiSliceWholeDirect

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.Okounkov SGPT.Okounkov.ToricTransport SGPT.Okounkov.SourceMultiSlice
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff Classical
variable {m k : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin (m + k) → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The ACTUAL produced character rank is the ORIGINAL remaining dimension,
for every original ambient m+k and every original prefix of length k. -/
theorem toricFaceOriginalDimension (e : Fin (m + k) ≃ Fin (m + k)) :
    toricFaceDimension (toricFlagSelectedIndices e (originalIndex m k)) = m := by
  rw [toricFaceDimension_flagSelectedIndices]
  exact Nat.add_sub_cancel_right m k

/-- The actual native toric full flag on the genuine lower-dimensional Y,
with the actual internally constructed remaining original ray order. -/
def toricFaceNativeFlagGeometry (v : latticePolytopeVertices γ)
    (e : Fin (m + k) ≃ Fin (m + k)) :
    OriginalFlagGeometry (toricFaceDimension (toricFlagSelectedIndices e (originalIndex m k))) :=
  toricFlagGeometry
    (hs := latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v
      (toricFlagSelectedIndices e (originalIndex m k)))
    (toricFaceVertexEquiv (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k))
      (toricFaceBaseVertex (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k))))
    (toricFaceTailOrder (hs := hs) v e (originalIndex m k))

/-- The SAME actual native Y carrier/topology/flags, with its independently
proved equal model dimension read as the original remaining dimension m. -/
def toricFaceRemainingFlagGeometry (v : latticePolytopeVertices γ)
    (e : Fin (m + k) ≃ Fin (m + k)) : OriginalFlagGeometry m :=
  changeFlagDimension (toricFaceOriginalDimension e) (toricFaceNativeFlagGeometry (hs := hs) v e)

/-- The SAME actual face/stratum homeomorphism onto the literal DIRECT
original Y_k, now in the genuine original remaining dimension. -/
def toricFaceOriginalDirectHomeomorph (v : latticePolytopeVertices γ)
    (e : Fin (m + k) ≃ Fin (m + k)) :
    (toricFaceRemainingFlagGeometry (hs := hs) v e).carrier ≃ₜ
      (toricFlagGeometry (hs := hs) v e).flag (originalIndex m k) :=
  toricFaceFlagHomeomorph (hs := hs) v e (originalIndex m k)

/-- Genuine FORWARD holomorphy into the SAME actual DIRECT inherited
original atlas; equality transport changes no points or chart construction. -/
theorem contMDiff_toricFaceOriginalDirectHomeomorph (v : latticePolytopeVertices γ)
    (e : Fin (m + k) ≃ Fin (m + k)) :
    letI := directCarrierCharts m k (toricFlagGeometry (hs := hs) v e)
    ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞
      (toricFaceOriginalDirectHomeomorph (hs := hs) v e) := by
  exact contMDiff_changeFlagDimension_to_submanifold (toricFaceOriginalDimension e)
    (toricFaceNativeFlagGeometry (hs := hs) v e)
    (toricFlag hs v e (originalIndex m k))
    (toricFaceFlag_dimension_le e (originalIndex m k))
    (toricFaceFlag_regular (hs := hs) v e (originalIndex m k)) (by omega)
    (directCarrier_regular m k (toricFlagGeometry (hs := hs) v e))
    (contMDiff_toricFaceFlagHomeomorph (hs := hs) v e (originalIndex m k))

/-- Genuine INVERSE holomorphy from the SAME actual DIRECT inherited
original atlas, including every original boundary point and m=0. -/
theorem contMDiff_toricFaceOriginalDirectHomeomorph_symm (v : latticePolytopeVertices γ)
    (e : Fin (m + k) ≃ Fin (m + k)) :
    letI := directCarrierCharts m k (toricFlagGeometry (hs := hs) v e)
    ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞
      (toricFaceOriginalDirectHomeomorph (hs := hs) v e).symm := by
  exact contMDiff_changeFlagDimension_from_submanifold (toricFaceOriginalDimension e)
    (toricFaceNativeFlagGeometry (hs := hs) v e)
    (toricFlag hs v e (originalIndex m k))
    (toricFaceFlag_dimension_le e (originalIndex m k))
    (toricFaceFlag_regular (hs := hs) v e (originalIndex m k)) (by omega)
    (directCarrier_regular m k (toricFlagGeometry (hs := hs) v e))
    (contMDiff_toricFaceFlagHomeomorph_symm (hs := hs) v e (originalIndex m k))

/-- The actual original iterated-tail/native-Y homeomorphism is the
COMPOSITION of the two genuine actual original carrier maps. -/
def toricFaceOriginalTailHomeomorph (v : latticePolytopeVertices γ)
    (e : Fin (m + k) ≃ Fin (m + k)) :
    (originalTail m k (toricFlagGeometry (hs := hs) v e)).carrier ≃ₜ
      (toricFaceRemainingFlagGeometry (hs := hs) v e).carrier :=
  (originalCarrierHomeomorph m k (toricFlagGeometry (hs := hs) v e)).trans
    (toricFaceOriginalDirectHomeomorph (hs := hs) v e).symm

theorem contMDiff_toricFaceOriginalTailHomeomorph (v : latticePolytopeVertices γ)
    (e : Fin (m + k) ≃ Fin (m + k)) :
    ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞
      (toricFaceOriginalTailHomeomorph (hs := hs) v e) := by
  let := directCarrierCharts m k (toricFlagGeometry (hs := hs) v e)
  exact (contMDiff_toricFaceOriginalDirectHomeomorph_symm (hs := hs) v e).comp
    (originalCarrierHomeomorph_contMDiff m k (toricFlagGeometry (hs := hs) v e))

theorem contMDiff_toricFaceOriginalTailHomeomorph_symm (v : latticePolytopeVertices γ)
    (e : Fin (m + k) ≃ Fin (m + k)) :
    ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞
      (toricFaceOriginalTailHomeomorph (hs := hs) v e).symm := by
  let := directCarrierCharts m k (toricFlagGeometry (hs := hs) v e)
  exact (originalCarrierHomeomorph_symm_contMDiff m k (toricFlagGeometry (hs := hs) v e)).comp
    (contMDiff_toricFaceOriginalDirectHomeomorph (hs := hs) v e)

/-- Literal original point readback for the SAME actual composite map. -/
theorem toricFaceOriginalTailHomeomorph_inclusion (v : latticePolytopeVertices γ)
    (e : Fin (m + k) ≃ Fin (m + k))
    (y : (originalTail m k (toricFlagGeometry (hs := hs) v e)).carrier) :
    toricFaceSourceInclusion (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k))
      (toricFaceOriginalTailHomeomorph (hs := hs) v e y) =
      originalInclusion m k (toricFlagGeometry (hs := hs) v e) y :=
  congrArg Subtype.val ((toricFaceOriginalDirectHomeomorph (hs := hs) v e).apply_symm_apply
    (originalCarrierHomeomorph m k (toricFlagGeometry (hs := hs) v e) y))

/-- EVERY ENTIRE remaining ORIGINAL flag is preserved by the SAME actual
composite biholomorphism, in the original source order and on all points. -/
theorem toricFaceOriginalTailHomeomorph_image_flag (v : latticePolytopeVertices γ)
    (e : Fin (m + k) ≃ Fin (m + k)) (s : Fin (m + 1)) :
    toricFaceOriginalTailHomeomorph (hs := hs) v e ''
      (originalTail m k (toricFlagGeometry (hs := hs) v e)).flag s =
      (toricFaceRemainingFlagGeometry (hs := hs) v e).flag s := by
  let i := originalIndex m k
  let hd := toricFaceOriginalDimension e
  let sD := Fin.cast (congrArg (fun a => a + 1) hd.symm) s
  have hindex : toricFaceTailAmbientIndex e i sD = remainingIndex m k s := Fin.ext rfl
  have hface := toricFaceFlagHomeomorph_image_remainingFlag (hs := hs) v e i sD
  rw [hindex] at hface
  have horig := originalCarrierHomeomorph_image_remainingFlag m k (toricFlagGeometry (hs := hs) v e) s
  change ((toricFaceOriginalDirectHomeomorph (hs := hs) v e).symm ∘
    (originalCarrierHomeomorph m k (toricFlagGeometry (hs := hs) v e))) '' _ = _
  rw [Set.image_comp, horig]
  change (toricFaceFlagHomeomorph (hs := hs) v e i).symm ''
    {y : toricFlag hs v e i | y.val ∈ toricFlag hs v e (remainingIndex m k s)} =
      toricFlag
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e i))
        (toricFaceVertexEquiv (hs := hs) v (toricFlagSelectedIndices e i)
          (toricFaceBaseVertex (hs := hs) v (toricFlagSelectedIndices e i)))
        (toricFaceTailOrder (hs := hs) v e i) sD
  rw [← hface, ← Set.image_comp]
  simp only [Homeomorph.symm_comp_self, Set.image_id]

/-- The genuine original geometry now produces the existing whole-flag
lifting used by the actual source body pullback theorem. -/
theorem toricFaceOriginalTailHomeomorph_isFlagLifting (v : latticePolytopeVertices γ)
    (e : Fin (m + k) ≃ Fin (m + k)) :
    IsFlagLifting (toricFaceRemainingFlagGeometry (hs := hs) v e)
      (originalTail m k (toricFlagGeometry (hs := hs) v e))
      (toricFaceOriginalTailHomeomorph (hs := hs) v e) :=
  isFlagLifting_of_biholomorphic _ (toricFaceOriginalTailHomeomorph_image_flag (hs := hs) v e)
    (contMDiff_toricFaceOriginalTailHomeomorph (hs := hs) v e)
    (contMDiff_toricFaceOriginalTailHomeomorph_symm (hs := hs) v e)

end SGPT.Toric
