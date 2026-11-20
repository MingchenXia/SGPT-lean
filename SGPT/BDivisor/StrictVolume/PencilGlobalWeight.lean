import SGPT.BDivisor.StrictVolume.PencilWeightReadback
import SGPT.Projective.FubiniStudy

/-! The actual weight readback in EVERY original native vertex coordinate. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.BDivisor.StrictPencilNext

open SGPT.Toric SGPT.Toric.BlowdownDraft
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped BigOperators

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

theorem originalPencilFsMetric_weight_homNormSq
    (v : latticePolytopeVertices blowupGenerator) (u : ComplexModel 2) :
    (originalPencilFsMetric hs).weight v u = Real.log 2 +
      Real.log (SGPT.Projective.ComplexProjectiveSpace.homNormSq (N := 1)
        (originalMonomialVector (blowupDirectionDivisor hs)
          (blowupDirectionLatticePoint hs) v u)) := by
  obtain ⟨k, hk⟩ := originalBlowupVertexEquiv.surjective v
  have hv : v = blowupVertex k := hk.symm
  subst v
  change (originalPencilFsMetric hs).weight (blowupVertex k) u = Real.log 2 +
    Real.log (∑ m : Fin 2, ‖originalMonomialVector (blowupDirectionDivisor hs)
      (blowupDirectionLatticePoint hs) (blowupVertex k) u m‖ ^ 2)
  let z : Fin 2 → ℂ := fun j => u ((blowupOriginalPermutation hs k).symm j)
  have hcoord : blowupOriginalCoordinates hs k z = u := by
    ext j
    simp [blowupOriginalCoordinates, z, modelPoint_apply]
  have hweight := originalPencilFsWeight_ordered hs k z
  have hvector := blowupDirectionOriginalVector hs k z
  rw [hcoord] at hweight hvector
  simpa only [← hvector, Fin.sum_univ_two] using hweight

end SGPT.BDivisor.StrictPencilNext
