import SGPT.Toric.PointBlowupGeometry
import SGPT.Toric.NativeChernPullback
import SGPT.Projective.FubiniStudy
import SGPT.Foundations.Analysis.Pending.NefMixedMass

/-! The SAME actual original pencil map, with internally proved positivity. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.BDivisor.StrictPencilNext

open Set
open SGPT.Toric SGPT.Toric.BlowdownDraft
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

def originalPencilPullbackForm :
    ClosedRealOneOneForm 2 (PolytopeToricVariety blowupGenerator hs) :=
  ClosedRealOneOneForm.pullback (contMDiff_originalBlowupDirection hs)
    (SGPT.Projective.ComplexProjectiveSpace.fsClosedForm (N := 1))

theorem originalPencilPullbackForm_isSemipositive :
    (originalPencilPullbackForm hs).val.IsSemipositive := by
  intro e z hz v
  let f := originalBlowupDirection hs
  let d := complexChartAt (n := 1) (f (e.val.symm z))
  have hzd : z ∈ HolomorphicMaps.coordinateDomain f e d := by
    refine ⟨hz, ?_⟩
    change f (e.val.symm z) ∈ (complexChartAt (n := 1) (f (e.val.symm z))).val.source
    exact mem_complexChartAt_source _
  let F := HolomorphicMaps.coordinateMap f e d
  let L := fderiv ℝ F z
  have hvec : L ∘ ![v, Complex.I • v] = ![L v, Complex.I • L v] := by
    funext i
    fin_cases i
    · rfl
    · exact HolomorphicMaps.coordinateMap_fderiv_map_smul_complex
        (contMDiff_originalBlowupDirection hs) e d hzd Complex.I v
  change (ClosedRealOneOneForm.pullback (contMDiff_originalBlowupDirection hs)
    (SGPT.Projective.ComplexProjectiveSpace.fsClosedForm (N := 1))).val.coeff
      e z ![v, Complex.I • v] ≥ 0
  rw [ClosedRealOneOneForm.pullback_val,
    SmoothRealForm.pullback_coeff (contMDiff_originalBlowupDirection hs) _ e d hzd,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, hvec]
  exact KahlerDomination.lineValue_nonneg_of_isHermitian
    (SGPT.Projective.ComplexProjectiveSpace.fsBackground (N := 1)).isKahler.1
    d (HolomorphicMaps.coordinateMap_mem_target hzd) (L v)

theorem originalPencilPullbackForm_nef
    (omega : KahlerBackground 2 (PolytopeToricVariety blowupGenerator hs)) :
    NefWithRespectTo omega (originalPencilPullbackForm hs) :=
  NefMixedMass.nefWithRespectTo_of_isSemipositive
    (originalPencilPullbackForm_isSemipositive hs)

end SGPT.BDivisor.StrictPencilNext
