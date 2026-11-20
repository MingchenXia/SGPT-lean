import SGPT.BDivisor.StrictVolume.PencilCurvature
import SGPT.Toric.ExceptionalSelfIntersection
import SGPT.Toric.SmoothMongeAmpereMass
import SGPT.Envelopes.SourceClassVolume
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Genuine physical H-E, its segment polytope, and actual native/source volume zero. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.BDivisor.StrictPencilNext

open Set MeasureTheory
open SGPT.Toric SGPT.Toric.BlowdownDraft SGPT.Toric.F1IntersectionDraft
open SGPT.Projective.FsNormalizationNext
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.NefMixedMass
open scoped BigOperators ENNReal

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

theorem originalPencilDivisor_eq_H_sub_E :
    blowupDirectionDivisor hs = blowupHyperplaneDivisor hs - originalExceptionalDivisor hs := by
  classical
  funext rho
  change (if rho.val = blowupRay4 then (1 : ℤ) else if rho.val = blowupRay7 then -1 else 0) =
    (if rho.val = blowupRay4 then 1 else 0) - (if rho.val = blowupRay7 then 1 else 0)
  by_cases h4 : rho.val = blowupRay4
  · have h7 : rho.val ≠ blowupRay7 := by
      rw [h4]
      decide
    simp only [if_pos h4, if_neg h7, sub_zero]
  · by_cases h7 : rho.val = blowupRay7
    · simp only [if_neg h4, if_pos h7, zero_sub]
    · simp only [if_neg h4, if_neg h7, sub_self]

theorem originalPencil_toricDivisorPolytope :
    toricDivisorPolytope (blowupDirectionDivisor hs) =
      {u | 0 ≤ u 0 ∧ 0 ≤ u 1 ∧ u 0 + u 1 = 1} := by
  rw [blowupDirectionDivisor, blowup_toricDivisorPolytope]
  ext u
  norm_num [blowupDirectionCoeff, blowupRay4, blowupRay5, blowupRay6, blowupRay7]
  constructor
  · rintro ⟨h4, h5, h6, h7⟩
    exact ⟨h5, h6, by linarith⟩
  · rintro ⟨h0, h1, heq⟩
    exact ⟨by linarith, h0, h1, by linarith⟩

theorem originalPencil_polytope_volume_zero :
    volume (toricDivisorPolytope (blowupDirectionDivisor hs)) = 0 := by
  let A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
    { carrier := {u | u 0 + u 1 = 1}
      smul_vsub_vadd_mem' := by
        intro c a b d ha hb hd
        change c * (a 0 - b 0) + d 0 + (c * (a 1 - b 1) + d 1) = 1
        change a 0 + a 1 = 1 at ha
        change b 0 + b 1 = 1 at hb
        change d 0 + d 1 = 1 at hd
        linear_combination c * ha - c * hb + hd }
  have hne : A ≠ ⊤ := by
    intro h
    have hmem : (0 : EuclideanSpace ℝ (Fin 2)) ∈ A := by
      rw [h]
      trivial
    change (0 : ℝ) + 0 = 1 at hmem
    norm_num at hmem
  refine measure_mono_null ?_ (Measure.addHaar_affineSubspace volume A hne)
  intro u hu
  rw [originalPencil_toricDivisorPolytope] at hu
  exact hu.2.2

private theorem pencilPolytope_nonempty :
    (toricDivisorPolytope (blowupDirectionDivisor hs)).Nonempty :=
  ⟨latticeVector (blowupDirectionExponent 0), blowupDirectionExponent_mem hs 0⟩

theorem originalPencil_sourceClassVolume_zero :
    sourceClassVolume (RealBottChern.ofRepresentative (originalPencilFsMetric hs).form) = 0 := by
  let h := originalPencilFsMetric hs
  let omega := polytopeToricKahlerBackground blowupGenerator hs
  have hP := pencilPolytope_nonempty hs
  calc
    _ = sourceClassVolume (RealBottChern.ofRepresentative (atlasClosedFormToNative h.atlasForm)) := by
      rw [BigToricMetric.atlasForm, sourceNativeAtlasForm_roundTrip]
    _ = h.MA (h.minimalEnvelope_mem hP) univ :=
      sourceClassVolume_eq_minimalEnvelope_mass omega (h.minimalEnvelope_mem hP).1
    _ = ((2 : ℕ).factorial : ENNReal) * volume (toricDivisorPolytope (blowupDirectionDivisor hs)) :=
      h.MA_minimalEnvelope_univ hP
    _ = 0 := by rw [originalPencil_polytope_volume_zero]; simp

theorem originalPencil_nativeSelfIntersection_zero
    (omega : KahlerBackground 2 (PolytopeToricVariety blowupGenerator hs)) :
    slotIntegral omega (fun _ : Fin 2 => (originalPencilFsMetric hs).form) = 0 := by
  let h := originalPencilFsMetric hs
  have hsemi := originalPencilFsMetric_isSemipositive hs
  rw [← toricSmoothMetric_zero_MA_eq_nativeIntegral h hsemi omega]
  change (h.MA (toricSmoothMetric_zero_mem h hsemi) univ).toReal = 0
  rw [toricSmoothMetric_zero_MA_univ h hsemi (pencilPolytope_nonempty hs),
    originalPencil_polytope_volume_zero]
  simp

end SGPT.BDivisor.StrictPencilNext
