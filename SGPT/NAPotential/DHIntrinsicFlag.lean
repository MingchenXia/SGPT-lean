import SGPT.NAPotential.DHIntrinsicCore
import SGPT.NAPotential.DHMeasure

/-! Comparison of the intrinsic Stieltjes construction with the existing
flag construction, for a supplied flag in positive dimension. -/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.NAPotential.DH

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Okounkov

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}
  [MeasurableSpace F.carrier] [BorelSpace F.carrier]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) F.carrier)}

/-- The intrinsic construction is the existing source flag measure. -/
theorem naIntrinsicDuistermaatHeckman_eq_flag
    (omega : KahlerBackground (m + 1) F.carrier)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γ : SourcePositiveIModelTestCurve θ) :
    naIntrinsicDuistermaatHeckman omega Γ = naDuistermaatHeckman (F := F) hbig Γ := by
  apply measure_eq_of_Ici_of_Ioi_eq_zero _ _ Γ.val.max
  · exact naIntrinsicDuistermaatHeckman_Ioi_max omega Γ
  · exact naDuistermaatHeckman_Ioi_max hbig Γ
  · intro t ht
    rw [naIntrinsicDuistermaatHeckman_Ici omega Γ ⟨t, ht⟩,
      naDuistermaatHeckman_Ici hbig Γ ⟨t, ht⟩]

end SGPT.NAPotential.DH
