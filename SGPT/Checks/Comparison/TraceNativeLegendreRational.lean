import SGPT.NAPotential.BJPrepDivisorialTransform
import SGPT.NAPotential.GFRationalCofinality

/-! The EXISTING original native divisorial transform, at rational parameters.
Blueprint: `trace-native-rational-sup.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace SGPT.NAPotential.TraceComparison

open Set
open SGPT.NAPotential.BJ.GfIm.RationalHull SGPT.PSH.CompactPrimeOver SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped ENNReal

/-- Exact rational cofinality for every actual antitone family on its
ORIGINAL open parameter interval, retaining every infinite value. -/
theorem antitone_subtype_parameterSup_eq_rational {T : ℝ} (F : Iio T → EReal) (hF : Antitone F) :
    (⨆ s : Iio T, F s + ((s : ℝ) : EReal)) =
      ⨆ q : ℚ, ⨆ (hq : (q : ℝ) < T), F ⟨q, hq⟩ + ((q : ℝ) : EReal) := by
  apply le_antisymm
  · refine iSup_le fun s => ?_
    apply (add_real_le_rational_iSup (F s) (s : ℝ)).trans
    refine iSup_le fun q => iSup_le fun hq => ?_
    exact le_iSup_of_le q (le_iSup_of_le (hq.trans s.2)
      (add_le_add (hF (show (⟨q, hq.trans s.2⟩ : Iio T) ≤ s from hq.le)) le_rfl))
  · exact iSup_le fun q => iSup_le fun hq => le_iSup
      (fun s : Iio T => F s + ((s : ℝ) : EReal)) ⟨q, hq⟩

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Rational cofinality for the original native curve transform itself. -/
theorem curveDivisorialTransform_eq_rational_parameterSup
    {σ : AtlasClosedRealOneOneForm (ofFixedModel n M)} (C : SourceTestCurvePredata σ)
    (p : PrimePresentation n M) (c : ℝ) (hc : 0 ≤ c) :
    BJPrep.curveDivisorialTransform C p c =
      ⨆ q : ℚ, ⨆ (hq : (q : ℝ) < C.max),
        -((c : EReal) * ((presentationReader (C.potential ⟨q, hq⟩) p : ℝ≥0∞) : EReal)) +
          ((q : ℝ) : EReal) := by
  let F : Iio C.max → EReal := fun s => -((c : EReal) * ((presentationReader (C.potential s) p : ℝ≥0∞) : EReal))
  have hF : Antitone F := by
    intro s t hst
    change -((c : EReal) * ((presentationReader (C.potential t) p : ℝ≥0∞) : EReal)) ≤
      -((c : EReal) * ((presentationReader (C.potential s) p : ℝ≥0∞) : EReal))
    apply EReal.neg_le_neg_iff.mpr
    apply mul_le_mul_of_nonneg_left _ (EReal.coe_nonneg.mpr hc)
    exact_mod_cast BJPrep.presentationReader_anti (fun x => C.antitone x hst) p
  calc
    BJPrep.curveDivisorialTransform C p c =
        ⨆ s : Iio C.max, F s + ((s : ℝ) : EReal) := by
      rw [iSup_subtype]
      apply iSup_congr
      intro τ
      apply iSup_congr
      intro hτ
      exact (sub_eq_add_neg _ _).trans (add_comm _ _)
    _ = _ := antitone_subtype_parameterSup_eq_rational F hF

/-- The EXISTING unchanged original native NA divisorial transform equals
its literal rational slice supremum. Its monotonicity follows from the
actual original curve and actual prime reader, not from a supplied square. -/
theorem naDivisorialTransform_eq_rational_parameterSup (Γ : SourceNAPotential θ)
    (κ : SourceKahlerForm n M) (p : PrimePresentation n M) (c : ℝ) (hc : 0 ≤ c) :
    BJPrep.naDivisorialTransform Γ κ p c =
      ⨆ q : ℚ, ⨆ (hq : (q : ℝ) < (Γ.component κ).val.max),
        -((c : EReal) * ((presentationReader ((Γ.component κ).val.potential ⟨q, hq⟩) p : ℝ≥0∞) : EReal)) +
          ((q : ℝ) : EReal) :=
  curveDivisorialTransform_eq_rational_parameterSup
    (Γ.component κ).val.toSourceTestCurvePredata p c hc

end SGPT.NAPotential.TraceComparison
