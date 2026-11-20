import SGPT.PSH.SourceTestCurveMassContinuity
import SGPT.PSH.SourceNonArchimedeanVolume
import Mathlib.MeasureTheory.Measure.Stieltjes

/-! # Intrinsic Duistermaat--Heckman measure

The Lebesgue--Stieltjes measure of minus the actual slice-mass function
constructs a flag-free measure directly in
all dimensions. At the cutoff the zero extension can have a jump, hence an
atom there is allowed.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.NAPotential.DH

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ConnectedSpace M] {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The negative of the actual finite slice masses, extended by zero at and
above the cutoff. -/
def naDHStieltjes (omega : KahlerBackground n M) (Γ : SourcePositiveIModelTestCurve θ) :
    StieltjesFunction ℝ where
  toFun t := -sourceTestCurveRealMassAt omega Γ.val t
  mono' := by
    intro x y hxy
    exact neg_le_neg ((sourceTestCurveRealMassAt_antitone omega Γ.val) hxy)
  right_continuous' t := by
    by_cases ht : t < Γ.val.max
    · exact ((sourceTestCurveRealMassAt_continuousAt omega Γ.val ht).neg).continuousWithinAt
    · refine (continuousWithinAt_const : ContinuousWithinAt (fun _ : ℝ => (0 : ℝ)) (Ici t) t).congr_of_mem
        (g := fun x : ℝ => -sourceTestCurveRealMassAt omega Γ.val x) ?_ (show t ∈ Ici t from by simp)
      intro x hx
      have hx' : ¬ x < Γ.val.max := not_lt.mpr ((not_lt.mp ht).trans hx)
      simp [sourceTestCurveRealMassAt, hx']

omit [ConnectedSpace M] in
theorem naDHStieltjes_tendsto_atTop (omega : KahlerBackground n M)
    (Γ : SourcePositiveIModelTestCurve θ) :
    Tendsto (naDHStieltjes omega Γ) atTop (𝓝 (0 : ℝ)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop Γ.val.max] with t ht
  simp [naDHStieltjes, sourceTestCurveRealMassAt, not_lt.mpr ht]

theorem naDHStieltjes_tendsto_atBot (omega : KahlerBackground n M)
    (Γ : SourcePositiveIModelTestCurve θ) :
    Tendsto (naDHStieltjes omega Γ) atBot
      (𝓝 (-(sourceNAVolume (sourcePositiveTestCurveToNA Γ)).toReal)) := by
  have h := (tendsto_comp_val_Iio_atBot (a := Γ.val.max)).mp
    (sourceTestCurveRealMassAt_tendsto_atBot omega Γ.val)
  rw [sourceNAVolume_positiveTestCurve omega Γ]
  exact h.neg

/-- A finite measure intrinsically associated to the original curve. -/
def naIntrinsicDuistermaatHeckman (omega : KahlerBackground n M)
    (Γ : SourcePositiveIModelTestCurve θ) : Measure ℝ :=
  (naDHStieltjes omega Γ).measure

instance naIntrinsicDuistermaatHeckman_finite (omega : KahlerBackground n M)
    (Γ : SourcePositiveIModelTestCurve θ) :
    IsFiniteMeasure (naIntrinsicDuistermaatHeckman omega Γ) :=
  (naDHStieltjes omega Γ).isFiniteMeasure
    (naDHStieltjes_tendsto_atBot omega Γ) (naDHStieltjes_tendsto_atTop omega Γ)

omit [ConnectedSpace M] in
theorem naIntrinsicDuistermaatHeckman_Ici (omega : KahlerBackground n M)
    (Γ : SourcePositiveIModelTestCurve θ) (t : Iio Γ.val.max) :
    naIntrinsicDuistermaatHeckman omega Γ (Ici (t : ℝ)) =
      sourcePotentialNonPluripolarMeasure θ (Γ.val.potential t) (Γ.val.thetaPSH t) univ := by
  have hc : ContinuousAt (naDHStieltjes omega Γ) (t : ℝ) :=
    (sourceTestCurveRealMassAt_continuousAt omega Γ.val t.property).neg
  have hl := ((naDHStieltjes omega Γ).mono.continuousWithinAt_Iio_iff_leftLim_eq).mp
    hc.continuousWithinAt
  rw [naIntrinsicDuistermaatHeckman, (naDHStieltjes omega Γ).measure_Ici
    (naDHStieltjes_tendsto_atTop omega Γ), hl]
  change ENNReal.ofReal (0 - -sourceTestCurveRealMassAt omega Γ.val t.val) = _
  rw [sub_neg_eq_add, zero_add, sourceTestCurveRealMassAt_of_lt omega Γ.val t.property,
    ENNReal.ofReal_toReal (Γ.val.mass_lt_top omega t).ne]

omit [ConnectedSpace M] in
theorem naIntrinsicDuistermaatHeckman_Ioi_max (omega : KahlerBackground n M)
    (Γ : SourcePositiveIModelTestCurve θ) :
    naIntrinsicDuistermaatHeckman omega Γ (Ioi Γ.val.max) = 0 := by
  rw [naIntrinsicDuistermaatHeckman, (naDHStieltjes omega Γ).measure_Ioi
    (naDHStieltjes_tendsto_atTop omega Γ)]
  simp [naDHStieltjes, sourceTestCurveRealMassAt]

theorem naIntrinsicDuistermaatHeckman_univ (omega : KahlerBackground n M)
    (Γ : SourcePositiveIModelTestCurve θ) :
    naIntrinsicDuistermaatHeckman omega Γ univ =
      sourceNAVolume (sourcePositiveTestCurveToNA Γ) := by
  rw [naIntrinsicDuistermaatHeckman, (naDHStieltjes omega Γ).measure_univ
    (naDHStieltjes_tendsto_atBot omega Γ) (naDHStieltjes_tendsto_atTop omega Γ)]
  simpa only [sub_neg_eq_add, zero_add] using
    ENNReal.ofReal_toReal (sourceNAVolume_lt_top omega (sourcePositiveTestCurveToNA Γ)).ne

end SGPT.NAPotential.DH
