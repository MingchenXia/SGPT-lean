import SGPT.PSH.SourceTestCurveSum
import SGPT.PSH.SourceTestCurveOriginalTranslation

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

private theorem shift_cutoff_eq (Γ : SourceTestCurvePredata θ) (a : ℝ) :
    sourceTestCurveCutoff (Γ.shift a) = sourceTestCurveCutoff Γ := by
  funext x
  change (⨅ r, (Γ.shift a).potential r x) = ⨅ s, Γ.potential s x
  apply le_antisymm
  · apply le_iInf
    intro s
    let r : Iio (Γ.shift a).max := ⟨s.1-a, by
      change s.1-a < Γ.max-a
      have hs : s.1 < Γ.max := s.2
      linarith⟩
    have hr : r.1+a = s.1 := by dsimp [r]; ring
    simpa only [SourceTestCurvePredata.shift, hr] using
      (iInf_le (fun q : Iio (Γ.shift a).max => (Γ.shift a).potential q x) r)
  · apply le_iInf
    intro r
    have hr : r.1+a < Γ.max := by
      have hs : r.1 < Γ.max-a := r.2
      linarith
    exact iInf_le (fun s : Iio Γ.max => Γ.potential s x) ⟨r.1+a,hr⟩

/-- Exact whole-extension parameter translation, including the actual cutoff infimum. -/
theorem SourceTestCurvePredata.shift_at (Γ : SourceTestCurvePredata θ) (a r : ℝ) :
    sourceTestCurveAt (Γ.shift a) r = sourceTestCurveAt Γ (r+a) := by
  by_cases ht : r < Γ.max-a
  · have hs : r+a < Γ.max := by linarith
    rw [sourceTestCurveAt_of_lt (Γ.shift a) ht, sourceTestCurveAt_of_lt Γ hs]
    rfl
  · by_cases he : r = Γ.max-a
    · subst r
      have harg : Γ.max-a+a = Γ.max := by ring
      rw [harg]
      change sourceTestCurveAt (Γ.shift a) (Γ.shift a).max = sourceTestCurveAt Γ Γ.max
      rw [sourceTestCurveAt_eq_max (Γ.shift a), sourceTestCurveAt_eq_max Γ, shift_cutoff_eq]
    · have hg : Γ.max-a < r := lt_of_le_of_ne (le_of_not_gt ht) (Ne.symm he)
      rw [sourceTestCurveAt_of_gt (Γ.shift a) hg,
        sourceTestCurveAt_of_gt Γ (show Γ.max < r+a by linarith)]

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

omit [BorelSpace M] [ConnectedSpace M] in
/-- The original additive convention on EVERY real whole-extension parameter. -/
theorem SourceTestCurve.translate_at (Γ : SourceTestCurve θ) (C r : ℝ) :
    sourceTestCurveAt (Γ.translate C).toSourceTestCurvePredata r =
      sourceTestCurveAt Γ.toSourceTestCurvePredata (r-C) := by
  change sourceTestCurveAt (Γ.toSourceTestCurvePredata.shift (-C)) r = _
  simpa only [sub_eq_add_neg] using Γ.toSourceTestCurvePredata.shift_at (-C) r

omit [BorelSpace M] [ConnectedSpace M] in
/-- Actual whole-real parameter reindexing for translation of the left raw summand. -/
theorem sourceTestCurveRawSum_translate_left (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ)
    (C τ : ℝ) :
    sourceTestCurveRawSum (Γ.translate C).toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ =
      sourceTestCurveRawSum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata (τ-C) := by
  funext x
  simp only [sourceTestCurveRawSum, SourceTestCurve.translate_at]
  apply le_antisymm
  · apply iSup_le
    intro r
    have he : (τ-C)-(r-C) = τ-r := by ring
    simpa only [he] using
      (le_iSup (fun q : ℝ => sourceTestCurveAt Γ.toSourceTestCurvePredata q x +
        sourceTestCurveAt Δ.toSourceTestCurvePredata ((τ-C)-q) x) (r-C))
  · apply iSup_le
    intro q
    have hΓ : (q+C)-C = q := by ring
    have hΔ : τ-(q+C) = (τ-C)-q := by ring
    simpa only [hΓ, hΔ] using
      (le_iSup (fun r : ℝ => sourceTestCurveAt Γ.toSourceTestCurvePredata (r-C) x +
        sourceTestCurveAt Δ.toSourceTestCurvePredata (τ-r) x) (q+C))

omit [BorelSpace M] [ConnectedSpace M] in
/-- Literal same-index affine argument identity for translation of the right raw summand. -/
theorem sourceTestCurveRawSum_translate_right (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ)
    (C τ : ℝ) :
    sourceTestCurveRawSum Γ.toSourceTestCurvePredata (Δ.translate C).toSourceTestCurvePredata τ =
      sourceTestCurveRawSum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata (τ-C) := by
  funext x
  simp only [sourceTestCurveRawSum, SourceTestCurve.translate_at]
  apply iSup_congr
  intro r
  rw [show (τ-r)-C = (τ-C)-r by ring]

/-- Translation of the genuine sum is the genuine sum with translated left input. -/
theorem SourceTestCurve.sum_translate_left (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ) (C : ℝ) :
    (SourceTestCurve.sum omega Γ Δ).translate C =
      SourceTestCurve.sum omega (Γ.translate C) Δ := by
  apply SourceTestCurve.ext_of_max_potential
  · simp only [SourceTestCurve.translate_max, SourceTestCurve.sum_max]
    ring
  · intro r hr hs
    simp only [SourceTestCurve.translate_potential, SourceTestCurve.sum_potential,
      sourceTestCurveRawSum_translate_left]

/-- Translation of the genuine sum is the genuine sum with translated right input. -/
theorem SourceTestCurve.sum_translate_right (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ) (C : ℝ) :
    (SourceTestCurve.sum omega Γ Δ).translate C =
      SourceTestCurve.sum omega Γ (Δ.translate C) := by
  apply SourceTestCurve.ext_of_max_potential
  · simp only [SourceTestCurve.translate_max, SourceTestCurve.sum_max]
    ring
  · intro r hr hs
    simp only [SourceTestCurve.translate_potential, SourceTestCurve.sum_potential,
      sourceTestCurveRawSum_translate_right]

/-- Both clauses of the original test-curve translation proposition. -/
theorem source_test_curve_translation_whole (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ) (C C' : ℝ) :
    (SourceTestCurve.sum omega Γ Δ).translate C =
        SourceTestCurve.sum omega Γ (Δ.translate C) ∧
      SourceTestCurve.sum omega Γ (Δ.translate C) =
        SourceTestCurve.sum omega (Γ.translate C) Δ ∧
      Γ.translate (C+C') = (Γ.translate C).translate C' :=
  ⟨SourceTestCurve.sum_translate_right omega Γ Δ C,
    (SourceTestCurve.sum_translate_right omega Γ Δ C).symm.trans
      (SourceTestCurve.sum_translate_left omega Γ Δ C),
    (Γ.translate_translate C C').symm⟩

end SGPT.PSH.VariableComplexAtlas
