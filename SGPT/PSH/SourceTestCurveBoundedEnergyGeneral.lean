import SGPT.PSH.SourceTestCurveBoundedEnergy
import SGPT.PSH.SourceTestCurveShift

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter MeasureTheory Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  {φ : M → EReal} {hφ : SourceModelPotential θ φ}

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem ereal_eq_coe_of_sub_eq {a : EReal} {c r : ℝ}
    (h : a - (c : EReal) = (r : EReal)) : a = ((r + c : ℝ) : EReal) := by
  cases a <;> simp_all [← EReal.coe_sub]
  norm_cast
  linarith

/-- Genuine boundedness alone produces actual finite test-curve energy
at every original real cutoff, before taking its real reader. -/
theorem SourceTestCurve.boundedEnergy_finite_all_cutoffs (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ) :
    Γ ∈ SourceFiniteEnergyTestCurves omega θ φ hφ ∧
      sourceTestCurveEnergy omega hφ Γ hΓ.1 =
        (((sourceTestCurveEnergy omega hφ Γ hΓ.1).toReal : ℝ) : EReal) := by
  have hb := (Γ.shift_bounded_iff hφ Γ.max).mpr hΓ
  have hz := (source_test_curve_zero_cutoff_normalization omega hφ Γ hΓ.1).1
  obtain ⟨hf, L, _, _, hE⟩ := (Γ.shift Γ.max).boundedEnergy_finite omega hb hz
  have hfinite : sourceTestCurveEnergy omega hφ (Γ.shift Γ.max) hb.1 =
      (((sourceTestCurveEnergy omega hφ (Γ.shift Γ.max) hb.1).toReal : ℝ) : EReal) := by
    rw [hE, EReal.toReal_coe]
  have hshift := Γ.shift_energy omega hφ hΓ.1 Γ.max
  have hco := ereal_eq_coe_of_sub_eq (hshift.symm.trans hfinite)
  refine ⟨(Γ.shift_finiteEnergy_iff omega hφ Γ.max).mp hf, ?_⟩
  rw [hco, EReal.toReal_coe]

omit [ConnectedSpace M] in
private theorem actual_energy_add_const (omega : KahlerBackground n M)
    (u : M → EReal) (c : ℝ) :
    sourceRelativeEnergy θ φ (fun x ↦ u x + (c : EReal)) hφ =
      sourceRelativeEnergy θ φ u hφ +
        ((c * (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal : ℝ) : EReal) := by
  rw [sourceRelativeEnergy_eq_native,
    SingularModelEnergyExtendedTranslation.energy_add_const omega u c,
    sourceRelativeEnergy_eq_native]
  rfl

/-- The SAME defining energies of the original assigned ray and original
bounded test curve agree at EVERY nonnegative time and EVERY real cutoff. -/
theorem SourceTestCurve.boundedLegendre_assigned_energy_identity_all_cutoffs
    (omega : KahlerBackground n M) (Γ : SourceTestCurve θ)
    (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ) (t : Ici (0 : ℝ)) :
    sourceRelativeEnergy θ φ (sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata t) hφ =
        ((t.1 * (sourceTestCurveEnergy omega hφ Γ hΓ.1).toReal : ℝ) : EReal) ∧
    sourceRelativeEnergy θ φ (sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata t) hφ =
        (t.1 : EReal) * sourceTestCurveEnergy omega hφ Γ hΓ.1 := by
  let V := (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal
  have hb := (Γ.shift_bounded_iff hφ Γ.max).mpr hΓ
  have hz := (source_test_curve_zero_cutoff_normalization omega hφ Γ hΓ.1).1
  have hfinite := (Γ.boundedEnergy_finite_all_cutoffs omega hΓ).2
  have hshift := Γ.shift_energy omega hφ hΓ.1 Γ.max
  have hreal : (sourceTestCurveEnergy omega hφ (Γ.shift Γ.max) hb.1).toReal =
      (sourceTestCurveEnergy omega hφ Γ hΓ.1).toReal - Γ.max * V := by
    rw [hshift, hfinite, ← EReal.coe_sub, EReal.toReal_coe]
    simp only [EReal.toReal_coe, V]
  have hnorm := (Γ.shift Γ.max).boundedLegendre_assigned_energy_identity omega hb hz t
  have hfun : sourceTestCurveLegendreRay (Γ.shift Γ.max).toSourceTestCurvePredata t =
      fun x ↦ sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata t x -
        ((t.1 * Γ.max : ℝ) : EReal) :=
    Γ.toSourceTestCurvePredata.shift_legendreRay Γ.max t
  have htranslate : sourceRelativeEnergy θ φ
      (sourceTestCurveLegendreRay (Γ.shift Γ.max).toSourceTestCurvePredata t) hφ =
      sourceRelativeEnergy θ φ (sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata t) hφ -
        ((t.1 * Γ.max * V : ℝ) : EReal) := by
    rw [hfun]
    have hfn : (fun x ↦ sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata t x -
        ((t.1 * Γ.max : ℝ) : EReal)) =
        (fun x ↦ sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata t x +
          ((-(t.1 * Γ.max) : ℝ) : EReal)) := by
      funext x
      simp only [sub_eq_add_neg, EReal.coe_neg]
    rw [hfn, actual_energy_add_const omega]
    simp only [neg_mul, EReal.coe_neg, sub_eq_add_neg, V]
  have hco := ereal_eq_coe_of_sub_eq (htranslate.symm.trans hnorm.1)
  have hresult : sourceRelativeEnergy θ φ
      (sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata t) hφ =
      ((t.1 * (sourceTestCurveEnergy omega hφ Γ hΓ.1).toReal : ℝ) : EReal) := by
    rw [hco]
    congr 1
    rw [hreal]
    ring
  refine ⟨hresult, ?_⟩
  rw [hfinite, ← EReal.coe_mul]
  exact hresult

/-- At every strictly positive time the actual raw transform is the
original assigned-ray potential, so its same defining energy identity holds. -/
theorem SourceTestCurve.boundedLegendre_energy_identity_all_cutoffs
    (omega : KahlerBackground n M) (Γ : SourceTestCurve θ)
    (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ) {t : ℝ} (ht : 0 < t) :
    sourceRelativeEnergy θ φ (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t) hφ =
        ((t * (sourceTestCurveEnergy omega hφ Γ hΓ.1).toReal : ℝ) : EReal) ∧
    sourceRelativeEnergy θ φ (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t) hφ =
        (t : EReal) * sourceTestCurveEnergy omega hφ Γ hΓ.1 := by
  have h := Γ.boundedLegendre_assigned_energy_identity_all_cutoffs omega hΓ ⟨t, ht.le⟩
  simpa only [sourceTestCurveLegendreRay, sourceTestCurveLegendreWithInitial,
    if_neg (ne_of_gt ht)] using h

end SGPT.PSH.VariableComplexAtlas
