import SGPT.Foundations.Analysis.Pending.ActualWeightedGlobalFormChartTests
import SGPT.Foundations.Analysis.FirstPass.GlobalCurrents

set_option autoImplicit false

/-! # Actual chart independence for weighted global differential forms

The full mathematical statement and proof preceded this source.
-/

noncomputable section

open Set TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.ActualWeightedGlobalFormOverlapPairing

open FirstPass ActualWeightedGlobalFormChartTests

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Internally constructed weighted global-form tests keep their actual current pairing. -/
theorem exists_tests_with_pairing {k : CurrentDegree n} (T : GlobalCurrent n M k)
    (γ : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val))
    (e f : ComplexChart n M) (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ)
    (hcompact : IsCompact (tsupport χ))
    (hsupport : tsupport χ ⊆ e.val.source ∩ f.val.source) :
    ∃ ηe : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget e)
        (Module.finrank ℝ (ComplexModel n) - k.val),
    ∃ ηf : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget f)
        (Module.finrank ℝ (ComplexModel n) - k.val),
      (∀ z, ηe z = e.val.target.indicator (fun y => χ (e.val.symm y) • γ.coeff e y) z) ∧
      (∀ z, ηf z = f.val.target.indicator (fun y => χ (f.val.symm y) • γ.coeff f y) z) ∧
      T.inChart e ηe = T.inChart f ηf := by
  classical
  obtain ⟨ηe, he, hse⟩ := exists_testForm e γ χ hχ hcompact
    (fun x hx => (hsupport hx).1)
  obtain ⟨ηf, hf, hsf⟩ := exists_testForm f γ χ hχ hcompact
    (fun x hx => (hsupport hx).2)
  have hseO : tsupport (ηe : ComplexModel n → _) ⊆ overlapSource e f := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hse hz
    change e.val x ∈ e.val.target ∧ e.val.symm (e.val x) ∈ f.val.source
    exact ⟨e.val.map_source (hsupport hx).1,
      by rw [e.val.left_inv (hsupport hx).1]; exact (hsupport hx).2⟩
  have hsfO : tsupport (ηf : ComplexModel n → _) ⊆ overlapTarget e f := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hsf hz
    change f.val x ∈ f.val.target ∧ f.val.symm (f.val x) ∈ e.val.source
    exact ⟨f.val.map_source (hsupport hx).2,
      by rw [f.val.left_inv (hsupport hx).2]; exact (hsupport hx).1⟩
  let ηes : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (overlapSource e f)
      (Module.finrank ℝ (ComplexModel n) - k.val) :=
    ⟨ηe, ηe.contDiff, ηe.hasCompactSupport, hseO⟩
  let ηfs : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (overlapTarget e f)
      (Module.finrank ℝ (ComplexModel n) - k.val) :=
    ⟨ηf, ηf.contDiff, ηf.hasCompactSupport, hsfO⟩
  have hrel : OverlapTestRelated e f ηes ηfs := by
    intro z hz v
    have hzO := hz
    change z ∈ e.val.target ∧ e.val.symm z ∈ f.val.source at hz
    have hFtarget : chartTransition e f z ∈ f.val.target :=
      f.val.map_source hz.2
    have hsame : f.val.symm (chartTransition e f z) = e.val.symm z :=
      f.val.left_inv hz.2
    change ηe z v = ηf (chartTransition e f z)
      (fun i => chartTransitionDerivative e f z (v i))
    rw [he z, hf (chartTransition e f z), indicator_of_mem hz.1,
      indicator_of_mem hFtarget]
    change χ (e.val.symm z) * γ.coeff e z v =
      χ (f.val.symm (chartTransition e f z)) * γ.coeff f (chartTransition e f z)
        (fun i => chartTransitionDerivative e f z (v i))
    rw [hsame, γ.compatible e f z hzO v]
  have hp := T.overlap e f ηes ηfs hrel
  change T.inChart e (TestFunction.monoCLM ℝ ηes) =
    T.inChart f (TestFunction.monoCLM ℝ ηfs) at hp
  have hincE : (TestFunction.monoCLM ℝ ηes :
      _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget e)
        (Module.finrank ℝ (ComplexModel n) - k.val)) = ηe := by
    apply TestFunction.ext
    intro z
    exact _root_.SGPT.Foundations.Analysis.LocalCurrents.testForm_inclusion_apply
      (overlapSource_le e f) ηes z
  have hincF : (TestFunction.monoCLM ℝ ηfs :
      _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget f)
        (Module.finrank ℝ (ComplexModel n) - k.val)) = ηf := by
    apply TestFunction.ext
    intro z
    exact _root_.SGPT.Foundations.Analysis.LocalCurrents.testForm_inclusion_apply
      (overlapTarget_le e f) ηfs z
  exact ⟨ηe, ηf, he, hf, by simpa only [hincE, hincF] using hp⟩

end SGPT.Foundations.Analysis.Pending.ActualWeightedGlobalFormOverlapPairing
