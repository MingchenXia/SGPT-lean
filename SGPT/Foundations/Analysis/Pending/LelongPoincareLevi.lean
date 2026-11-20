import SGPT.Foundations.Analysis.Pending.LelongPoincareSlices
import SGPT.Foundations.Analysis.FirstPass.LocalCurrents
import SGPT.Foundations.Analysis.TestLeviPairing

/-!
# `ddᶜ log |G|²` as a distribution-valued form: its Levi coefficient is the slice measure

The project's local currents (`FirstPass.LocalCurrents`) are distribution-valued forms, with
`ddᶜ = (i/2π) ∂∂̄` (`LocalCurrents.ddC`), and `ddᶜT(v, iv) = π⁻¹ Levi_v T`
(`LocalCurrents.ddC_complexLine`).  For `G` on an open set `Ω ⊆ ℂ × E` whose slices along the
first factor are meromorphic and nowhere locally zero, the coefficient of `ddᶜ log |G|²` on the
complex line of the first factor is the slice measure of the divisor of `G`:

  `ddᶜ (log |G|²) ((1,0), i(1,0)) (φ) = ∫_w ∑_s ord_s (G (·, w)) φ (s, w) dw`

(`ddC_log_normSq_apply_first`).  For `G (s, w) = sᵐ v (s, w)` with `v` without zeros this is
`m ∫ φ (0, w) dw`, the current of the hyperplane `{s = 0}` with multiplicity `m`
(`ddC_log_normSq_pow_mul_apply_first`).

This is the Lelong--Poincaré equation `ddᶜ log |G|² = [div G]` read on one complex direction, in
the project's current formalism (step LP3 of `ana:divisor-lelong-poincare`; blueprint
`ana:lelong-poincare-slices`).  Sorry-free.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Laplacian Distributions

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.LelongPoincareLevi

open LelongPoincareSlices

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E]
  [SFinite (volume : Measure E)]

omit [IsScalarTower ℝ ℂ E] [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E]
  [SFinite (volume : Measure E)] in
/-- The Levi form of a smooth function in the direction `(1, 0)` of `ℂ × E` is a quarter of its
Laplacian in the first variable. -/
theorem leviForm_first {χ : ℂ × E → ℝ} (hχ : ContDiff ℝ 2 χ) (z : ℂ × E) :
    leviForm χ z ((1 : ℂ), (0 : E)) = sliceLaplacian χ z / 4 := by
  have hI : Complex.I • ((1 : ℂ), (0 : E)) = (Complex.I, (0 : E)) := by
    simp
  rw [leviForm, hI, sliceLaplacian_eq hχ z, realHessian, realHessian]

omit [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [BorelSpace E]
  [SecondCountableTopology E]
  [SFinite (volume : Measure E)] in
theorem locallyIntegrableOn_log_norm_of_log_normSq {Ω : Set (ℂ × E)} {G : ℂ × E → ℂ}
    (hint : LocallyIntegrableOn (fun z => Real.log (‖G z‖ ^ 2)) Ω volume) :
    LocallyIntegrableOn (fun z => Real.log ‖G z‖) Ω volume := by
  have h := hint.smul (1 / 2 : ℝ)
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, Real.log_pow]
  push_cast
  ring

/-- **`ddᶜ log |G|²` on the first complex direction is the slice measure of the divisor.** -/
theorem ddC_log_normSq_apply_first {Ω : Opens (ℂ × E)} {G : ℂ × E → ℂ}
    (hG : ∀ᵐ w ∂(volume : Measure E), MeromorphicOn (fun s => G (s, w)) (sliceSet Ω w) ∧
      ∀ s : sliceSet Ω w, meromorphicOrderAt (fun s => G (s, w)) s ≠ ⊤)
    (hint : LocallyIntegrableOn (fun z => Real.log (‖G z‖ ^ 2)) Ω volume) (φ : 𝓓(Ω, ℝ)) :
    LocalCurrents.ddC (regularDistribution volume (fun z => Real.log (‖G z‖ ^ 2)) hint)
        ![((1 : ℂ), (0 : E)), Complex.I • ((1 : ℂ), (0 : E))] φ =
      ∫ w, ∑ᶠ s, (MeromorphicOn.divisor (fun s => G (s, w)) (sliceSet Ω w) s : ℝ) * φ (s, w) := by
  have hint' := locallyIntegrableOn_log_norm_of_log_normSq hint
  have hslice := integral_log_norm_mul_sliceLaplacian (μ := (volume : Measure E)) Ω.isOpen hG
    (by rwa [← Measure.volume_eq_prod]) φ.contDiff φ.hasCompactSupport φ.tsupport_subset
  rw [LocalCurrents.ddC_complexLine, smul_apply,
    distributionalLeviCLM_regularDistribution_apply, smul_eq_mul]
  have hpt : ∀ z : ℂ × E, Real.log (‖G z‖ ^ 2) * leviForm φ z ((1 : ℂ), (0 : E)) =
      (1 / 2 : ℝ) * (Real.log ‖G z‖ * sliceLaplacian φ z) := by
    intro z
    rw [leviForm_first (φ.contDiff.of_le ENat.LEInfty.out) z, Real.log_pow]
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_const_mul, Measure.volume_eq_prod, hslice]
  field_simp

/-- **The local model**: for `G = sᵐ v` with `v` continuous, holomorphic in `s` and without zeros
on `Ω`, `ddᶜ log |G|²` on the first complex direction is `m` times the hyperplane `{s = 0}`. -/
theorem ddC_log_normSq_pow_mul_apply_first [IsLocallyFiniteMeasure (volume : Measure E)]
    {Ω : Opens (ℂ × E)} (m : ℕ) {v : ℂ × E → ℂ} (hvc : ContinuousOn v Ω)
    (hva : ∀ w, AnalyticOnNhd ℂ (fun s => v (s, w)) (sliceSet Ω w)) (hv0 : ∀ z ∈ Ω, v z ≠ 0)
    (hint : LocallyIntegrableOn (fun z => Real.log (‖z.1 ^ m * v z‖ ^ 2)) Ω volume)
    (φ : 𝓓(Ω, ℝ)) :
    LocalCurrents.ddC (regularDistribution volume (fun z => Real.log (‖z.1 ^ m * v z‖ ^ 2)) hint)
        ![((1 : ℂ), (0 : E)), Complex.I • ((1 : ℂ), (0 : E))] φ =
      m * ∫ w, φ (0, w) := by
  have hslice := integral_log_norm_mul_sliceLaplacian_pow_mul' (μ := (volume : Measure E))
    Ω.isOpen m hvc hva hv0 φ.contDiff φ.hasCompactSupport φ.tsupport_subset
  rw [LocalCurrents.ddC_complexLine, smul_apply,
    distributionalLeviCLM_regularDistribution_apply, smul_eq_mul]
  have hpt : ∀ z : ℂ × E, Real.log (‖z.1 ^ m * v z‖ ^ 2) * leviForm φ z ((1 : ℂ), (0 : E)) =
      (1 / 2 : ℝ) * (Real.log ‖z.1 ^ m * v z‖ * sliceLaplacian φ z) := by
    intro z
    rw [leviForm_first (φ.contDiff.of_le ENat.LEInfty.out) z, Real.log_pow]
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_const_mul, Measure.volume_eq_prod, hslice]
  field_simp

end SGPT.Foundations.Analysis.Pending.LelongPoincareLevi
