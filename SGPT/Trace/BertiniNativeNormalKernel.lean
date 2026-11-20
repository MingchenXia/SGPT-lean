import SGPT.Trace.OptimalScaledNormalResidue
import SGPT.Foundations.Analysis.Pending.ProductMixedMeasure

/-! Exact native coordinate Lebesgue normalization for the actual scalar normal. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace SGPT.Trace.BertiniNativeNormalKernel

open Set Filter MeasureTheory
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Foundations.Analysis.Pending.ProductMixedMeasure
open SGPT.Trace.OptimalNormalResidueKernel SGPT.Trace.OptimalScaledNormalResidue

def modelOneScalarEquiv : ComplexModel 1 ≃ₗᵢ[ℂ] ℂ where
  toLinearEquiv := (PiLp.equivOfUnique 2 ℂ (fun _ : Fin 1 => ℂ)).toLinearEquiv
  norm_map' z := by
    change ‖z 0‖ = ‖z‖
    have h : ‖z‖ ^ 2 = ‖z 0‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [Fin.sum_univ_one]
    nlinarith [norm_nonneg z, norm_nonneg (z 0)]

theorem modelOneScalarEquiv_apply (z : ComplexModel 1) : modelOneScalarEquiv z = z 0 := rfl

theorem measurePreserving_modelOneScalarEquiv :
    MeasurePreserving modelOneScalarEquiv (volume : Measure (ComplexModel 1)) (volume : Measure ℂ) := by
  have h := (IsometryEquiv.toRealLinearIsometryEquivOfMapZero modelOneScalarEquiv.toIsometryEquiv
    (by rw [LinearIsometryEquiv.coe_toIsometryEquiv]; exact map_zero _)).measurePreserving
  rw [IsometryEquiv.coe_toRealLinearIsometryEquivOfMapZero] at h
  exact h

def normalProductEquiv (d : ℕ) : (ComplexModel d × ℂ) ≃L[ℂ] ComplexModel (d + 1) :=
  ((ContinuousLinearEquiv.refl ℂ (ComplexModel d)).prodCongr modelOneScalarEquiv.symm.toContinuousLinearEquiv).trans
    (prodModelEquiv d 1)

theorem normalProductEquiv_last (d : ℕ) (q : ComplexModel d × ℂ) :
    normalProductEquiv d q (Fin.last d) = q.2 := by
  change prodModelEquiv d 1 (q.1, modelOneScalarEquiv.symm q.2) (Fin.last d) = q.2
  have h := modelOneScalarEquiv.apply_symm_apply q.2
  change (modelOneScalarEquiv.symm q.2).ofLp 0 = q.2 at h
  simpa [prodModelEquiv] using h

theorem measurePreserving_normalProductEquiv (d : ℕ) :
    MeasurePreserving (normalProductEquiv d)
      ((volume : Measure (ComplexModel d)).prod (volume : Measure ℂ)) (volume : Measure (ComplexModel (d + 1))) := by
  have hi : MeasurePreserving modelOneScalarEquiv.symm (volume : Measure ℂ) (volume : Measure (ComplexModel 1)) :=
    MeasurePreserving.symm modelOneScalarEquiv.toHomeomorph.toMeasurableEquiv measurePreserving_modelOneScalarEquiv
  have hp := (MeasurePreserving.id (volume : Measure (ComplexModel d))).prod hi
  exact (measurePreserving_prodModelEquiv d 1).comp hp

theorem integrable_native_scaled_normal {d : ℕ} {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    {χ : ComplexModel (d + 1) → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    Integrable (fun z : ComplexModel (d + 1) => residueKernel ε (z (Fin.last d) / (ρ : ℂ)) * χ z) volume := by
  let E := normalProductEquiv d
  have hc : Continuous (χ ∘ E) := hχ.comp E.continuous
  have hcc : HasCompactSupport (χ ∘ E) := hχc.comp_homeomorph E.toHomeomorph
  have hi := integrable_original_scaled_product_normal hρ hε hc hcc
  apply ((measurePreserving_normalProductEquiv d).integrable_comp_emb E.toHomeomorph.measurableEmbedding).mp
  convert hi using 1
  funext q
  change residueKernel ε (E q (Fin.last d) / (ρ : ℂ)) * χ (E q) = _
  rw [normalProductEquiv_last]
  rfl

theorem tendsto_integral_native_scaled_normal {d : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    {χ : ComplexModel (d + 1) → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    Tendsto (fun ε : ℝ => ∫ z : ComplexModel (d + 1), residueKernel ε (z (Fin.last d) / (ρ : ℂ)) * χ z)
      (𝓝[>] 0) (𝓝 (Real.pi * ρ ^ 2 * ∫ u : ComplexModel d, χ (normalProductEquiv d (u, 0)))) := by
  let E := normalProductEquiv d
  have hc : Continuous (χ ∘ E) := hχ.comp E.continuous
  have hcc : HasCompactSupport (χ ∘ E) := hχc.comp_homeomorph E.toHomeomorph
  have h := tendsto_integral_original_scaled_product_normal hρ hc hcc
  apply h.congr'
  filter_upwards [] with ε
  have heq := (measurePreserving_normalProductEquiv d).integral_comp E.toHomeomorph.measurableEmbedding
    (fun z : ComplexModel (d + 1) => residueKernel ε (z (Fin.last d) / (ρ : ℂ)) * χ z)
  simpa only [normalProductEquiv_last, Function.comp_apply] using heq

end SGPT.Trace.BertiniNativeNormalKernel
