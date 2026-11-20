import SGPT.Trace.TwistedL2SingularGlue

/-!
# Fatou for functions on an increasing open exhaustion

A real weight is fixed and finite at every point. The sequence is only continuous
on its current open domain, and convergence and coverage are required almost
everywhere. This avoids treating multiplication by an infinite weight as continuous
at zero.
-/
set_option autoImplicit false
noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Fatou's lemma applied to the zero extensions from increasing open sets.
No integrability or measurability of the limiting function is needed. -/
theorem lintegral_le_of_ae_tendsto_on_exhaustion
    {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {U : ℕ → Set X} (hUo : ∀ j, IsOpen (U j)) (hUm : Monotone U)
    (hcover : ∀ᵐ x ∂μ, ∃ j, x ∈ U j)
    (u : ℕ → X → ℝ) (v w : X → ℝ)
    (hu : ∀ j, ContinuousOn (u j) (U j)) (hw : Measurable w)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun j => u j x) atTop (𝓝 (v x)))
    {I : ℝ≥0∞}
    (hbound : ∀ j, (∫⁻ x in U j, ENNReal.ofReal (u j x * w x) ∂μ) ≤ I) :
    (∫⁻ x, ENNReal.ofReal (v x * w x) ∂μ) ≤ I := by
  classical
  let f : ℕ → X → ℝ≥0∞ := fun j => (U j).indicator fun x =>
    ENNReal.ofReal (u j x * w x)
  have hm : ∀ j, AEMeasurable (f j) μ := by
    intro j
    have hg : Measurable ((U j).indicator (u j)) := by
      rw [← Set.piecewise_eq_indicator]
      exact (hu j).measurable_piecewise continuousOn_const (hUo j).measurableSet
    have hf : f j = fun x => ENNReal.ofReal (((U j).indicator (u j)) x * w x) := by
      funext x
      by_cases hx : x ∈ U j <;> simp [f, hx]
    rw [hf]
    exact ((hg.mul hw).ennreal_ofReal).aemeasurable
  have hp : ∀ᵐ x ∂μ, ENNReal.ofReal (v x * w x) ≤ liminf (fun j => f j x) atTop := by
    filter_upwards [hcover, hconv] with x hx hc
    obtain ⟨j₀, hj₀⟩ := hx
    have ht : Tendsto (fun j => f j x) atTop (𝓝 (ENNReal.ofReal (v x * w x))) := by
      apply (ENNReal.tendsto_ofReal (hc.mul_const (w x))).congr'
      filter_upwards [eventually_ge_atTop j₀] with j hj
      simp [f, hUm hj hj₀]
    exact ht.liminf_eq.ge
  calc
    (∫⁻ x, ENNReal.ofReal (v x * w x) ∂μ) ≤
        ∫⁻ x, liminf (fun j => f j x) atTop ∂μ := lintegral_mono_ae hp
    _ ≤ liminf (fun j => ∫⁻ x, f j x ∂μ) atTop := lintegral_liminf_le' hm
    _ ≤ I := by
      refine liminf_le_of_frequently_le' (Frequently.of_forall fun j => ?_)
      simpa only [f, lintegral_indicator (hUo j).measurableSet] using hbound j

end SGPT.Trace.TwistedL2
