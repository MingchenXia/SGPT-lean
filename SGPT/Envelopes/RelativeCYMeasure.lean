import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Comparison of finite Borel measures by continuous test functions

Measure-theoretic input for the relative Calabi–Yau theorem (source `thm:Yau_rel`):
Xia, *Foundations of pluripotential theory*, `lem:global-measure-continuous-comparison`.

* `le_of_forall_lintegral_le`: on a pseudo-metrizable space, if
  `∫ g dσ ≤ ∫ g dλ` for every bounded continuous `g ≥ 0`, then `σ ≤ λ` (closed sets are
  approximated by thickened indicators, Borel sets from inside by closed sets);
* `le_of_tendsto_integral`: if finite measures `λ_j` converge weakly to `λ` (convergence of
  the integrals of all continuous functions on a compact space) and `σ ≤ λ_j` for every `j`,
  then `σ ≤ λ`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Envelopes.RelativeCY

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Comparison by test functions**: on a pseudo-metrizable space, a finite measure `σ`
whose integrals of bounded continuous functions `g ≥ 0` are dominated by those of a finite
measure `λ` satisfies `σ ≤ λ`. -/
theorem le_of_forall_lintegral_le [TopologicalSpace.PseudoMetrizableSpace X]
    {σ lam : Measure X} [IsFiniteMeasure σ] [IsFiniteMeasure lam]
    (h : ∀ g : X →ᵇ ℝ≥0, ∫⁻ x, (g x : ℝ≥0∞) ∂σ ≤ ∫⁻ x, (g x : ℝ≥0∞) ∂lam) : σ ≤ lam := by
  let := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  have hclosed : ∀ F : Set X, IsClosed F → σ F ≤ lam F := by
    intro F hF
    have hδ : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
    have hlim : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 := tendsto_lintegral_thickenedIndicator_of_isClosed σ hF hδ hlim
    have h2 := tendsto_lintegral_thickenedIndicator_of_isClosed lam hF hδ hlim
    exact le_of_tendsto_of_tendsto' h1 h2 fun k => h _
  rw [Measure.le_iff]
  intro E hE
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨K, hKE, hK, hlt⟩ :=
    hE.exists_isClosed_lt_add (μ := σ) (measure_ne_top σ E) (ENNReal.coe_ne_zero.mpr hε.ne')
  calc σ E ≤ σ K + ε := hlt.le
    _ ≤ lam K + ε := add_le_add_left (hclosed K hK) _
    _ ≤ lam E + ε := add_le_add_left (measure_mono hKE) _

/-- **Weak limits preserve a fixed lower bound.** On a compact pseudo-metrizable space, if
finite measures `λ_j` converge weakly to a finite measure `λ` and `σ ≤ λ_j` for every `j`,
then `σ ≤ λ`. -/
theorem le_of_tendsto_integral [TopologicalSpace.PseudoMetrizableSpace X] [CompactSpace X]
    {σ lam : Measure X} {lams : ℕ → Measure X} [IsFiniteMeasure σ] [IsFiniteMeasure lam]
    [∀ j, IsFiniteMeasure (lams j)]
    (hlim : ∀ g : C(X, ℝ), Tendsto (fun j => ∫ x, g x ∂lams j) atTop (𝓝 (∫ x, g x ∂lam)))
    (hle : ∀ j, σ ≤ lams j) : σ ≤ lam := by
  refine le_of_forall_lintegral_le fun g => ?_
  let gc : C(X, ℝ) := ⟨fun x => (g x : ℝ), NNReal.continuous_coe.comp g.continuous⟩
  have hgi : ∀ μ : Measure X, IsFiniteMeasure μ → Integrable (fun x => (g x : ℝ)) μ :=
    fun μ _ => (BoundedContinuousFunction.mkOfCompact gc).integrable μ
  have hint : ∀ μ : Measure X, IsFiniteMeasure μ → ∫⁻ x, (g x : ℝ≥0∞) ∂μ =
      ENNReal.ofReal (∫ x, (g x : ℝ) ∂μ) := fun μ hμ =>
    lintegral_coe_eq_integral _ (hgi μ hμ)
  rw [hint σ inferInstance, hint lam inferInstance]
  apply ENNReal.ofReal_le_ofReal
  refine ge_of_tendsto' (hlim gc) fun j => ?_
  exact integral_mono_measure (hle j) (Eventually.of_forall fun x => NNReal.coe_nonneg _)
    (hgi (lams j) inferInstance)

end SGPT.Envelopes.RelativeCY
