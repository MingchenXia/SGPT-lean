import SGPT.Foundations.Analysis.Pending.ActualMixedCapacityMassLiminf
import SGPT.Foundations.Analysis.Pending.ActualMixedCapacityContinuousTestLiminf
import SGPT.Foundations.Analysis.Pending.GlobalNonPluripolarKahler
import Mathlib.MeasureTheory.Measure.FiniteMeasure

set_option autoImplicit false

/-! # Actual singular mixed weak limits under the source mass condition

True continuous-test lower semicontinuity and the natural total-mass
limsup condition produce all signed continuous-test integral limits,
then actual native finite-measure weak convergence.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualMixedCapacityWeakConvergence

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar ThetaCapacity

noncomputable section

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M]

private theorem eventually_integral_gt
    {μ : ℕ → Measure M} {ν : Measure M}
    [∀ j, IsFiniteMeasure (μ j)] [IsFiniteMeasure ν]
    {g : M → ℝ} (hc : Continuous g) (hn : ∀ x, 0 ≤ g x)
    (hliminf : (∫⁻ x, ENNReal.ofReal (g x) ∂ν) ≤
      liminf (fun j => ∫⁻ x, ENNReal.ofReal (g x) ∂μ j) atTop)
    {a : ℝ} (ha : a < ∫ x, g x ∂ν) :
    ∀ᶠ j in atTop, a < ∫ x, g x ∂μ j := by
  have hint (τ : Measure M) [IsFiniteMeasure τ] : Integrable g τ :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have heq (τ : Measure M) [IsFiniteMeasure τ] :
      ENNReal.ofReal (∫ x, g x ∂τ) = ∫⁻ x, ENNReal.ofReal (g x) ∂τ :=
    ofReal_integral_eq_lintegral_ofReal (hint τ) (Eventually.of_forall hn)
  by_cases ha0 : a < 0
  · exact Eventually.of_forall (fun j => ha0.trans_le (integral_nonneg hn))
  · have ha0' : 0 ≤ a := not_lt.mp ha0
    have hp : 0 < ∫ x, g x ∂ν := ha0'.trans_lt ha
    have hENN : ENNReal.ofReal a < liminf (fun j => ∫⁻ x,
        ENNReal.ofReal (g x) ∂μ j) atTop :=
      ((ENNReal.ofReal_lt_ofReal_iff hp).mpr ha).trans_le ((heq ν).trans_le hliminf)
    filter_upwards [eventually_lt_of_lt_liminf hENN] with j hj
    rw [← heq (μ j)] at hj
    exact (ENNReal.ofReal_lt_ofReal_iff').mp hj |>.1

private theorem tendsto_integral_of_mass_and_lower_tests
    {μ : ℕ → Measure M} {ν : Measure M}
    [∀ j, IsFiniteMeasure (μ j)] [IsFiniteMeasure ν]
    (hmass : Tendsto (fun j => μ j univ) atTop (𝓝 (ν univ)))
    (hlower : ∀ g : M → ℝ, Continuous g → (∀ x, 0 ≤ g x) →
      (∫⁻ x, ENNReal.ofReal (g x) ∂ν) ≤
        liminf (fun j => ∫⁻ x, ENNReal.ofReal (g x) ∂μ j) atTop)
    {f : M → ℝ} (hf : Continuous f) :
    Tendsto (fun j => ∫ x, f x ∂μ j) atTop (𝓝 (∫ x, f x ∂ν)) := by
  obtain ⟨D, hD⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  let B : ℝ := max D 0
  have hfB (x : M) : |f x| ≤ B := by
    have hbound : |f x| ≤ D := by simpa only [Real.norm_eq_abs] using hD x (mem_univ x)
    exact hbound.trans (le_max_left _ _)
  have hp : Continuous (fun x => B + f x) := continuous_const.add hf
  have hp0 (x : M) : 0 ≤ B + f x := by linarith [(abs_le.mp (hfB x)).1]
  have hn : Continuous (fun x => B - f x) := continuous_const.sub hf
  have hn0 (x : M) : 0 ≤ B - f x := by linarith [(abs_le.mp (hfB x)).2]
  have hint (τ : Measure M) [IsFiniteMeasure τ] : Integrable f τ :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hconst (τ : Measure M) [IsFiniteMeasure τ] : Integrable (fun _ : M => B) τ :=
    integrable_const B
  have heqp (τ : Measure M) [IsFiniteMeasure τ] :
      (∫ x, B + f x ∂τ) = B * τ.real univ + ∫ x, f x ∂τ := by
    rw [integral_add (hconst τ) (hint τ), integral_const, smul_eq_mul, mul_comm]
  have heqn (τ : Measure M) [IsFiniteMeasure τ] :
      (∫ x, B - f x ∂τ) = B * τ.real univ - ∫ x, f x ∂τ := by
    rw [integral_sub (hconst τ) (hint τ), integral_const, smul_eq_mul, mul_comm]
  have hreal : Tendsto (fun j => (μ j).real univ) atTop (𝓝 (ν.real univ)) := by
    simpa only [measureReal_def, Function.comp_def] using
      (ENNReal.tendsto_toReal (measure_ne_top ν univ)).comp hmass
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have hplus := eventually_integral_gt hp hp0 (hlower _ hp hp0)
    (show (∫ x, B + f x ∂ν) - ε / 3 < ∫ x, B + f x ∂ν by linarith)
  have hminus := eventually_integral_gt hn hn0 (hlower _ hn hn0)
    (show (∫ x, B - f x ∂ν) - ε / 3 < ∫ x, B - f x ∂ν by linarith)
  have hnear := Metric.tendsto_nhds.mp (hreal.const_mul B) (ε / 3) hε3
  filter_upwards [hplus, hminus, hnear] with j hjp hjn hjmass
  rw [heqp ν, heqp (μ j)] at hjp
  rw [heqn ν, heqn (μ j)] at hjn
  rw [Real.dist_eq, abs_lt] at hjmass ⊢
  constructor <;> linarith [hjmass.1, hjmass.2]

variable {n : ℕ} [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The source's genuine total-mass limsup condition and actual capacity
limits internally produce every signed continuous-test integral limit. -/
theorem tendsto_integral (omega : KahlerBackground n M)
    {θ : Fin n → ClosedRealOneOneForm n M}
    {u : ℕ → Fin n → M → EReal} {v : Fin n → M → EReal}
    (hu : ∀ j i, IsThetaPshPotential (θ i).val (u j i))
    (hv : ∀ i, IsThetaPshPotential (θ i).val (v i))
    (hcap : ∀ i a, 0 < a → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | u j i x ≠ ⊥ ∧ v i x ≠ ⊥ ∧ a < |(u j i x).toReal - (v i x).toReal|})
      atTop (𝓝 0))
    (hupper : limsup (fun j => globalMixedMeasure θ (u j) (fun i => (hu j i).1) univ)
      atTop ≤ globalMixedMeasure θ v (fun i => (hv i).1) univ)
    {f : M → ℝ} (hf : Continuous f) :
    Tendsto (fun j => ∫ x, f x ∂globalMixedMeasure θ (u j) (fun i => (hu j i).1))
      atTop (𝓝 (∫ x, f x ∂globalMixedMeasure θ v (fun i => (hv i).1))) := by
  let μ (j : ℕ) : Measure M := globalMixedMeasure θ (u j) (fun i => (hu j i).1)
  let ν : Measure M := globalMixedMeasure θ v (fun i => (hv i).1)
  let : ∀ j, IsFiniteMeasure (μ j) := fun j => globalMixedMeasure_isFiniteMeasure omega _
  let : IsFiniteMeasure ν := globalMixedMeasure_isFiniteMeasure omega _
  have hmass : Tendsto (fun j => μ j univ) atTop (𝓝 (ν univ)) :=
    tendsto_of_le_liminf_of_limsup_le
      (ActualMixedCapacityMassLiminf.globalMixedMass_le_liminf omega hu hv hcap) hupper
  exact tendsto_integral_of_mass_and_lower_tests hmass
    (fun g hc hn => ActualMixedCapacityContinuousTestLiminf.lintegral_le_liminf
      omega hu hv hcap hc hn) hf

/-- Genuine internally finite global products converge in the actual
native topology of weak convergence of finite measures. -/
theorem tendsto_finiteMeasure (omega : KahlerBackground n M)
    {θ : Fin n → ClosedRealOneOneForm n M}
    {u : ℕ → Fin n → M → EReal} {v : Fin n → M → EReal}
    (hu : ∀ j i, IsThetaPshPotential (θ i).val (u j i))
    (hv : ∀ i, IsThetaPshPotential (θ i).val (v i))
    (hcap : ∀ i a, 0 < a → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | u j i x ≠ ⊥ ∧ v i x ≠ ⊥ ∧ a < |(u j i x).toReal - (v i x).toReal|})
      atTop (𝓝 0))
    (hupper : limsup (fun j => globalMixedMeasure θ (u j) (fun i => (hu j i).1) univ)
      atTop ≤ globalMixedMeasure θ v (fun i => (hv i).1) univ) :
    @Tendsto ℕ (FiniteMeasure M)
      (fun j => (⟨globalMixedMeasure θ (u j) (fun i => (hu j i).1),
        globalMixedMeasure_isFiniteMeasure omega _⟩ : FiniteMeasure M)) atTop
      (@nhds (FiniteMeasure M) FiniteMeasure.instTopologicalSpace
        (⟨globalMixedMeasure θ v (fun i => (hv i).1),
        globalMixedMeasure_isFiniteMeasure omega _⟩ : FiniteMeasure M)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  exact tendsto_integral omega hu hv hcap hupper f.continuous

end
end SGPT.Foundations.Analysis.Pending.ActualMixedCapacityWeakConvergence
