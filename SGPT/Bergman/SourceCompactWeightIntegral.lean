import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Bergman.WeightVariation

variable {K E : Type*} [TopologicalSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E]

omit [CompleteSpace E] in
/-- Genuine differentiation of the actual weighted integral. Compactness
produces the uniform local derivative bound internally. -/
theorem hasDerivAt_weighted_integral (μ : Measure K) [IsFiniteMeasure μ]
    (f : C(K, E)) (u : C(K, ℝ)) (a t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x, Real.exp (-a * t * u x) • f x ∂μ)
      (∫ x, (-a * u x * Real.exp (-a * t₀ * u x)) • f x ∂μ) t₀ := by
  let S : Set ℝ := Icc (t₀ - 1) (t₀ + 1)
  let : CompactSpace S := isCompact_iff_compactSpace.mp isCompact_Icc
  let D : C(S × K, E) :=
    ⟨fun p => (-a * u p.2 * Real.exp (-a * (p.1 : ℝ) * u p.2)) • f p.2,
      by fun_prop⟩
  let F : ℝ → K → E := fun t x => Real.exp (-a * t * u x) • f x
  let F' : ℝ → K → E := fun t x =>
    (-a * u x * Real.exp (-a * t * u x)) • f x
  have hFc (t : ℝ) : Continuous (F t) := by dsimp [F]; fun_prop
  have hDc (t : ℝ) : Continuous (F' t) := by dsimp [F']; fun_prop
  have hdiff (t : ℝ) (x : K) : HasDerivAt (fun r => F r x) (F' t x) t := by
    have h := ((((hasDerivAt_id t).const_mul (-a)).mul_const (u x)).exp).smul_const (f x)
    simpa only [F, F', id_eq, mul_one, mul_assoc, mul_left_comm, mul_comm] using h
  have hbound : ∀ x : K, ∀ t ∈ S, ‖F' t x‖ ≤ ‖D‖ := by
    intro x t ht
    exact ContinuousMap.norm_coe_le_norm D (⟨t, ht⟩, x)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Icc_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall (fun t => (hFc t).aestronglyMeasurable))
    ((hFc t₀).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hDc t₀).aestronglyMeasurable
    (Filter.Eventually.of_forall hbound) (integrable_const ‖D‖)
    (Filter.Eventually.of_forall (fun x t _ => hdiff t x))).2

end SGPT.Bergman.WeightVariation
