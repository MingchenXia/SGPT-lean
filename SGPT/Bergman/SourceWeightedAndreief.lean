import SGPT.Bergman.SourceAndreiefIntegral
import SGPT.Bergman.SourceAndreiefTilt
import Mathlib.Topology.ContinuousMap.Compact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.Andreief
open Set MeasureTheory
open scoped BigOperators ComplexConjugate

variable {ι K : Type*} [Fintype ι] [DecidableEq ι]
  [TopologicalSpace K] [CompactSpace K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K]

omit [Fintype ι] [DecidableEq ι] [CompactSpace K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K] in
/-- Pair continuity of the actual tilted evaluations follows from the
original pair products and the exact positive physical exponential. -/
theorem tilted_pair_continuous (f : ι → K → ℂ)
    (hpair : ∀ i j, Continuous (fun x => conj (f i x) * f j x))
    (u : C(K, ℝ)) (a t : ℝ) (i j : ι) :
    Continuous (fun x => conj (tiltedEvaluations f u a t i x) *
      tiltedEvaluations f u a t j x) := by
  have heq : (fun x => conj (tiltedEvaluations f u a t i x) *
      tiltedEvaluations f u a t j x) =
      (fun x => (Real.exp (a * t * u x) : ℂ) * (conj (f i x) * f j x)) :=
    funext (tilted_pair f u a t i j)
  rw [heq]
  exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
    (continuous_const.mul u.continuous))).mul (hpair i j)

/-- Genuine weighted Andreief identity with the original actual scalar
family, original measure, continuous weight and true Gram integral. -/
theorem integral_weighted_squaredEvaluationDet (μ : Measure K) [IsFiniteMeasure μ]
    (f : ι → K → ℂ)
    (hpair : ∀ i j, Continuous (fun x => conj (f i x) * f j x))
    (u : C(K, ℝ)) (a t : ℝ) :
    (∫ x : ι → K, Real.exp (a * t * ∑ j, u (x j)) * squaredEvaluationDet f x
      ∂Measure.pi (fun _ : ι => μ)) =
      ((Fintype.card ι).factorial : ℝ) *
        (integralGram μ (tiltedEvaluations f u a t)).det.re := by
  simpa only [squaredEvaluationDet_tilt] using!
    integral_squaredEvaluationDet μ (tiltedEvaluations f u a t)
      (tilted_pair_continuous f hpair u a t)

end SGPT.Bergman.Andreief
