import SGPT.Trace.TwistedL2MainStatement

/-!
# Reduction of the twisted correction to finite data energy

The infinite-energy case has the zero holomorphic section as a witness. This
reduction does not supply the finite-energy correction estimate.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

omit [BorelSpace X] in
/-- Once the correction is constructed whenever its data-energy integral is
finite, the infinite-energy case follows by taking the zero section. -/
theorem correction_of_finite_data
    (hfinite : ∀ T : TwistedDatum n X,
      (∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ) < ⊤ →
      ∃ S : (x : X) → T.L.Fiber x,
        SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) T.L.Fiber S T.U ∧
        (∫⁻ x in T.U, ENNReal.ofReal
          (‖T.G x - S x‖ ^ 2 * Real.exp (-T.φ x) / (T.a x + T.b x)) ∂T.μ) ≤
          ∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ)
    (T : TwistedDatum n X) :
    ∃ S : (x : X) → T.L.Fiber x,
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) T.L.Fiber S T.U ∧
      (∫⁻ x in T.U, ENNReal.ofReal
        (‖T.G x - S x‖ ^ 2 * Real.exp (-T.φ x) / (T.a x + T.b x)) ∂T.μ) ≤
        ∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ := by
  by_cases htop : (∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ) = ⊤
  · refine ⟨fun _ => 0, ?_, ?_⟩
    · exact ((Bundle.contMDiff_zeroSection ℂ T.L.Fiber (n := 1)
        (IB := 𝓘(ℂ, ComplexModel n))).mdifferentiable one_ne_zero).mdifferentiableOn
    · rw [htop]
      exact le_top
  · exact hfinite T (lt_top_iff_ne_top.mpr htop)

end SGPT.Trace.TwistedL2
